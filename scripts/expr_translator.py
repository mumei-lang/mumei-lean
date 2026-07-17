"""Translate mumei contract expressions into Lean 4 ``Prop`` source.

This is the translator used by ``scripts/ingest_cert.py``
to turn a mumei atom's ``requires`` / ``ensures`` strings into Lean
theorem statements. It deliberately handles a small, well-documented
subset:

* arithmetic comparisons: ``>``, ``>=``, ``<``, ``<=``, ``==``, ``!=``
* logical connectives:    ``&&`` (∧), ``||`` (∨), ``!`` (¬, prefix only)
* arithmetic operators:   ``+``, ``-``, ``*``, ``/``, ``%``
* integer / boolean / string literals, identifiers (including ``result``)
* parentheses
* bounded ``forall(..)``, unbounded ``forall`` / ``exists`` quantifiers,
  ``if .. then .. else ..``, ``match`` expressions,
  ``arr[i]`` access, and known calls:
  ``len``, ``abs``, ``min``, ``max``, ``old``, ``starts_with``, ``ends_with``,
  ``contains``, ``not_contains``, ``sum``, ``count``, ``mod``, ``pow``, ``phi``,
  finite-field helpers, group-theory helpers, crypto helpers,
  smart-contract / RTGS obligation helpers, and higher-order predicate calls
  through ``holds(P, x)``

Anything outside this subset is preserved verbatim and emitted as a
Lean fragment that almost certainly will not type-check; the generated
theorem then carries a ``-- TODO: unproven`` marker which
``MumeiLean.unproven`` makes greppable.
"""
from __future__ import annotations

import re
from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional, Set, Tuple

# Tokens we recognise. Order matters: longer prefixes must come first
# so e.g. ``>=`` is not split into ``>`` + ``=``.
#
# The translator's call / array-access / comma handling lives in the
# translation phase rather than the lexer: the lexer keeps ``(``,
# ``)``, ``[``, ``]``, ``,`` as plain ``OP`` tokens and the
# ``_emit_tokens`` walker pattern-matches ``ID (`` / ``ID [`` /
# ``forall (`` to drive the rewrites added by the bridge translator.
_TOKEN_RE = re.compile(
    r"""
    \s+                          |  # whitespace
    (?P<STR>"(?:\\.|[^"\\])*") |  # string literal
    (?P<NUM>\d+)                 |  # integer literal
    (?P<BOOL>\btrue\b|\bfalse\b) |  # boolean literal
    (?P<KW>\bforall\b|\bexists\b|\bif\b|\bthen\b|\belse\b|\bmatch\b|\blet\b|\bin\b) |  # keywords
    (?P<ID>[A-Za-z_][A-Za-z0-9_]*) |  # identifier
    (?P<OP>
        ==>|==|!=|>=|<=|&&|\|\||=>|\.\.|
        [+\-*/%<>=!()\[\]{},:]
    )
    """,
    re.VERBOSE,
)

# Identifiers that should NOT be quantified — they are either Lean
# keywords/standard names or mumei built-ins handled inline.
_RESERVED_IDENTS: Set[str] = {
    "true", "false",
    "result",  # bound separately as the theorem's return-value parameter
    # Mumei built-ins handled inline by ``_emit_tokens``. Listing them
    # keeps ``_extract_identifiers`` from binding them as theorem
    # parameters if they show up as bare ID tokens.
    "forall", "exists", "len", "abs", "min", "max", "old",
    "starts_with", "ends_with", "contains", "not_contains", "sum", "count",
    "mod", "pow", "phi",
    "hash", "signature_verify", "encrypt", "decrypt",
    "holds",
    "unknown", "unknown_obligation",
    "ff_add", "ff_sub", "ff_mul", "ff_neg", "ff_pow", "ff_inv", "ff_div",
    "ff_in_field", "is_prime", "mod_eq", "group_mul", "group_inv",
    "group_pow", "group_identity",
    "if", "then", "else", "match", "let", "in", "_",
    "implies",
    "kdf", "hmac", "commitment_hash", "zk_verify",
    "ff_zero", "ff_one", "ff_eq", "group_order", "group_comm",
    "sc_reentrancy_guard", "sc_balance_preserved", "sc_withdraw_allowed",
    "sc_no_negative_balance", "rtgs_validated", "rtgs_settled",
    "rtgs_balance_conserved", "rtgs_trace_safe",
    "i64", "u64", "f64", "bool", "string", "str", "int", "nat", "field",
    "predicate",
    # Lean keywords we never want to over-bind even if the contract uses
    # them as identifier names (it should not, but defensively).
    "Type", "Prop", "fun", "let", "do", "match", "with", "by", "in",
}

# Operator translation: token text → Lean token text.
_OP_TRANSLATION = {
    "&&": "∧",
    "||": "∨",
    "==": "=",
    "!=": "≠",
    "!":  "¬",
    "==>": "→",
    # passthrough for the rest
    ">=": "≥",
    "<=": "≤",
}

_KNOWN_FUNCTIONS = {
    "len": "mumei_len",
    "abs": "mumei_abs",
    "min": "min",
    "max": "max",
    "old": "old_",
    "starts_with": "mumei_starts_with",
    "ends_with": "mumei_ends_with",
    "contains": "mumei_contains",
    "not_contains": "mumei_not_contains",
    "sum": "mumei_sum",
    "count": "mumei_count",
    "mod": "MumeiLean.CryptoHelpers.mumei_mod",
    "pow": "MumeiLean.CryptoHelpers.mumei_pow",
    "phi": "MumeiLean.CryptoHelpers.mumei_phi",
    "hash": "MumeiLean.Crypto.hash",
    "signature_verify": "MumeiLean.Crypto.signature_verify",
    "encrypt": "MumeiLean.Crypto.encrypt",
    "decrypt": "MumeiLean.Crypto.decrypt",
    "holds": "holds",
    "unknown": "MumeiLean.AdvancedPatterns.mumei_unknown_obligation",
    "unknown_obligation": "MumeiLean.AdvancedPatterns.mumei_unknown_obligation",
    "ff_add": "MumeiLean.Algebra.mumei_ff_add",
    "ff_sub": "MumeiLean.Algebra.mumei_ff_sub",
    "ff_mul": "MumeiLean.Algebra.mumei_ff_mul",
    "ff_neg": "MumeiLean.Algebra.mumei_ff_neg",
    "ff_pow": "MumeiLean.Algebra.mumei_ff_pow",
    "ff_inv": "MumeiLean.Algebra.mumei_ff_inv",
    "ff_div": "MumeiLean.Algebra.mumei_ff_div",
    "ff_in_field": "MumeiLean.Algebra.mumei_ff_in_field",
    "is_prime": "MumeiLean.Algebra.mumei_is_prime",
    "mod_eq": "MumeiLean.Algebra.mumei_mod_eq",
    "group_mul": "MumeiLean.Algebra.mumei_group_mul",
    "group_inv": "MumeiLean.Algebra.mumei_group_inv",
    "group_pow": "MumeiLean.Algebra.mumei_group_pow",
    "group_identity": "MumeiLean.Algebra.mumei_group_identity",
    "kdf": "MumeiLean.Crypto.kdf",
    "hmac": "MumeiLean.Crypto.hmac",
    "commitment_hash": "MumeiLean.Crypto.commitment_hash",
    "zk_verify": "MumeiLean.Crypto.zk_verify",
    "ff_zero": "MumeiLean.Algebra.mumei_ff_zero",
    "ff_one": "MumeiLean.Algebra.mumei_ff_one",
    "ff_eq": "MumeiLean.Algebra.mumei_ff_eq",
    "group_order": "MumeiLean.Algebra.mumei_group_order",
    "group_comm": "MumeiLean.Algebra.mumei_group_comm",
    "sc_reentrancy_guard": "MumeiLean.AdvancedPatterns.sc_reentrancy_guard",
    "sc_balance_preserved": "MumeiLean.AdvancedPatterns.sc_balance_preserved",
    "sc_withdraw_allowed": "MumeiLean.AdvancedPatterns.sc_withdraw_allowed",
    "sc_no_negative_balance": "MumeiLean.AdvancedPatterns.sc_no_negative_balance",
    "rtgs_validated": "MumeiLean.AdvancedPatterns.rtgs_validated",
    "rtgs_settled": "MumeiLean.AdvancedPatterns.rtgs_settled",
    "rtgs_balance_conserved": "MumeiLean.AdvancedPatterns.rtgs_balance_conserved",
    "rtgs_trace_safe": "MumeiLean.AdvancedPatterns.rtgs_trace_safe",
    "implies": "implies",
}

_KNOWN_FUNCTION_ARITY = {
    "len": 1,
    "abs": 1,
    "min": 2,
    "max": 2,
    "old": 1,
    "starts_with": 2,
    "ends_with": 2,
    "contains": 2,
    "not_contains": 2,
    "sum": 2,
    "count": 2,
    "mod": 2,
    "pow": 2,
    "phi": 1,
    "hash": 2,
    "signature_verify": 4,
    "encrypt": 3,
    "decrypt": 3,
    "holds": 2,
    "unknown": 1,
    "unknown_obligation": 1,
    "ff_add": 3,
    "ff_sub": 3,
    "ff_mul": 3,
    "ff_neg": 2,
    "ff_pow": 3,
    "ff_inv": 2,
    "ff_div": 3,
    "ff_in_field": 2,
    "is_prime": 1,
    "mod_eq": 3,
    "group_mul": 2,
    "group_inv": 1,
    "group_pow": 2,
    "group_identity": 0,
    "kdf": 3,
    "hmac": 2,
    "commitment_hash": 2,
    "zk_verify": 3,
    "ff_zero": 1,
    "ff_one": 1,
    "ff_eq": 3,
    "group_order": 1,
    "group_comm": 2,
    "sc_reentrancy_guard": 2,
    "sc_balance_preserved": 2,
    "sc_withdraw_allowed": 2,
    "sc_no_negative_balance": 1,
    "rtgs_validated": 1,
    "rtgs_settled": 1,
    "rtgs_balance_conserved": 4,
    "rtgs_trace_safe": 2,
    "implies": 2,
}

_QUANTIFIER_KEYWORDS = {"forall", "exists"}
_STRING_FUNCTIONS = {"starts_with", "ends_with", "contains", "not_contains"}
_ARRAY_FIRST_ARG_FUNCTIONS = {"sum", "count"}
_FINITE_FIELD_FUNCTIONS = {
    "ff_add", "ff_sub", "ff_mul", "ff_neg", "ff_pow", "ff_inv", "ff_div",
    "ff_in_field", "is_prime", "mod_eq", "ff_zero", "ff_one", "ff_eq",
}
_GROUP_FUNCTIONS = {"group_mul", "group_inv", "group_pow", "group_identity", "group_order", "group_comm"}
_CRYPTO_FUNCTIONS = {"hash", "signature_verify", "encrypt", "decrypt", "kdf", "hmac", "commitment_hash", "zk_verify"}
_SMART_CONTRACT_FUNCTIONS = {
    "sc_reentrancy_guard", "sc_balance_preserved",
    "sc_withdraw_allowed", "sc_no_negative_balance",
}
_RTGS_FUNCTIONS = {
    "rtgs_validated", "rtgs_settled",
    "rtgs_balance_conserved", "rtgs_trace_safe",
}
_HIGHER_ORDER_PREDICATE_FUNCTIONS = {"holds"}
_UNKNOWN_OBLIGATION_FUNCTIONS = {"unknown", "unknown_obligation"}
_SCALAR_CALL_FUNCTIONS = (
    set(_KNOWN_FUNCTIONS)
    - _STRING_FUNCTIONS
    - _ARRAY_FIRST_ARG_FUNCTIONS
    - _HIGHER_ORDER_PREDICATE_FUNCTIONS
    - {"old"}
)

TRANSLATOR_VERSION = "mumei-lean-translator-ir-v2"
BRIDGE_LEMMA_HASH = "a3e9c1f4b7d2806e5f19347cab82d0963ef1a5bc70d4e8290f136d5ab7c84e11"

# Obligation class taxonomy for escalated atoms.
# Each class maps to a set of Lean bridge lemma entry points.
OBLIGATION_CLASS_QUANTIFIER = "quantifier_obligation"
OBLIGATION_CLASS_FINITE_FIELD = "finite_field_obligation"
OBLIGATION_CLASS_GROUP_THEORY = "group_theory_obligation"
OBLIGATION_CLASS_CRYPTO = "crypto_primitive_obligation"
OBLIGATION_CLASS_ARITHMETIC = "arithmetic_obligation"
OBLIGATION_CLASS_SMART_CONTRACT = "smart_contract_obligation"
OBLIGATION_CLASS_SMART_CONTRACT_GUARD_TRACE = "smart_contract_guard_trace_obligation"
OBLIGATION_CLASS_RTGS = "rtgs_obligation"
OBLIGATION_CLASS_UNKNOWN = "unknown_obligation"

SMART_CONTRACT_GUARD_TRACE_LOWERING = "smart_contract_guard_trace_lowering"

_OBLIGATION_CLASS_BRIDGE_LEMMAS: Dict[str, List[str]] = {
    OBLIGATION_CLASS_QUANTIFIER: [
        "MumeiLean.Quantifiers.skolemize_exists",
        "MumeiLean.Quantifiers.herbrand_forall",
        "MumeiLean.Quantifiers.bounded_forall_of_unrestricted",
        "MumeiLean.Quantifiers.bounded_exists_of_witness",
        "MumeiLean.Quantifiers.forall_and_intro",
        "MumeiLean.Quantifiers.nested_forall_intro",
        "MumeiLean.Quantifiers.nested_exists_intro",
        "MumeiLean.Quantifiers.forall_exists_swap_of_finite",
        "MumeiLean.AdvancedPatterns.bounded_forall_weaken",
        "MumeiLean.AdvancedPatterns.bounded_exists_map",
        "MumeiLean.AdvancedPatterns.nested_forall_swap",
        "MumeiLean.AdvancedPatterns.int_nonnegative_induction_pattern",
    ],
    OBLIGATION_CLASS_FINITE_FIELD: [
        "MumeiLean.Algebra.ff_add_in_field",
        "MumeiLean.Algebra.ff_mul_in_field",
        "MumeiLean.Algebra.ff_sub_in_field",
        "MumeiLean.Algebra.ff_neg_in_field",
        "MumeiLean.Algebra.ff_zero_in_field",
        "MumeiLean.Algebra.ff_one_in_field",
        "MumeiLean.Algebra.ff_eq_refl",
        "MumeiLean.Algebra.ff_eq_symm",
        "MumeiLean.Algebra.ff_eq_trans",
        "MumeiLean.Algebra.ff_add_comm",
        "MumeiLean.Algebra.ff_mul_comm",
        "MumeiLean.Algebra.ff_add_zero",
        "MumeiLean.Algebra.ff_mul_one",
        "MumeiLean.AdvancedPatterns.finite_field_binary_closed",
    ],
    OBLIGATION_CLASS_GROUP_THEORY: [
        "MumeiLean.Algebra.group_mul_assoc",
        "MumeiLean.Algebra.group_left_inv",
        "MumeiLean.Algebra.group_right_inv",
        "MumeiLean.Algebra.group_mul_one",
        "MumeiLean.Algebra.group_one_mul",
        "MumeiLean.Algebra.group_inv_inv",
        "MumeiLean.Algebra.group_mul_inv_rev",
        "MumeiLean.Algebra.mumei_group_comm_int",
        "MumeiLean.AdvancedPatterns.group_hom_preserves_mul",
    ],
    OBLIGATION_CLASS_CRYPTO: [
        "MumeiLean.Crypto.hash_deterministic",
        "MumeiLean.Crypto.hash_modulus_bounds",
        "MumeiLean.Crypto.encryption_roundtrip",
        "MumeiLean.Crypto.rsa_signature_correct",
        "MumeiLean.Crypto.signature_verify_sound",
        "MumeiLean.Crypto.kdf_deterministic",
        "MumeiLean.Crypto.hmac_deterministic",
        "MumeiLean.Crypto.commitment_binding_pattern",
        "MumeiLean.Crypto.zk_verify_soundness",
        "MumeiLean.AdvancedPatterns.hash_stability_under_equal_inputs",
        "MumeiLean.AdvancedPatterns.signature_pattern",
        "MumeiLean.AdvancedPatterns.encryption_pattern",
    ],
    OBLIGATION_CLASS_ARITHMETIC: [
        "MumeiLean.Algebra.sc_subtraction_nonnegative",
    ],
    OBLIGATION_CLASS_SMART_CONTRACT: [
        "MumeiLean.AdvancedPatterns.sc_withdraw_allowed_intro",
        "MumeiLean.AdvancedPatterns.sc_no_negative_after_withdraw",
    ],
    OBLIGATION_CLASS_SMART_CONTRACT_GUARD_TRACE: [
        "MumeiLean.SmartContract.no_external_call_without_lock",
    ],
    OBLIGATION_CLASS_RTGS: [
        "MumeiLean.AdvancedPatterns.rtgs_balance_conserved_refl",
        "MumeiLean.AdvancedPatterns.rtgs_trace_safe_intro",
        "MumeiLean.Algebra.rtgs_transfer_conserves_sum",
    ],
    OBLIGATION_CLASS_UNKNOWN: [
        "MumeiLean.AdvancedPatterns.unknown_obligation_intro",
    ],
}


@dataclass
class TranslatorIRBinder:
    mumei_name: str
    lean_name: str
    mumei_type: str
    lean_type: str
    role: str = "free"
    refinement: Optional[str] = None

    def to_dict(self) -> Dict[str, object]:
        payload: Dict[str, object] = {
            "mumei_name": self.mumei_name,
            "lean_name": self.lean_name,
            "mumei_type": self.mumei_type,
            "lean_type": self.lean_type,
            "role": self.role,
        }
        if self.refinement:
            payload["refinement"] = self.refinement
        return payload


@dataclass
class TranslatorIRProvenanceSpan:
    file: str = ""
    line: int = 0
    col: int = 0
    len: int = 0

    def to_dict(self) -> Dict[str, object]:
        return {
            "file": self.file,
            "line": self.line,
            "col": self.col,
            "len": self.len,
        }


@dataclass
class TranslatorIR:
    sort: str
    binders: List[TranslatorIRBinder]
    theorem_goal: str
    provenance_span: TranslatorIRProvenanceSpan = field(default_factory=TranslatorIRProvenanceSpan)
    lowering_rules: List[str] = field(default_factory=list)
    manual_lemma_reason: Optional[str] = None
    semantic_gap_notes: List[str] = field(default_factory=list)
    proof_trace_hints: List[str] = field(default_factory=list)
    requires_bridge_lemmas: List[str] = field(default_factory=list)
    obligation_class: Optional[str] = None
    guard_trace_ops: List[str] = field(default_factory=list)
    guard_trace_expected_outcome: Optional[str] = None

    def to_dict(self) -> Dict[str, object]:
        payload: Dict[str, object] = {
            "sort": self.sort,
            "binders": [binder.to_dict() for binder in self.binders],
            "theorem_goal": self.theorem_goal,
            "provenance_span": self.provenance_span.to_dict(),
            "lowering_rules": list(self.lowering_rules),
        }
        if self.manual_lemma_reason:
            payload["manual_lemma_reason"] = self.manual_lemma_reason
        if self.semantic_gap_notes:
            payload["semantic_gap_notes"] = list(self.semantic_gap_notes)
        if self.proof_trace_hints:
            payload["proof_trace_hints"] = list(self.proof_trace_hints)
        if self.requires_bridge_lemmas:
            payload["requires_bridge_lemmas"] = list(self.requires_bridge_lemmas)
        if self.obligation_class:
            payload["obligation_class"] = self.obligation_class
        if self.guard_trace_ops:
            payload["guard_trace_ops"] = list(self.guard_trace_ops)
        if self.guard_trace_expected_outcome is not None:
            payload["guard_trace_expected_outcome"] = self.guard_trace_expected_outcome
        return payload


@dataclass
class TranslationResult:
    """Outcome of translating a single contract string."""

    lean_expr: str
    """Lean source fragment representing the contract as a ``Prop``."""

    identifiers: List[str]
    """Free identifiers referenced by the contract (excluding reserved)."""

    is_trivial: bool
    """``True`` if the source contract was empty / ``true`` /
    semantically a no-op. Trivial contracts produce ``True`` in Lean."""

    is_partial: bool
    """``True`` if the translator encountered tokens it could not fully
    handle (e.g. function calls, indexing). The caller should mark the
    generated theorem as ``-- TODO: unproven``."""

    array_identifiers: List[str]
    """Subset of ``identifiers`` that appear in ``arr[i]`` array-access
    position. These must be typed as ``Int → Int`` (not ``Int``) when
    emitted as theorem parameters, because the translator lowers
    ``arr[i]`` to Lean function application ``(arr (i))``."""

    string_identifiers: List[str]
    """Subset of ``identifiers`` that are passed to string predicates
    such as ``starts_with`` / ``ends_with``. The renderer types these
    identifiers as ``String`` instead of the scalar ``Int`` default."""

    predicate_identifiers: List[str] = field(default_factory=list)
    """Subset of ``identifiers`` used as higher-order predicates through
    ``holds(P, x)``. The renderer types these as ``Int → Prop``."""

    predicate_arities: Dict[str, int] = field(default_factory=dict)
    """Arity for each higher-order predicate identifier."""

    translator_ir: Optional[TranslatorIR] = None
    """Typed TranslatorIR metadata used by the escalation handshake."""

    unsupported_reasons: List[str] = field(default_factory=list)
    """Structural reasons for partial translation, if any."""

    manual_lemma_reason: Optional[str] = None
    """Non-empty when the expression must be finished by a manual lemma."""


_FORMAL_SPEC_LOWERING_RULES: Set[str] = {
    "type_system_mapping",
    "contract_lowering",
    "array_bounds_bridge",
    "string_regex_bridge",
    "refinement_predicate_lowering",
    "integer_overflow_bridge",
    "finite_field_lowering",
    "group_theory_lowering",
    "crypto_primitive_lowering",
    "higher_order_predicate_lowering",
    "inductive_definition_lowering",
    "mathlib4_bridge",
    "finset_bounded_quantifier_lowering",
    "quantifier_skolemize_lowering",
    "implication_lowering",
    "let_binding_lowering",
    "unknown_obligation_lowering",
    "smart_contract_lowering",
    "smart_contract_guard_trace_lowering",
    "rtgs_settlement_lowering",
    "sort_ascending_bridge",
}

_FORMAL_SPEC_TYPE_MAPPINGS: Dict[str, str] = {
    "i64": "Int",
    "u64": "Nat",
    "f64": "Float",
    "bool": "Bool",
    "string": "String",
    "str": "String",
    "int": "Int",
    "nat": "Nat",
    "field": "Int",
    "predicate<i64>": "Int → Prop",
    "predicate<i64,i64>": "Int → Int → Prop",
    "predicate<i64,i64,i64>": "Int → Int → Int → Prop",
    "predicate<nat>": "Nat → Prop",
}

_QUANTIFIER_TYPE_ALIASES: Dict[str, Tuple[str, str]] = {
    "i64": ("i64", "Int"),
    "int": ("i64", "Int"),
    "u64": ("u64", "Nat"),
    "nat": ("u64", "Nat"),
    "bool": ("bool", "Bool"),
    "string": ("string", "String"),
    "str": ("string", "String"),
    "field": ("field", "Int"),
    "t": ("i64", "Int"),
}


def _predicate_lean_type(arity: int) -> str:
    safe_arity = max(1, arity)
    return " → ".join(["Int"] * safe_arity + ["Prop"])


def _predicate_mumei_type(arity: int) -> str:
    safe_arity = max(1, arity)
    if safe_arity == 1:
        return "predicate<i64>"
    return "predicate<" + ",".join(["i64"] * safe_arity) + ">"


def _lean_type_from_mumei_type(mumei_type: str) -> Optional[str]:
    if mumei_type.startswith("array<") and mumei_type.endswith(">"):
        inner_mumei_type = mumei_type[len("array<"):-1]
        inner_lean_type = _lean_type_from_mumei_type(inner_mumei_type)
        if inner_lean_type is None:
            return None
        return f"List {inner_lean_type}"
    return _FORMAL_SPEC_TYPE_MAPPINGS.get(mumei_type)


def validate_translator_ir_compliance(translator_ir: TranslatorIR) -> List[str]:
    """Warn if TranslatorIR metadata drifts from the formal Lean spec.

    The check is intentionally non-fatal: generated Lean obligations are
    still valuable triage artefacts even when a new lowering rule or binder
    type has not yet been documented.
    """
    issues: List[str] = []
    for rule in translator_ir.lowering_rules:
        if rule not in _FORMAL_SPEC_LOWERING_RULES:
            issues.append(
                f"lowering rule is not in docs/LEAN_TRANSLATOR_SPEC.md: {rule}"
            )

    for binder in translator_ir.binders:
        expected_lean_type = _lean_type_from_mumei_type(binder.mumei_type)
        if expected_lean_type is None:
            issues.append(
                "binder type mapping is not in docs/LEAN_TRANSLATOR_SPEC.md: "
                f"{binder.mumei_type} -> {binder.lean_type} ({binder.mumei_name})"
            )
        elif binder.lean_type != expected_lean_type:
            issues.append(
                "binder type mapping disagrees with docs/LEAN_TRANSLATOR_SPEC.md: "
                f"{binder.mumei_type} -> {binder.lean_type}, expected "
                f"{expected_lean_type} ({binder.mumei_name})"
            )

    return issues


def _lean_binder_name(name: str) -> str:
    clean = "".join(ch if ch.isalnum() or ch == "_" else "_" for ch in name)
    if not clean:
        return "binder"
    if clean[0].isdigit():
        clean = "_" + clean
    if clean in _RESERVED_IDENTS or clean in {"theorem", "def", "namespace", "end"}:
        return f"{clean}_binder"
    return clean


def _binder_for_identifier(
    name: str,
    array_ids: List[str],
    string_ids: List[str],
    predicate_ids: Optional[List[str]] = None,
    predicate_arities: Optional[Dict[str, int]] = None,
) -> TranslatorIRBinder:
    if predicate_ids and name in predicate_ids:
        arity = (predicate_arities or {}).get(name, 1)
        return TranslatorIRBinder(
            name,
            _lean_binder_name(name),
            _predicate_mumei_type(arity),
            _predicate_lean_type(arity),
        )
    if name in array_ids:
        return TranslatorIRBinder(name, _lean_binder_name(name), "array<i64>", "List Int")
    if name in string_ids:
        return TranslatorIRBinder(name, _lean_binder_name(name), "string", "String")
    return TranslatorIRBinder(name, _lean_binder_name(name), "i64", "Int")


def _unsupported_reasons(source: str, tokens: List[tuple], is_partial: bool) -> List[str]:
    reasons: List[str] = []
    if any(kind == "UNK" for kind, _text in tokens):
        reasons.append("unknown_token")
    if "regex" in source:
        reasons.append("regex_semantics_require_manual_lemma")
    if any(kind == "KW" and text == "match" for kind, text in tokens):
        reasons.append("match_or_inductive_translation_requires_manual_lemma")
    if any(kind == "ID" and text in _UNKNOWN_OBLIGATION_FUNCTIONS for kind, text in tokens):
        reasons.append("unknown_obligation_requires_manual_lemma")
    for idx, (kind, text) in enumerate(tokens):
        if kind == "ID" and idx + 1 < len(tokens) and tokens[idx + 1] == ("OP", "("):
            if text not in _KNOWN_FUNCTIONS and not _is_predicate_call_name(text):
                reasons.append(f"unsupported_call:{text}")
    if is_partial and not reasons:
        reasons.append("unsupported_syntax")
    return sorted(set(reasons))


def _lowering_rules(tokens: List[tuple], array_ids: List[str], string_ids: List[str]) -> List[str]:
    rules = ["type_system_mapping", "contract_lowering"]
    if array_ids:
        rules.append("array_bounds_bridge")
    if string_ids or any("regex" in str(text) for _kind, text in tokens):
        rules.append("string_regex_bridge")
    if any(kind == "KW" and text in _QUANTIFIER_KEYWORDS for kind, text in tokens):
        rules.append("refinement_predicate_lowering")
    if any(kind == "OP" and text in {"*", "/", "%"} for kind, text in tokens):
        rules.append("integer_overflow_bridge")
    if any(kind == "ID" and text in _FINITE_FIELD_FUNCTIONS for kind, text in tokens):
        rules.extend(["finite_field_lowering", "mathlib4_bridge"])
    if any(kind == "ID" and text in _GROUP_FUNCTIONS for kind, text in tokens):
        rules.extend(["group_theory_lowering", "mathlib4_bridge"])
    if any(kind == "ID" and text in _CRYPTO_FUNCTIONS for kind, text in tokens):
        rules.extend(["crypto_primitive_lowering", "mathlib4_bridge"])
    if any(kind == "ID" and text in _SMART_CONTRACT_FUNCTIONS for kind, text in tokens):
        rules.extend(["smart_contract_lowering", "mathlib4_bridge"])
    if any(kind == "ID" and text in _RTGS_FUNCTIONS for kind, text in tokens):
        rules.extend(["rtgs_settlement_lowering", "mathlib4_bridge"])
    if any(kind == "ID" and text in _UNKNOWN_OBLIGATION_FUNCTIONS for kind, text in tokens):
        rules.extend(["unknown_obligation_lowering", "mathlib4_bridge"])
    if any(kind == "ID" and text in _HIGHER_ORDER_PREDICATE_FUNCTIONS for kind, text in tokens) or any(
        kind == "ID" and _is_predicate_call_name(text) for kind, text in tokens
    ):
        rules.extend(["higher_order_predicate_lowering", "mathlib4_bridge"])
    if any(kind == "KW" and text == "match" for kind, text in tokens):
        rules.append("inductive_definition_lowering")
    if any(kind == "OP" and text == "==>" for kind, text in tokens) or any(
        kind == "ID" and text == "implies" for kind, text in tokens
    ):
        rules.append("implication_lowering")
    if any(kind == "KW" and text == "let" for kind, text in tokens):
        rules.append("let_binding_lowering")
    if any(
        kind == "KW" and text in _QUANTIFIER_KEYWORDS for kind, text in tokens
    ) and any(
        kind == "ID" and text in _CRYPTO_FUNCTIONS for kind, text in tokens
    ):
        rules.append("quantifier_skolemize_lowering")
    deduped: List[str] = []
    for rule in rules:
        if rule not in deduped:
            deduped.append(rule)
    return deduped


def _build_semantic_gap_notes(
    tokens: List[tuple],
    array_ids: List[str],
    string_ids: List[str],
) -> List[str]:
    notes: List[str] = []
    if any(kind == "OP" and text in {"*", "/", "%"} for kind, text in tokens):
        notes.append(
            "integer_overflow_bridge: Mumei uses 2's complement wrap semantics, "
            "Lean 4 Int is unbounded. Bridge lemma required for overflow behavior."
        )
    if array_ids:
        notes.append(
            "array_bounds_bridge: Mumei requires explicit bounds checking, "
            "Lean 4 List.get! requires Nat index. Bridge lemma required."
        )
    if string_ids or any("regex" in str(text) for _kind, text in tokens):
        notes.append(
            "string_regex_bridge: String operations and regex semantics differ "
            "between Z3 and Lean 4. Manual lemma may be required."
        )
    if any(kind == "KW" and text in _QUANTIFIER_KEYWORDS for kind, text in tokens):
        notes.append(
            "refinement_predicate_lowering: Quantifiers are lowered to Lean "
            "dependent types. Bridge lemma may be required for complex predicates."
        )
    if any(kind == "ID" and text in _FINITE_FIELD_FUNCTIONS for kind, text in tokens):
        notes.append(
            "finite_field_lowering: GF(p)-style helpers are lowered through "
            "mathlib4 modular arithmetic and ZMod bridge lemmas."
        )
    if any(kind == "ID" and text in _GROUP_FUNCTIONS for kind, text in tokens):
        notes.append(
            "group_theory_lowering: group expressions are lowered to reusable "
            "mathlib4 group law lemmas."
        )
    if any(kind == "ID" and text in _CRYPTO_FUNCTIONS for kind, text in tokens):
        notes.append(
            "crypto_primitive_lowering: hash/signature/encryption primitives "
            "are routed through MumeiLean.Crypto proof patterns."
        )
    if any(kind == "ID" and text in _SMART_CONTRACT_FUNCTIONS for kind, text in tokens):
        notes.append(
            "smart_contract_lowering: SC obligations are routed through "
            "MumeiLean.AdvancedPatterns smart-contract receptacles."
        )
    if any(kind == "ID" and text in _RTGS_FUNCTIONS for kind, text in tokens):
        notes.append(
            "rtgs_settlement_lowering: RTGS obligations are routed through "
            "MumeiLean.AdvancedPatterns settlement receptacles."
        )
    if any(kind == "ID" and text in _UNKNOWN_OBLIGATION_FUNCTIONS for kind, text in tokens):
        notes.append(
            "unknown_obligation_lowering: explicit unknown obligations compile "
            "through MumeiLean.AdvancedPatterns but require a manual Lean lemma."
        )
    if any(kind == "ID" and text in _HIGHER_ORDER_PREDICATE_FUNCTIONS for kind, text in tokens):
        notes.append(
            "higher_order_predicate_lowering: predicate parameters are typed "
            "as Lean functions and applied directly."
        )
    if any(kind == "OP" and text == "==>" for kind, text in tokens) or any(
        kind == "ID" and text == "implies" for kind, text in tokens
    ):
        notes.append(
            "implication_lowering: Mumei ==> / implies(a,b) maps to Lean → "
            "via MumeiLean.Quantifiers.mumei_implies_intro."
        )
    if any(kind == "KW" and text == "let" for kind, text in tokens):
        notes.append(
            "let_binding_lowering: let x = e in body maps to Lean let "
            "binding. Scoping rules match Lean 4 semantics."
        )
    return notes


def _bridge_lemmas_for_rules(lowering_rules: List[str]) -> List[str]:
    bridge_lemmas: List[str] = []
    if "integer_overflow_bridge" in lowering_rules:
        bridge_lemmas.append("mumei_i64_overflow_bridge")
    if "array_bounds_bridge" in lowering_rules:
        bridge_lemmas.append("mumei_array_bounds_bridge")
        bridge_lemmas.append("mumei_array_get_bridge")
    if "string_regex_bridge" in lowering_rules:
        bridge_lemmas.append("mumei_regex_bridge")
    if "refinement_predicate_lowering" in lowering_rules:
        bridge_lemmas.append("mumei_subtype_predicate_bridge")
    if "finite_field_lowering" in lowering_rules:
        bridge_lemmas.append("mumei_finite_field_bridge")
    if "group_theory_lowering" in lowering_rules:
        bridge_lemmas.append("mumei_group_theory_bridge")
    if "crypto_primitive_lowering" in lowering_rules:
        bridge_lemmas.append("mumei_crypto_primitive_bridge")
    if "smart_contract_lowering" in lowering_rules:
        bridge_lemmas.append("mumei_smart_contract_bridge")
    if "smart_contract_guard_trace_lowering" in lowering_rules:
        bridge_lemmas.append("MumeiLean.SmartContract.no_external_call_without_lock")
    if "rtgs_settlement_lowering" in lowering_rules:
        bridge_lemmas.append("mumei_rtgs_settlement_bridge")
    if "unknown_obligation_lowering" in lowering_rules:
        bridge_lemmas.append("mumei_unknown_obligation_bridge")
    if "higher_order_predicate_lowering" in lowering_rules:
        bridge_lemmas.append("mumei_higher_order_predicate_bridge")
    if "inductive_definition_lowering" in lowering_rules:
        bridge_lemmas.append("mumei_inductive_definition_bridge")
    if "implication_lowering" in lowering_rules:
        bridge_lemmas.append("mumei_implication_bridge")
    if "let_binding_lowering" in lowering_rules:
        bridge_lemmas.append("mumei_let_binding_bridge")
    if "quantifier_skolemize_lowering" in lowering_rules:
        bridge_lemmas.append("mumei_quantifier_skolemize_bridge")
    return bridge_lemmas


def _proof_trace_hints_for_rules(lowering_rules: List[str]) -> List[str]:
    hints: List[str] = []
    if "integer_overflow_bridge" in lowering_rules:
        hints.append("assert mumei_i64_in_range hypotheses before applying arithmetic lemmas")
    if "array_bounds_bridge" in lowering_rules:
        hints.append("preserve i < arr.length evidence before guarded List access")
    if "string_regex_bridge" in lowering_rules:
        hints.append("route regex/string obligations through explicit bridge assumptions")
    if "smart_contract_lowering" in lowering_rules:
        hints.append("discharge SC obligations with guard-state and balance lemmas")
    if "smart_contract_guard_trace_lowering" in lowering_rules:
        hints.append("close concrete guard traces with SmartContract.runGuard and decide")
    if "rtgs_settlement_lowering" in lowering_rules:
        hints.append("discharge RTGS obligations with validation-before-settlement and conservation lemmas")
    if "refinement_predicate_lowering" in lowering_rules:
        hints.append("carry subtype predicate witnesses through quantifier lowering")
    if "finite_field_lowering" in lowering_rules:
        hints.append("try finite-field closure lemmas before falling back to manual proof")
    if "group_theory_lowering" in lowering_rules:
        hints.append("rewrite with group associativity, identity, and inverse lemmas")
    if "crypto_primitive_lowering" in lowering_rules:
        hints.append("apply hash/signature/encryption pattern lemma matching the primitive")
    if "unknown_obligation_lowering" in lowering_rules:
        hints.append("replace the unknown obligation placeholder with a named manual lemma")
    if "higher_order_predicate_lowering" in lowering_rules:
        hints.append("instantiate predicate hypotheses before arithmetic simplification")
    if "inductive_definition_lowering" in lowering_rules:
        hints.append("split base and step cases with the AdvancedPatterns induction lemmas")
    if "implication_lowering" in lowering_rules:
        hints.append("use MumeiLean.Quantifiers.mumei_implies_intro for implication goals")
    if "let_binding_lowering" in lowering_rules:
        hints.append("unfold let bindings before applying arithmetic or predicate lemmas")
    if "quantifier_skolemize_lowering" in lowering_rules:
        hints.append("apply skolemize_bounded_exists or herbrand_bounded_forall from Quantifiers module")
    return hints


def _result_binder_for_source(source: str, tokens: List[tuple]) -> TranslatorIRBinder:
    mumei_type = "i64"
    lean_type = "Int"
    for idx, (kind, text) in enumerate(tokens):
        if kind == "ID" and text == "result" and idx + 1 < len(tokens) and tokens[idx + 1] == ("OP", "["):
            mumei_type = "array<i64>"
            lean_type = "List Int"
        if kind == "STR" and any(tok == ("ID", "result") for tok in tokens):
            mumei_type = "string"
            lean_type = "String"
        if kind == "ID" and text in _STRING_FUNCTIONS and idx + 1 < len(tokens) and tokens[idx + 1] == ("OP", "("):
            close = _find_matching(tokens, idx + 1, "(", ")")
            if close != -1:
                for arg in _split_top_level(tokens, idx + 2, close):
                    if any(tok == ("ID", "result") for tok in arg):
                        mumei_type = "string"
                        lean_type = "String"
    return TranslatorIRBinder("result", "result", mumei_type, lean_type, role="result")


def _extract_predicate_identifiers(tokens: List[tuple]) -> List[str]:
    return list(_extract_predicate_arities(tokens))


def _is_predicate_call_name(name: str) -> bool:
    return (
        bool(name)
        and name[0].isupper()
        and name not in _RESERVED_IDENTS
        and name not in _KNOWN_FUNCTIONS
    )


def _extract_predicate_arities(tokens: List[tuple]) -> Dict[str, int]:
    predicate_arities: Dict[str, int] = {}
    for idx, (kind, text) in enumerate(tokens):
        if (
            kind == "ID"
            and text in _HIGHER_ORDER_PREDICATE_FUNCTIONS
            and idx + 1 < len(tokens)
            and tokens[idx + 1] == ("OP", "(")
        ):
            close = _find_matching(tokens, idx + 1, "(", ")")
            if close == -1:
                continue
            parts = _split_top_level(tokens, idx + 2, close)
            if not parts or len(parts[0]) != 1 or parts[0][0][0] != "ID":
                continue
            name = parts[0][0][1]
            if name not in _RESERVED_IDENTS:
                predicate_arities[name] = max(predicate_arities.get(name, 1), 1)
        elif (
            kind == "ID"
            and _is_predicate_call_name(text)
            and idx + 1 < len(tokens)
            and tokens[idx + 1] == ("OP", "(")
        ):
            close = _find_matching(tokens, idx + 1, "(", ")")
            if close == -1:
                continue
            arity = len(_split_top_level(tokens, idx + 2, close))
            if arity > 0:
                predicate_arities[text] = max(predicate_arities.get(text, 1), arity)
    return predicate_arities


def classify_obligation(tokens: List[tuple], lowering_rules: List[str]) -> str:
    """Classify the obligation into one of the formal obligation classes.

    The classification uses a priority order: crypto > finite_field >
    group_theory > smart_contract > rtgs > quantifier > unknown >
    arithmetic. The first matching class wins; mixed obligations inherit
    the highest-priority class for bridge lemma selection.
    Arithmetic is the fallback when no other class matches.
    """
    has_crypto = any(
        kind == "ID" and text in _CRYPTO_FUNCTIONS for kind, text in tokens
    ) or "crypto_primitive_lowering" in lowering_rules
    has_ff = any(
        kind == "ID" and text in _FINITE_FIELD_FUNCTIONS for kind, text in tokens
    ) or "finite_field_lowering" in lowering_rules
    has_group = any(
        kind == "ID" and text in _GROUP_FUNCTIONS for kind, text in tokens
    ) or "group_theory_lowering" in lowering_rules
    has_guard_trace = "smart_contract_guard_trace_lowering" in lowering_rules
    has_sc = any(
        kind == "ID" and text in _SMART_CONTRACT_FUNCTIONS for kind, text in tokens
    ) or "smart_contract_lowering" in lowering_rules
    has_rtgs = any(
        kind == "ID" and text in _RTGS_FUNCTIONS for kind, text in tokens
    ) or "rtgs_settlement_lowering" in lowering_rules
    has_quantifier = any(
        kind == "KW" and text in _QUANTIFIER_KEYWORDS for kind, text in tokens
    ) or "refinement_predicate_lowering" in lowering_rules
    has_unknown = any(
        kind == "ID" and text in _UNKNOWN_OBLIGATION_FUNCTIONS for kind, text in tokens
    ) or "unknown_obligation_lowering" in lowering_rules

    if has_crypto:
        return OBLIGATION_CLASS_CRYPTO
    if has_ff:
        return OBLIGATION_CLASS_FINITE_FIELD
    if has_group:
        return OBLIGATION_CLASS_GROUP_THEORY
    if has_guard_trace:
        return OBLIGATION_CLASS_SMART_CONTRACT_GUARD_TRACE
    if has_sc:
        return OBLIGATION_CLASS_SMART_CONTRACT
    if has_rtgs:
        return OBLIGATION_CLASS_RTGS
    if has_quantifier:
        return OBLIGATION_CLASS_QUANTIFIER
    if has_unknown:
        return OBLIGATION_CLASS_UNKNOWN
    return OBLIGATION_CLASS_ARITHMETIC


def obligation_bridge_lemmas(obligation_class: str) -> List[str]:
    """Return the canonical bridge lemma entry points for an obligation class."""
    return list(_OBLIGATION_CLASS_BRIDGE_LEMMAS.get(obligation_class, []))


def _sanitize_lean_identifier(name: str) -> str:
    clean = "".join(ch if ch.isalnum() or ch == "_" else "_" for ch in name)
    clean = clean.strip("_")
    if not clean:
        return "generated_theorem"
    if clean[0].isdigit():
        clean = f"_{clean}"
    return clean


def guard_trace_expected_to_lean(expected_outcome: Any) -> str:
    if expected_outcome is True:
        return "some GuardState.Unlocked"
    if expected_outcome is False:
        return "none"
    if not isinstance(expected_outcome, str):
        raise ValueError(f"unsupported guard trace outcome: {expected_outcome!r}")
    normalized = expected_outcome.strip()
    lowered = normalized.lower()
    if normalized in {"some GuardState.Unlocked", "none"}:
        return normalized
    if lowered in {"safe", "guarded", "some", "unlocked"}:
        return "some GuardState.Unlocked"
    if lowered in {"unsafe", "unguarded", "none", "exposed"}:
        return "none"
    raise ValueError(f"unsupported guard trace outcome: {expected_outcome!r}")


def normalize_guard_trace_translator_ir(translator_ir: Dict[str, Any]) -> Dict[str, Any]:
    guard_trace = translator_ir.get("guard_trace")
    if not isinstance(guard_trace, dict):
        return translator_ir
    ops = guard_trace.get("ops")
    if not isinstance(ops, list) or not all(isinstance(op, str) for op in ops):
        return translator_ir
    expected_outcome = guard_trace.get("expected_outcome")
    if expected_outcome is None:
        return translator_ir
    try:
        lean_expected_outcome = guard_trace_expected_to_lean(expected_outcome)
    except ValueError:
        return translator_ir
    normalized = dict(translator_ir)
    normalized_guard_trace = {
        "ops": [str(op) for op in ops],
        "expected_outcome": expected_outcome,
    }
    normalized["guard_trace"] = normalized_guard_trace
    normalized["guard_trace_ops"] = list(normalized_guard_trace["ops"])
    normalized["guard_trace_expected_outcome"] = normalized_guard_trace["expected_outcome"]
    normalized["theorem_goal"] = (
        "runGuard GuardState.Unlocked "
        f"[{', '.join(f'GuardOp.{op}' for op in normalized_guard_trace['ops'])}] = "
        f"{lean_expected_outcome}"
    )
    normalized["obligation_class"] = OBLIGATION_CLASS_SMART_CONTRACT_GUARD_TRACE
    lowering_rules = normalized.setdefault("lowering_rules", [])
    if SMART_CONTRACT_GUARD_TRACE_LOWERING not in lowering_rules:
        lowering_rules.append(SMART_CONTRACT_GUARD_TRACE_LOWERING)
    proof_trace_hints = normalized.setdefault("proof_trace_hints", [])
    hint = "use the concrete guard trace with SmartContract.runGuard"
    if hint not in proof_trace_hints:
        proof_trace_hints.append(hint)
    requires_bridge_lemmas = normalized.setdefault("requires_bridge_lemmas", [])
    bridge_lemma = "MumeiLean.SmartContract.no_external_call_without_lock"
    if bridge_lemma not in requires_bridge_lemmas:
        requires_bridge_lemmas.append(bridge_lemma)
    return normalized


def render_guard_trace_theorem(
    atom_name: str,
    guard_trace: Dict[str, Any],
    provenance_prefix: str = "",
) -> str:
    ops = guard_trace.get("ops")
    if not isinstance(ops, list) or not all(isinstance(op, str) for op in ops):
        raise ValueError("guard trace must include an ordered list of op strings")
    theorem_name = f"{_sanitize_lean_identifier(atom_name)}_correct"
    ops_expr = ", ".join(f"GuardOp.{op}" for op in ops)
    expected_outcome = guard_trace.get("expected_outcome")
    if expected_outcome is None:
        raise ValueError("guard trace must include a recognized expected_outcome")
    expected = guard_trace_expected_to_lean(expected_outcome)
    return provenance_prefix + "\n".join(
        [
            f"theorem {theorem_name} :",
            f"    runGuard GuardState.Unlocked [{ops_expr}] = {expected} := by",
            "  decide",
            "",
        ]
    )


def _build_translator_ir(
    source: str,
    lean_expr: str,
    identifiers: List[str],
    array_ids: List[str],
    string_ids: List[str],
    tokens: List[tuple],
    manual_lemma_reason: Optional[str],
) -> TranslatorIR:
    predicate_arities = _extract_predicate_arities(tokens)
    predicate_ids = list(predicate_arities)
    binders = [
        _binder_for_identifier(name, array_ids, string_ids, predicate_ids, predicate_arities)
        for name in identifiers
    ]
    if contains_identifier(source, "result") and "result" not in identifiers:
        binders.append(_result_binder_for_source(source, tokens))
    sort = "manual_lemma_required" if manual_lemma_reason else "contract_obligation"
    lowering_rules = _lowering_rules(tokens, array_ids, string_ids)
    obl_class = classify_obligation(tokens, lowering_rules)
    bridge_lemmas = _bridge_lemmas_for_rules(lowering_rules)
    obl_lemmas = obligation_bridge_lemmas(obl_class)
    for lemma in obl_lemmas:
        if lemma not in bridge_lemmas:
            bridge_lemmas.append(lemma)
    return TranslatorIR(
        sort=sort,
        binders=binders,
        theorem_goal=lean_expr,
        lowering_rules=lowering_rules,
        manual_lemma_reason=manual_lemma_reason,
        semantic_gap_notes=_build_semantic_gap_notes(tokens, array_ids, string_ids),
        proof_trace_hints=_proof_trace_hints_for_rules(lowering_rules),
        requires_bridge_lemmas=bridge_lemmas,
        obligation_class=obl_class,
    )


def _make_translation_result(
    source: str,
    lean_expr: str,
    identifiers: List[str],
    is_trivial: bool,
    is_partial: bool,
    array_identifiers: List[str],
    string_identifiers: List[str],
    predicate_identifiers: Optional[List[str]] = None,
    tokens: Optional[List[tuple]] = None,
) -> TranslationResult:
    result = TranslationResult(
        lean_expr=lean_expr,
        identifiers=identifiers,
        is_trivial=is_trivial,
        is_partial=is_partial,
        array_identifiers=array_identifiers,
        string_identifiers=string_identifiers,
        predicate_identifiers=predicate_identifiers or [],
    )
    result = _attach_translator_ir(source, result, tokens)
    if result.translator_ir is not None:
        for issue in validate_translator_ir_compliance(result.translator_ir):
            print(f"TranslatorIR compliance warning: {issue}")
    return result


def _attach_translator_ir(
    source: str,
    result: TranslationResult,
    tokens: Optional[List[tuple]] = None,
) -> TranslationResult:
    real_tokens = tokens if tokens is not None else _tokenize(source or "")
    result.predicate_identifiers = _extract_predicate_identifiers(real_tokens)
    result.predicate_arities = _extract_predicate_arities(real_tokens)
    reasons = _unsupported_reasons(source or "", real_tokens, result.is_partial)
    result.unsupported_reasons = reasons
    result.manual_lemma_reason = ";".join(reasons) if reasons else None
    result.translator_ir = _build_translator_ir(
        source or "",
        result.lean_expr,
        result.identifiers,
        result.array_identifiers,
        result.string_identifiers,
        real_tokens,
        result.manual_lemma_reason,
    )
    return result


def _extract_identifiers(tokens: List[tuple]) -> List[str]:
    seen: List[str] = []
    i = 0
    while i < len(tokens):
        kind, text = tokens[i]
        if (
            kind == "ID"
            and text == "old"
            and i + 1 < len(tokens)
            and tokens[i + 1] == ("OP", "(")
        ):
            close = _find_matching(tokens, i + 1, "(", ")")
            if close != -1:
                parts = _split_top_level(tokens, i + 2, close)
                if (
                    len(parts) == 1
                    and len(parts[0]) == 1
                    and parts[0][0][0] == "ID"
                ):
                    old_name = f"old_{parts[0][0][1]}"
                    if old_name not in seen:
                        seen.append(old_name)
                    i = close + 1
                    continue
        if kind != "ID":
            i += 1
            continue
        if text in _RESERVED_IDENTS:
            i += 1
            continue
        if text not in seen:
            seen.append(text)
        i += 1
    return seen


def _parse_let_binding_scope(
    tokens: List[tuple], start: int
) -> Optional[tuple[str, int, int]]:
    if start + 1 >= len(tokens) or tokens[start + 1][0] != "ID":
        return None
    var_name = tokens[start + 1][1]
    eq_idx = -1
    j = start + 2
    if j < len(tokens) and tokens[j] == ("OP", "="):
        eq_idx = j
    elif j < len(tokens) and tokens[j] == ("OP", ":"):
        j2 = j + 1
        while j2 < len(tokens) and tokens[j2][0] == "ID":
            j2 += 1
        if j2 < len(tokens) and tokens[j2] == ("OP", "="):
            eq_idx = j2
    if eq_idx == -1:
        return None

    in_idx = -1
    depth = 0
    j = eq_idx + 1
    while j < len(tokens):
        tk, tt = tokens[j]
        if tk == "OP" and tt in ("(", "[", "{"):
            depth += 1
        elif tk == "OP" and tt in (")", "]", "}"):
            depth -= 1
        elif tk == "KW" and tt == "in" and depth == 0:
            in_idx = j
            break
        j += 1
    if in_idx == -1:
        return None

    body_end = len(tokens)
    depth = 0
    j = in_idx + 1
    while j < len(tokens):
        tk, tt = tokens[j]
        if depth == 0 and tk == "OP" and tt in {",", ")", "]", "}"}:
            body_end = j
            break
        if tk == "OP" and tt in ("(", "[", "{"):
            depth += 1
        elif tk == "OP" and tt in (")", "]", "}"):
            depth -= 1
        j += 1
    return var_name, in_idx + 1, body_end


def _tokenize(source: str) -> List[tuple]:
    """Return a list of ``(kind, text)`` tuples for ``source``.

    Whitespace is dropped. Unrecognised characters are folded into a
    synthetic ``UNK`` token so the caller can flag them.
    """
    pos = 0
    tokens: List[tuple] = []
    while pos < len(source):
        m = _TOKEN_RE.match(source, pos)
        if not m or m.end() == pos:
            tokens.append(("UNK", source[pos]))
            pos += 1
            continue
        if m.lastgroup is None:
            # whitespace
            pos = m.end()
            continue
        tokens.append((m.lastgroup, m.group(m.lastgroup)))
        pos = m.end()
    return tokens


def contains_identifier(source: str, name: str) -> bool:
    """Return ``True`` iff ``source`` contains an identifier *token*
    that is exactly ``name``.

    Unlike a plain ``name in source`` substring test, this respects
    token boundaries: ``contains_identifier("results > 0", "result")``
    is ``False`` and so is ``contains_identifier("no_result > 0",
    "result")``.
    """
    if not name:
        return False
    for kind, text in _tokenize(source or ""):
        if kind == "ID" and text == name:
            return True
    return False


def _find_matching(
    tokens: List[tuple], start: int, open_tok: str, close_tok: str
) -> int:
    """Return the index of the closing ``close_tok`` matching ``tokens[start]``.

    ``tokens[start]`` must be ``("OP", open_tok)``. Returns ``-1`` if no
    matching close is found (caller should treat this as a partial
    translation failure).
    """
    depth = 0
    for j in range(start, len(tokens)):
        kind, text = tokens[j]
        if kind != "OP":
            continue
        if text == open_tok:
            depth += 1
        elif text == close_tok:
            depth -= 1
            if depth == 0:
                return j
    return -1


def _split_top_level(
    tokens: List[tuple], start: int, end: int
) -> List[List[tuple]]:
    """Split ``tokens[start:end]`` by top-level ``,`` tokens.

    Top-level meaning the comma is not nested inside ``()``/``[]``.
    """
    out: List[List[tuple]] = [[]]
    depth = 0
    for j in range(start, end):
        kind, text = tokens[j]
        if kind == "OP" and text in ("(", "[", "{"):
            depth += 1
            out[-1].append(tokens[j])
        elif kind == "OP" and text in (")", "]", "}"):
            depth -= 1
            out[-1].append(tokens[j])
        elif kind == "OP" and text == "," and depth == 0:
            out.append([])
        else:
            out[-1].append(tokens[j])
    return out


def _find_top_level_arrow(tokens: List[tuple]) -> int:
    depth = 0
    for idx, (kind, text) in enumerate(tokens):
        if kind == "OP" and text in ("(", "[", "{"):
            depth += 1
        elif kind == "OP" and text in (")", "]", "}"):
            depth -= 1
        elif kind == "OP" and text == "=>" and depth == 0:
            return idx
    return -1


def _if_else_tail_is_supported(tokens: List[tuple]) -> bool:
    depth = 0
    for kind, text in tokens:
        if kind == "OP" and text in ("(", "[", "{"):
            depth += 1
        elif kind == "OP" and text in (")", "]", "}"):
            depth -= 1
        elif depth == 0 and (
            (kind == "KW" and text != "match")
            or (kind == "OP" and text in {"&&", "||", "==", "!=", ">=", "<=", ">", "<"})
        ):
            return False
    return True


def _find_quantifier_colon(tokens: List[tuple], start: int, end: int) -> int:
    depth = 0
    for j in range(start, end):
        kind, text = tokens[j]
        if kind == "OP" and text in ("(", "[", "{"):
            depth += 1
        elif kind == "OP" and text in (")", "]", "}"):
            depth -= 1
        elif kind == "OP" and text == ":" and depth == 0:
            return j
    return -1


def _parse_quantifier_binder(tokens: List[tuple]) -> Optional[Tuple[str, str, str]]:
    if len(tokens) == 1 and tokens[0][0] == "ID":
        return tokens[0][1], "i64", "Int"
    if (
        len(tokens) == 3
        and tokens[0][0] == "ID"
        and tokens[1] == ("OP", ":")
        and tokens[2][0] == "ID"
    ):
        type_key = tokens[2][1].lower()
        type_pair = _QUANTIFIER_TYPE_ALIASES.get(type_key)
        if type_pair is not None:
            mumei_type, lean_type = type_pair
            return tokens[0][1], mumei_type, lean_type
    return None


def _parse_unbounded_quantifier(
    tokens: List[tuple], start: int
) -> Optional[Tuple[str, str, int, List[tuple]]]:
    if start + 2 >= len(tokens):
        return None
    if tokens[start][0] != "KW" or tokens[start][1] not in _QUANTIFIER_KEYWORDS:
        return None
    var_kind, var_name = tokens[start + 1]
    if var_kind != "ID":
        return None
    lean_type = "Int"
    separator_idx = -1
    if tokens[start + 2] == ("OP", ","):
        separator_idx = start + 2
    elif tokens[start + 2] == ("OP", ":"):
        if (
            start + 4 < len(tokens)
            and tokens[start + 3][0] == "ID"
            and tokens[start + 4] in {("OP", ":"), ("OP", ",")}
        ):
            type_pair = _QUANTIFIER_TYPE_ALIASES.get(tokens[start + 3][1].lower())
            if type_pair is None:
                return None
            lean_type = type_pair[1]
            separator_idx = start + 4
        else:
            separator_idx = start + 2
    if separator_idx == -1:
        return None
    body_start = separator_idx + 1
    if body_start >= len(tokens):
        return None
    return var_name, lean_type, body_start, tokens[body_start:]


def _unbounded_quantifier_type_name(tokens: List[tuple], start: int) -> Optional[str]:
    if (
        start + 4 < len(tokens)
        and tokens[start][0] == "KW"
        and tokens[start][1] in _QUANTIFIER_KEYWORDS
        and tokens[start + 1][0] == "ID"
        and tokens[start + 2] == ("OP", ":")
        and tokens[start + 3][0] == "ID"
        and tokens[start + 4] in {("OP", ":"), ("OP", ",")}
    ):
        return tokens[start + 3][1]
    return None


def _parse_bounded_range_binder(
    tokens: List[tuple],
) -> Optional[Tuple[str, List[tuple], List[tuple]]]:
    if len(tokens) < 5 or tokens[0][0] != "ID" or tokens[1] != ("KW", "in"):
        return None
    range_idx = -1
    depth = 0
    for idx in range(2, len(tokens)):
        kind, text = tokens[idx]
        if kind == "OP" and text in ("(", "[", "{"):
            depth += 1
        elif kind == "OP" and text in (")", "]", "}"):
            depth -= 1
        elif kind == "OP" and text == ".." and depth == 0:
            range_idx = idx
            break
    if range_idx == -1 or range_idx == 2 or range_idx == len(tokens) - 1:
        return None
    return tokens[0][1], tokens[2:range_idx], tokens[range_idx + 1 :]


def translate_quantifier(source: str) -> TranslationResult:
    """Translate a standalone ``forall`` / ``exists`` contract fragment.

    This public wrapper makes the quantifier lowering entry point explicit for
    callers that want to route Z3-``unknown`` quantified obligations directly
    into the Lean escalation path.
    """
    return translate_contract(source)


def _int_to_nat_expr(lean_expr: str) -> str:
    if re.fullmatch(r"\d+", lean_expr):
        return f"({lean_expr} : Int).toNat"
    if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", lean_expr):
        return f"{lean_expr}.toNat"
    return f"({lean_expr}).toNat"


def translate_bounded_quantifier_to_finset(
    quantifier: str,
    var_name: str,
    start_expr: str,
    end_expr: str,
    body_expr: str,
) -> Optional[TranslationResult]:
    """Prototype mathlib4 lowering for bounded integer quantifiers.

    ``forall(i, lo, hi, body)`` normally lowers to explicit integer guard
    implications. This helper exposes the mathlib-backed alternative used in
    the integration design: quantify over ``Finset.Ico lo.toNat hi.toNat`` and
    re-bind the Nat element back to the Mumei ``Int`` variable inside the body.
    """
    if quantifier not in _QUANTIFIER_KEYWORDS or not var_name.isidentifier():
        return None

    start = translate_body(start_expr)
    end = translate_body(end_expr)
    body = translate_contract(body_expr)
    nat_name = f"{var_name}Nat"
    interval = (
        f"Finset.Ico {_int_to_nat_expr(start.lean_expr)} "
        f"{_int_to_nat_expr(end.lean_expr)}"
    )
    binder = f"let {var_name} : Int := Int.ofNat {nat_name}; {body.lean_expr}"
    if quantifier == "forall":
        lean_expr = f"(∀ {nat_name} ∈ {interval}, {binder})"
    else:
        lean_expr = f"(∃ {nat_name} ∈ {interval}, {binder})"

    identifiers: List[str] = []
    for result in (start, end, body):
        for identifier in result.identifiers:
            if identifier not in {var_name, nat_name} and identifier not in identifiers:
                identifiers.append(identifier)
    array_ids: List[str] = []
    for result in (start, end, body):
        for identifier in result.array_identifiers:
            if identifier not in array_ids:
                array_ids.append(identifier)
    string_ids: List[str] = []
    for result in (start, end, body):
        for identifier in result.string_identifiers:
            if identifier not in string_ids:
                string_ids.append(identifier)

    is_partial = start.is_partial or end.is_partial or body.is_partial
    lowered = TranslationResult(
        lean_expr=lean_expr,
        identifiers=identifiers,
        is_trivial=False,
        is_partial=is_partial,
        array_identifiers=array_ids,
        string_identifiers=string_ids,
    )
    lowered.translator_ir = TranslatorIR(
        sort="Prop",
        binders=[
            _binder_for_identifier(identifier, array_ids, string_ids)
            for identifier in identifiers
        ],
        theorem_goal=lean_expr,
        lowering_rules=[
            "type_system_mapping",
            "contract_lowering",
            "refinement_predicate_lowering",
            "mathlib4_bridge",
            "finset_bounded_quantifier_lowering",
        ],
        semantic_gap_notes=[
            "finset_bounded_quantifier_lowering: bounded Int quantifiers use "
            "mathlib4 Finset.Ico over Nat and re-bind each element through Int.ofNat."
        ],
        proof_trace_hints=[
            "rewrite Finset.Ico membership before applying integer bounds lemmas"
        ],
        requires_bridge_lemmas=["mumei_finset_bounded_quantifier_bridge"],
    )
    return lowered


def translate_finite_field(function_name: str, arg_srcs: List[str]) -> Optional[str]:
    """Return the Lean helper call for a finite-field expression."""
    if function_name not in _FINITE_FIELD_FUNCTIONS:
        return None
    if len(arg_srcs) != _KNOWN_FUNCTION_ARITY[function_name]:
        return None
    if function_name == "ff_in_field":
        x, p = arg_srcs
        return f"(0 ≤ {x} ∧ {x} < {p})"
    if function_name == "ff_add":
        a, b, p = arg_srcs
        return f"(({a} + {b}) % {p})"
    call_args = f" {' '.join(arg_srcs)}" if arg_srcs else ""
    return f"({_KNOWN_FUNCTIONS[function_name]}{call_args})"


def translate_group_theory(function_name: str, arg_srcs: List[str]) -> Optional[str]:
    """Return the Lean helper call for a group-theory expression."""
    if function_name not in _GROUP_FUNCTIONS:
        return None
    if len(arg_srcs) != _KNOWN_FUNCTION_ARITY[function_name]:
        return None
    call_args = f" {' '.join(arg_srcs)}" if arg_srcs else ""
    return f"({_KNOWN_FUNCTIONS[function_name]}{call_args})"


def _emit_tokens(tokens: List[tuple]) -> Tuple[str, bool]:
    """Token-level emit pass with ``forall(..)``, known calls, ``arr[i]``,
    and unknown function-call rewrites.

    Returns ``(lean_source, is_partial)``. ``is_partial`` is True when
    we encountered an UNK token, an unmatched bracket, a malformed
    ``forall`` (wrong number of arguments), or a function call that is
    not one of the known built-ins (``len`` / ``abs`` / ``min`` / ``max``) — the
    generated theorem then carries a ``-- TODO: unproven`` marker.
    """
    pieces: List[str] = []
    is_partial = any(kind == "UNK" for kind, _ in tokens)
    i = 0
    n = len(tokens)
    while i < n:
        kind, text = tokens[i]

        # let var = expr in body → let var := expr in body (Lean 4 syntax)
        if kind == "KW" and text == "let":
            # Expect: let <id> = <expr> in <body>
            if i + 1 < n and tokens[i + 1][0] == "ID":
                var_name = tokens[i + 1][1]
                eq_idx = -1
                j = i + 2
                if j < n and tokens[j] == ("OP", "="):
                    eq_idx = j
                elif j < n and tokens[j] == ("OP", ":"):
                    # let x : Type = ...
                    j2 = j + 1
                    while j2 < n and tokens[j2][0] == "ID":
                        j2 += 1
                    if j2 < n and tokens[j2] == ("OP", "="):
                        eq_idx = j2
                if eq_idx != -1:
                    in_idx = -1
                    depth = 0
                    j = eq_idx + 1
                    while j < n:
                        tk, tt = tokens[j]
                        if tk == "OP" and tt in ("(", "[", "{"):
                            depth += 1
                        elif tk == "OP" and tt in (")", "]", "}"):
                            depth -= 1
                        elif tk == "KW" and tt == "in" and depth == 0:
                            in_idx = j
                            break
                        j += 1
                    if in_idx != -1:
                        expr_src, p1 = _emit_tokens(tokens[eq_idx + 1 : in_idx])
                        body_src, p2 = _emit_tokens(tokens[in_idx + 1 :])
                        pieces.append(f"(let {var_name} := {expr_src}; {body_src})")
                        is_partial = is_partial or p1 or p2
                        i = n
                        continue
            pieces.append(text)
            is_partial = True
            i += 1
            continue

        # if cond then a else b → if cond then a else b
        if kind == "KW" and text == "if":
            depth = 0
            then_idx = -1
            else_idx = -1
            j = i + 1
            while j < n:
                tk, tt = tokens[j]
                if tk == "OP" and tt in ("(", "["):
                    depth += 1
                elif tk == "OP" and tt in (")", "]"):
                    depth -= 1
                elif tk == "KW" and tt == "then" and depth == 0:
                    then_idx = j
                    break
                j += 1
            if then_idx != -1:
                depth = 0
                j = then_idx + 1
                while j < n:
                    tk, tt = tokens[j]
                    if tk == "OP" and tt in ("(", "["):
                        depth += 1
                    elif tk == "OP" and tt in (")", "]"):
                        depth -= 1
                    elif tk == "KW" and tt == "else" and depth == 0:
                        else_idx = j
                        break
                    j += 1
            if then_idx == -1 or else_idx == -1:
                pieces.append(text)
                is_partial = True
                i += 1
                continue
            cond_src, p1 = _emit_tokens(tokens[i + 1 : then_idx])
            then_src, p2 = _emit_tokens(tokens[then_idx + 1 : else_idx])
            else_src, p3 = _emit_tokens(tokens[else_idx + 1 :])
            pieces.append(f"if {cond_src} then {then_src} else {else_src}")
            is_partial = is_partial or p1 or p2 or p3
            if i != 0 or not _if_else_tail_is_supported(tokens[else_idx + 1 :]):
                is_partial = True
            i = n
            continue

        # match x { 0 => a, 1 => b, _ => c } →
        #   match x with | 0 => a | 1 => b | _ => c
        if kind == "KW" and text == "match":
            brace_idx = -1
            depth = 0
            j = i + 1
            while j < n:
                tk, tt = tokens[j]
                if tk == "OP" and tt in ("(", "["):
                    depth += 1
                elif tk == "OP" and tt in (")", "]"):
                    depth -= 1
                elif tk == "OP" and tt == "{" and depth == 0:
                    brace_idx = j
                    break
                j += 1
            if brace_idx == -1:
                pieces.append(text)
                is_partial = True
                i += 1
                continue
            close = _find_matching(tokens, brace_idx, "{", "}")
            if close == -1:
                pieces.append(text)
                is_partial = True
                i += 1
                continue
            scrutinee_src, p_scrutinee = _emit_tokens(tokens[i + 1 : brace_idx])
            arm_parts = _split_top_level(tokens, brace_idx + 1, close)
            arm_srcs: List[str] = []
            match_partial = p_scrutinee or close != n - 1
            for arm in arm_parts:
                arrow_idx = _find_top_level_arrow(arm)
                if arrow_idx == -1:
                    match_partial = True
                    continue
                pattern_tokens = arm[:arrow_idx]
                value_tokens = arm[arrow_idx + 1 :]
                if not pattern_tokens or not value_tokens:
                    match_partial = True
                    continue
                pattern_src = " ".join(text for _kind, text in pattern_tokens)
                value_src, p_value = _emit_tokens(value_tokens)
                arm_srcs.append(f"| {pattern_src} => {value_src}")
                match_partial = match_partial or p_value
            if not arm_srcs:
                pieces.append(text)
                is_partial = True
                i += 1
                continue
            pieces.append(f"(match {scrutinee_src} with {' '.join(arm_srcs)})")
            is_partial = is_partial or match_partial
            i = n if close == n - 1 else close + 1
            continue

        # forall var: body / exists var: body →
        #   (∀ var : Int, body) / (∃ var : Int, body)
        if kind == "KW" and text in _QUANTIFIER_KEYWORDS:
            parsed = _parse_unbounded_quantifier(tokens, i)
            if parsed is not None:
                var_name, lean_type, _body_start, body_tokens = parsed
                body_src, p = _emit_tokens(body_tokens)
                symbol = "∀" if text == "forall" else "∃"
                pieces.append(f"({symbol} {var_name} : {lean_type}, {body_src})")
                is_partial = is_partial or p
                i = n
                continue

        # forall(var, start, end, body) →
        #   (∀ var : Int, start ≤ var → var < end → body)
        # exists(var, body) → (∃ var : Int, body)
        # exists(var, start, end, body) →
        #   (∃ var : Int, start ≤ var ∧ var < end ∧ body)
        if (
            kind == "KW"
            and text in _QUANTIFIER_KEYWORDS
            and i + 1 < n
            and tokens[i + 1] == ("OP", "(")
        ):
            close = _find_matching(tokens, i + 1, "(", ")")
            if close == -1:
                pieces.append(text)
                is_partial = True
                i += 1
                continue
            parts = _split_top_level(tokens, i + 2, close)
            parsed_range_binder = _parse_bounded_range_binder(parts[0]) if len(parts) == 2 else None
            is_range_quantifier = parsed_range_binder is not None
            is_unbounded_quantifier = text == "exists" and len(parts) == 2 and not is_range_quantifier
            is_bounded_quantifier = len(parts) == 4
            if not (is_unbounded_quantifier or is_bounded_quantifier or is_range_quantifier):
                # Malformed — fall back to verbatim.
                pieces.append(text)
                is_partial = True
                i += 1
                continue
            parsed_binder = _parse_quantifier_binder(parts[0]) if not is_range_quantifier else None
            if parsed_binder is None:
                # Bound variable must be an identifier, optionally with a supported type.
                if not is_range_quantifier:
                    pieces.append(text)
                    is_partial = True
                    i += 1
                    continue
            if is_range_quantifier and parsed_range_binder is not None:
                var_name, start_tokens, end_tokens = parsed_range_binder
                start_src, p1 = _emit_tokens(start_tokens)
                end_src, p2 = _emit_tokens(end_tokens)
                body_src, p3 = _emit_tokens(parts[1])
                if text == "forall":
                    pieces.append(
                        f"(∀ {var_name} : Int, {start_src} ≤ {var_name} → "
                        f"{var_name} < {end_src} → {body_src})"
                    )
                else:
                    pieces.append(
                        f"(∃ {var_name} : Int, {start_src} ≤ {var_name} ∧ "
                        f"{var_name} < {end_src} ∧ {body_src})"
                    )
                is_partial = is_partial or p1 or p2 or p3
            elif is_unbounded_quantifier and parsed_binder is not None:
                var_name, _mumei_type, lean_type = parsed_binder
                body_src, p = _emit_tokens(parts[1])
                symbol = "∀" if text == "forall" else "∃"
                pieces.append(f"({symbol} {var_name} : {lean_type}, {body_src})")
                is_partial = is_partial or p
            elif parsed_binder is not None:
                var_name, _mumei_type, lean_type = parsed_binder
                start_tokens, end_tokens, body_tokens = parts[1], parts[2], parts[3]
                start_src, p1 = _emit_tokens(start_tokens)
                end_src, p2 = _emit_tokens(end_tokens)
                body_src, p3 = _emit_tokens(body_tokens)
                if text == "forall":
                    pieces.append(
                        f"(∀ {var_name} : {lean_type}, {start_src} ≤ {var_name} → "
                        f"{var_name} < {end_src} → {body_src})"
                    )
                else:
                    pieces.append(
                        f"(∃ {var_name} : {lean_type}, {start_src} ≤ {var_name} ∧ "
                        f"{var_name} < {end_src} ∧ {body_src})"
                    )
                is_partial = is_partial or p1 or p2 or p3
            i = close + 1
            continue

        # [a, b, c] → Lean list literal [a, b, c]
        if kind == "OP" and text == "[":
            close = _find_matching(tokens, i, "[", "]")
            if close == -1:
                pieces.append(text)
                is_partial = True
                i += 1
                continue
            elem_parts = _split_top_level(tokens, i + 1, close)
            elem_srcs: List[str] = []
            for elem in elem_parts:
                if not elem:
                    continue
                src, p = _emit_tokens(elem)
                elem_srcs.append(src)
                is_partial = is_partial or p
            pieces.append(f"[{', '.join(elem_srcs)}]")
            i = close + 1
            continue

        # id[expr] → ``id.get! <nat-index>``. Lean 4's ``List.get!``
        # takes a ``Nat`` index, but the surrounding mumei contract
        # binds variables (and the ``forall(i, lo, hi, …)`` quantifier)
        # at type ``Int``. We bridge the gap by emitting an ``.toNat``
        # conversion on identifier / compound indices; numeric literals
        # are left bare so Lean's polymorphic numeric literal elaboration
        # can pick the right ``Nat`` instance directly.
        if (
            kind == "ID"
            and i + 1 < n
            and tokens[i + 1] == ("OP", "[")
        ):
            close = _find_matching(tokens, i + 1, "[", "]")
            if close == -1:
                pieces.append(text)
                is_partial = True
                i += 1
                continue
            inner_tokens = tokens[i + 2 : close]
            inner_src, p = _emit_tokens(inner_tokens)
            num_only = (
                len(inner_tokens) == 1 and inner_tokens[0][0] == "NUM"
            )
            id_only = (
                len(inner_tokens) == 1 and inner_tokens[0][0] == "ID"
            )
            if num_only:
                # ``arr[5]`` → ``arr.get! 5`` (literal, infers as ``Nat``).
                pieces.append(f"{text}.get! {inner_src}")
            elif id_only:
                # ``arr[i]`` → ``arr.get! i.toNat``. Method-call binding
                # is tighter than function application in Lean, so the
                # parens around ``i.toNat`` are unnecessary.
                pieces.append(f"{text}.get! {inner_src}.toNat")
            else:
                # ``arr[i + 1]`` → ``arr.get! (i + 1).toNat``. The outer
                # parens are required for ``.toNat`` to bind to the
                # whole compound expression rather than just the last
                # token.
                pieces.append(f"{text}.get! ({inner_src}).toNat")
            is_partial = is_partial or p
            i = close + 1
            continue

        # Known calls lower into Lean helper / standard functions:
        # ``len(arr)`` → ``(mumei_len arr)``, ``abs(x)`` → ``(mumei_abs x)``,
        # ``min(a, b)`` → ``(min a b)``, ``max(a, b)`` → ``(max a b)``.
        # Unknown calls are emitted verbatim and marked partial.
        if (
            kind == "ID"
            and i + 1 < n
            and tokens[i + 1] == ("OP", "(")
        ):
            close = _find_matching(tokens, i + 1, "(", ")")
            if close == -1:
                pieces.append(text)
                is_partial = True
                i += 1
                continue
            arg_parts = _split_top_level(tokens, i + 2, close)
            if text in _KNOWN_FUNCTIONS and _KNOWN_FUNCTION_ARITY[text] == 0:
                if len(arg_parts) == 1 and not arg_parts[0]:
                    arg_parts = []
            arg_srcs: List[str] = []
            for ap in arg_parts:
                src, p = _emit_tokens(ap)
                arg_srcs.append(src)
                is_partial = is_partial or p
            if text in _KNOWN_FUNCTIONS:
                expected_arity = _KNOWN_FUNCTION_ARITY[text]
                if len(arg_parts) != expected_arity or any(not ap for ap in arg_parts):
                    pieces.append(f"{text} ({', '.join(arg_srcs)})")
                    is_partial = True
                elif text == "old":
                    old_arg = arg_parts[0]
                    if len(old_arg) == 1 and old_arg[0][0] == "ID":
                        pieces.append(f"old_{old_arg[0][1]}")
                    else:
                        pieces.append(f"old_ ({arg_srcs[0]})")
                        is_partial = True
                elif text == "holds":
                    predicate_arg = arg_parts[0]
                    if len(predicate_arg) == 1 and predicate_arg[0][0] == "ID":
                        pieces.append(f"({arg_srcs[0]} {arg_srcs[1]})")
                    else:
                        pieces.append(f"holds ({', '.join(arg_srcs)})")
                        is_partial = True
                elif text in _FINITE_FIELD_FUNCTIONS:
                    lowered = translate_finite_field(text, arg_srcs)
                    if lowered is None:
                        pieces.append(f"{text} ({', '.join(arg_srcs)})")
                        is_partial = True
                    else:
                        pieces.append(lowered)
                elif text in _GROUP_FUNCTIONS:
                    lowered = translate_group_theory(text, arg_srcs)
                    if lowered is None:
                        pieces.append(f"{text} ({', '.join(arg_srcs)})")
                        is_partial = True
                    else:
                        pieces.append(lowered)
                elif text == "implies":
                    pieces.append(f"({arg_srcs[0]} → {arg_srcs[1]})")
                elif text == "zk_verify":
                    pieces.append(f"({_KNOWN_FUNCTIONS[text]} {' '.join(arg_srcs)})")
                else:
                    call_args = f" {' '.join(arg_srcs)}" if arg_srcs else ""
                    pieces.append(f"({_KNOWN_FUNCTIONS[text]}{call_args})")
            elif _is_predicate_call_name(text):
                call_args = f" {' '.join(arg_srcs)}" if arg_srcs else ""
                pieces.append(f"({text}{call_args})")
            else:
                pieces.append(f"{text} ({', '.join(arg_srcs)})")
                is_partial = True
            i = close + 1
            continue

        if kind == "OP":
            if text == ":":
                is_partial = True
            if text == "..":
                is_partial = True
            if text == "=" and (i == 0 or tokens[i - 1] != ("OP", "!")):
                # Bare ``=`` outside a ``let..in`` binding is not part of
                # the supported contract surface (use ``==`` for equality).
                # The let handler consumes ``=`` before reaching here.
                is_partial = True
            pieces.append(_OP_TRANSLATION.get(text, text))
        elif kind == "BOOL":
            pieces.append("True" if text == "true" else "False")
        elif kind == "KW":
            pieces.append(text)
            # Keywords reaching here are malformed in the supported surface
            # (for example ``forall`` without ``(`` or a stray ``then``).
            is_partial = True
        elif kind == "STR":
            pieces.append(text)
        else:
            # Bare known helper names (without a
            # following ``(``) cannot be lowered to a Lean helper call
            # and would reference an undeclared name. Flag as partial so
            # the generated theorem carries a ``-- TODO: unproven``
            # marker rather than silently emitting broken Lean.
            if kind == "ID" and text in _KNOWN_FUNCTIONS:
                is_partial = True
            pieces.append(text)
        i += 1

    return " ".join(pieces), is_partial


def translate_contract(source: str) -> TranslationResult:
    """Translate a single mumei contract string to a Lean ``Prop``.

    The translator is deliberately *token-level*: it does not build a
    typed AST. This is enough for the initial scope (arithmetic
    comparisons + boolean connectives + bounded ``forall`` quantifiers
    and array-access ``arr[i]`` Function applications).
    """
    stripped = (source or "").strip()
    if stripped == "" or stripped == "true":
        return _make_translation_result(
            stripped,
            lean_expr="True",
            identifiers=[],
            is_trivial=True,
            is_partial=False,
            array_identifiers=[],
            string_identifiers=[],
        )
    if stripped == "false":
        return _make_translation_result(
            stripped,
            lean_expr="False",
            identifiers=[],
            is_trivial=False,
            is_partial=False,
            array_identifiers=[],
            string_identifiers=[],
        )

    tokens = _tokenize(stripped)
    lean_expr, is_partial = _emit_tokens(tokens)
    # Collect identifiers that appear in ``arr[i]`` position. These need
    # ``List Int`` typing in the rendered theorem signature so that
    # ``arr.get! i`` type-checks.
    array_idents: List[str] = []
    for j, (kind, text) in enumerate(tokens):
        # ``arr[i]``
        if (
            kind == "ID"
            and j + 1 < len(tokens)
            and tokens[j + 1] == ("OP", "[")
        ):
            if text in _RESERVED_IDENTS:
                # Reserved names like ``result`` cannot be re-typed as
                # ``List Int`` (``render_theorem`` binds them as the
                # scalar return value). Flag as partial so the generated
                # theorem carries a ``-- TODO: unproven`` marker rather
                # than silently emitting ill-typed Lean.
                is_partial = True
            elif text not in array_idents:
                array_idents.append(text)
    # ``sum(arr, n)`` / ``count(arr, val)``: the first argument is a
    # ``List Int`` in the Lean helper signatures (``mumei_sum`` /
    # ``mumei_count``), so identifiers appearing there must be typed as
    # ``List Int`` — not the scalar ``Int`` default that
    # ``render_theorem`` would otherwise emit. Without this pass the
    # generated theorem would reference ``mumei_sum arr n`` with
    # ``arr : Int``, which is a Lean type error.
    for j, (kind, text) in enumerate(tokens):
        if (
            kind == "ID"
            and text in ("sum", "count")
            and j + 1 < len(tokens)
            and tokens[j + 1] == ("OP", "(")
        ):
            close = _find_matching(tokens, j + 1, "(", ")")
            if close == -1:
                continue
            parts = _split_top_level(tokens, j + 2, close)
            if not parts or not parts[0]:
                continue
            first_arg = parts[0]
            if len(first_arg) == 1 and first_arg[0][0] == "ID":
                name = first_arg[0][1]
                if name in _RESERVED_IDENTS:
                    is_partial = True
                elif name not in array_idents:
                    array_idents.append(name)
            else:
                # Non-trivial first argument (e.g. a nested call) cannot
                # be re-typed at the parameter level; flag as partial so
                # the generated theorem carries a ``-- TODO: unproven``
                # marker.
                is_partial = True
    string_idents: List[str] = []
    for j, (kind, text) in enumerate(tokens):
        if (
            kind == "ID"
            and text in _STRING_FUNCTIONS
            and j + 1 < len(tokens)
            and tokens[j + 1] == ("OP", "(")
        ):
            close = _find_matching(tokens, j + 1, "(", ")")
            if close == -1:
                continue
            for ap in _split_top_level(tokens, j + 2, close):
                for ak, at in ap:
                    if (
                        ak == "ID"
                        and at not in _RESERVED_IDENTS
                        and at not in string_idents
                    ):
                        string_idents.append(at)
    scalar_call_idents: List[str] = []
    # Type-conflict guard: an identifier passed to a scalar known call
    # (e.g. ``len`` / ``abs`` / ``min`` / ``max`` / ``mod`` / ``pow``) that *also* appears in
    # ``arr[i]`` position
    # or string-predicate position would be typed non-``Int`` by the
    # renderer, producing a Lean type error. Flag such contracts as partial
    # so they carry a ``-- TODO: unproven`` marker instead of silently emitting
    # ill-typed Lean.
    for j, (kind, text) in enumerate(tokens):
        if (
            kind == "ID"
            and text in _SCALAR_CALL_FUNCTIONS | _ARRAY_FIRST_ARG_FUNCTIONS
            and j + 1 < len(tokens)
            and tokens[j + 1] == ("OP", "(")
        ):
            close = _find_matching(tokens, j + 1, "(", ")")
            if close == -1:
                continue
            arg_parts = _split_top_level(tokens, j + 2, close)
            # ``sum`` / ``count`` take a ``List Int`` first argument, so
            # identifiers there are legitimately non-scalar and must not
            # trip the scalar-vs-array conflict guard below. String
            # predicates take ``String`` arguments, so they also must not
            # trip the scalar-vs-string guard.
            if text in _ARRAY_FIRST_ARG_FUNCTIONS:
                arg_parts_to_scan = arg_parts[1:]
            elif text in _STRING_FUNCTIONS:
                arg_parts_to_scan = []
            else:
                arg_parts_to_scan = arg_parts
            for ap in arg_parts_to_scan:
                for ak, at in ap:
                    if ak == "ID" and at not in _RESERVED_IDENTS:
                        if at not in scalar_call_idents:
                            scalar_call_idents.append(at)
                        if at in array_idents or at in string_idents:
                            is_partial = True
                            break
    # Stand-alone commas outside known function calls / ``forall(..)`` /
    # ``arr[..]`` are not part of the supported surface; mark such
    # contracts as partial so the generated theorem still carries the
    # ``-- TODO: unproven`` triage marker.
    if not is_partial:
        depth = 0
        allowed_comma_depths: List[int] = []
        quantifier_separator_commas: Set[int] = set()
        for j, (kind, text) in enumerate(tokens):
            if kind == "KW" and text in _QUANTIFIER_KEYWORDS:
                parsed = _parse_unbounded_quantifier(tokens, j)
                if parsed is not None:
                    _var_name, _lean_type, body_start, _body_tokens = parsed
                    separator_idx = body_start - 1
                    if separator_idx >= 0 and tokens[separator_idx] == ("OP", ","):
                        quantifier_separator_commas.add(separator_idx)
        bracket_depth = 0
        brace_depth = 0
        for j, (kind, text) in enumerate(tokens):
            if kind == "OP" and text == "(":
                depth += 1
            elif kind == "OP" and text == ")":
                while allowed_comma_depths and allowed_comma_depths[-1] >= depth:
                    allowed_comma_depths.pop()
                depth -= 1
            elif kind == "OP" and text == "[":
                bracket_depth += 1
            elif kind == "OP" and text == "]":
                bracket_depth -= 1
            elif kind == "OP" and text == "{":
                brace_depth += 1
            elif kind == "OP" and text == "}":
                brace_depth -= 1
            elif (
                (
                    (kind == "KW" and text in _QUANTIFIER_KEYWORDS)
                    or (kind == "ID" and text in _KNOWN_FUNCTIONS)
                    or (kind == "ID" and _is_predicate_call_name(text))
                )
                and j + 1 < len(tokens)
                and tokens[j + 1] == ("OP", "(")
            ):
                close = _find_matching(tokens, j + 1, "(", ")")
                if close != -1:
                    allowed_comma_depths.append(depth + 1)
            elif kind == "OP" and text == ",":
                if j in quantifier_separator_commas:
                    continue
                inside_allowed_call = (
                    bool(allowed_comma_depths) and depth >= allowed_comma_depths[-1]
                )
                if not inside_allowed_call and bracket_depth == 0 and brace_depth == 0:
                    is_partial = True
                    break
    # Free identifiers are everything except reserved names AND the
    # bound variables of any quantifier. The latter are still reported
    # as ID tokens by ``_extract_identifiers`` because we don't track
    # binder scope here; Lean will simply shadow them inside the
    # quantifier body, so emitting them as ``variable`` declarations
    # would be wrong. Filter explicit quantifier-bound names out.
    bound: Set[str] = set()
    let_bound: Set[str] = set()
    let_scopes: List[tuple[int, int, str, int]] = []
    quantifier_type_names: Set[str] = set()
    i = 0
    while i < len(tokens):
        kind, text = tokens[i]
        if kind == "KW" and text in _QUANTIFIER_KEYWORDS:
            parsed_unbounded = _parse_unbounded_quantifier(tokens, i)
            if parsed_unbounded is not None:
                bound.add(parsed_unbounded[0])
                type_name = _unbounded_quantifier_type_name(tokens, i)
                if type_name is not None:
                    quantifier_type_names.add(type_name)
            elif i + 1 < len(tokens) and tokens[i + 1] == ("OP", "("):
                close = _find_matching(tokens, i + 1, "(", ")")
                if close != -1:
                    parts = _split_top_level(tokens, i + 2, close)
                    parsed_range_binder = _parse_bounded_range_binder(parts[0]) if len(parts) == 2 else None
                    valid_arity = (
                        len(parts) == 4
                        or (text == "exists" and len(parts) == 2)
                        or parsed_range_binder is not None
                    )
                    parsed_binder = _parse_quantifier_binder(parts[0]) if valid_arity else None
                    if parsed_binder is not None:
                        bound.add(parsed_binder[0])
                        if len(parts[0]) == 3:
                            quantifier_type_names.add(parts[0][2][1])
                    elif parsed_range_binder is not None:
                        bound.add(parsed_range_binder[0])
        elif kind == "KW" and text == "let":
            parsed_let = _parse_let_binding_scope(tokens, i)
            if parsed_let is not None:
                let_name, body_start, body_end = parsed_let
                let_bound.add(let_name)
                let_scopes.append((body_start, body_end, let_name, i + 1))
        i += 1
    free = [
        name for name in _extract_identifiers(tokens)
        if name not in bound
        and name not in let_bound
        and name not in quantifier_type_names
    ]
    for ident in string_idents:
        if ident in array_idents:
            is_partial = True
    # Scope-awareness guard: ``bound`` is a flat set so an ID shared
    # between a quantifier's binder and a free occurrence outside that
    # quantifier would be silently dropped from ``free``, producing Lean
    # that references an undeclared name. Detect any such collision
    # and flag the contract as partial rather than emit broken output.
    if bound:
        scope_stack: List[tuple] = []  # (close_index, bound_name)
        for j, (kind, text) in enumerate(tokens):
            while scope_stack and scope_stack[-1][0] <= j:
                scope_stack.pop()
            if kind == "KW" and text in _QUANTIFIER_KEYWORDS:
                parsed_unbounded = _parse_unbounded_quantifier(tokens, j)
                if parsed_unbounded is not None:
                    scope_stack.append((len(tokens), parsed_unbounded[0]))
                elif j + 1 < len(tokens) and tokens[j + 1] == ("OP", "("):
                    close = _find_matching(tokens, j + 1, "(", ")")
                    if close != -1:
                        parts = _split_top_level(tokens, j + 2, close)
                        parsed_range_binder = _parse_bounded_range_binder(parts[0]) if len(parts) == 2 else None
                        valid_arity = (
                            len(parts) == 4
                            or (text == "exists" and len(parts) == 2)
                            or parsed_range_binder is not None
                        )
                        parsed_binder = _parse_quantifier_binder(parts[0]) if valid_arity else None
                        if parsed_binder is not None:
                            scope_stack.append((close, parsed_binder[0]))
                        elif parsed_range_binder is not None:
                            scope_stack.append((close, parsed_range_binder[0]))
            elif kind == "ID" and text in bound:
                if not any(name == text for _, name in scope_stack):
                    is_partial = True
                    break
    if let_bound:
        for j, (kind, text) in enumerate(tokens):
            if kind != "ID" or text not in let_bound:
                continue
            if any(
                binder_idx == j and name == text
                for _, _, name, binder_idx in let_scopes
            ):
                continue
            if not any(
                start <= j < end and name == text
                for start, end, name, _ in let_scopes
            ):
                is_partial = True
                break
    return _make_translation_result(
        stripped,
        lean_expr=lean_expr,
        identifiers=free,
        is_trivial=False,
        is_partial=is_partial,
        array_identifiers=[a for a in array_idents if a in free],
        string_identifiers=[s for s in string_idents if s in free],
        tokens=tokens,
    )


_IDENT_PATTERN = r"[A-Za-z_][A-Za-z0-9_]*"


def _fragment_translation(source: str) -> tuple[str, list[str], bool]:
    tokens = _tokenize(source.strip())
    lean_expr, is_partial = _emit_tokens(tokens)
    return lean_expr, _extract_identifiers(tokens), is_partial


def _merge_identifiers(groups: list[list[str]]) -> list[str]:
    merged: list[str] = []
    for group in groups:
        for ident in group:
            if ident not in merged:
                merged.append(ident)
    return merged


def _known_body_pattern(source: str) -> Optional[TranslationResult]:
    braced_if = re.fullmatch(
        r"if\s+([^{}]+?)\s*\{\s*([^{}]+?)\s*\}\s*else\s*\{\s*([^{}]+?)\s*\}",
        source,
        re.DOTALL,
    )
    if braced_if:
        cond_src, then_src, else_src = braced_if.groups()
        cond = translate_contract(cond_src.strip())
        then_branch = translate_body(then_src.strip())
        else_branch = translate_body(else_src.strip())
        identifiers = _merge_identifiers(
            [cond.identifiers, then_branch.identifiers, else_branch.identifiers]
        )
        array_ids = _merge_identifiers(
            [
                cond.array_identifiers,
                then_branch.array_identifiers,
                else_branch.array_identifiers,
            ]
        )
        string_ids = _merge_identifiers(
            [
                cond.string_identifiers,
                then_branch.string_identifiers,
                else_branch.string_identifiers,
            ]
        )
        predicate_ids = _merge_identifiers(
            [
                cond.predicate_identifiers,
                then_branch.predicate_identifiers,
                else_branch.predicate_identifiers,
            ]
        )
        predicate_arities: Dict[str, int] = {}
        for result in (cond, then_branch, else_branch):
            for name, arity in result.predicate_arities.items():
                predicate_arities[name] = max(predicate_arities.get(name, 1), arity)
        lowered = TranslationResult(
            lean_expr=(
                f"if {cond.lean_expr} then {then_branch.lean_expr} "
                f"else {else_branch.lean_expr}"
            ),
            identifiers=identifiers,
            is_trivial=False,
            is_partial=(
                cond.is_partial
                or then_branch.is_partial
                or else_branch.is_partial
            ),
            array_identifiers=array_ids,
            string_identifiers=string_ids,
            predicate_identifiers=predicate_ids,
            predicate_arities=predicate_arities,
        )
        return _attach_translator_ir(source, lowered)

    conditional_abs = re.fullmatch(
        rf"if\s+({_IDENT_PATTERN})\s*>=\s*0\s+then\s+\1\s+else\s+(?:-\s*\1|0\s*-\s*\1)",
        source,
    )
    if conditional_abs:
        var_name = conditional_abs.group(1)
        return TranslationResult(
            lean_expr=f"if {var_name} ≥ 0 then {var_name} else - {var_name}",
            identifiers=[var_name],
            is_trivial=False,
            is_partial=False,
            array_identifiers=[],
            string_identifiers=[],
        )

    saturating_abs = re.fullmatch(
        rf"if\s+({_IDENT_PATTERN})\s*==\s*(.+?)\s+then\s+(.+?)\s+else\s+if\s+\1\s*>=\s*0\s+then\s+\1\s+else\s+(?:-\s*\1|0\s*-\s*\1)",
        source,
    )
    if saturating_abs:
        var_name, min_src, max_src = saturating_abs.groups()
        min_lean, min_ids, min_partial = _fragment_translation(min_src)
        max_lean, max_ids, max_partial = _fragment_translation(max_src)
        return TranslationResult(
            lean_expr=(
                f"if {var_name} = {min_lean} then {max_lean} "
                f"else if {var_name} ≥ 0 then {var_name} else 0 - {var_name}"
            ),
            identifiers=_merge_identifiers([[var_name], min_ids, max_ids]),
            is_trivial=False,
            is_partial=min_partial or max_partial,
            array_identifiers=[],
            string_identifiers=[],
        )

    saturating_lower_bound = re.fullmatch(
        rf"if\s+({_IDENT_PATTERN})\s*<\s*(.+?)\s+then\s+(.+?)\s+else\s+\1",
        source,
    )
    if saturating_lower_bound:
        var_name, min_src, saturated_src = saturating_lower_bound.groups()
        if re.sub(r"\s+", "", min_src) != re.sub(r"\s+", "", saturated_src):
            return None
        min_lean, min_ids, min_partial = _fragment_translation(min_src)
        return TranslationResult(
            lean_expr=f"if {var_name} < {min_lean} then {min_lean} else {var_name}",
            identifiers=_merge_identifiers([[var_name], min_ids]),
            is_trivial=False,
            is_partial=min_partial,
            array_identifiers=[],
            string_identifiers=[],
        )

    finite_field_source = source
    finite_field_braced = re.fullmatch(r"\{\s*(.*?)\s*\}", source, re.DOTALL)
    if finite_field_braced:
        finite_field_source = finite_field_braced.group(1).strip()
    finite_field_zero = re.fullmatch(
        rf"ff_zero\s*\(\s*({_IDENT_PATTERN})\s*\)",
        finite_field_source,
    )
    if finite_field_zero:
        p_name = finite_field_zero.group(1)
        return TranslationResult(
            lean_expr=f"MumeiLean.Algebra.mumei_ff_zero {p_name}",
            identifiers=[p_name],
            is_trivial=False,
            is_partial=False,
            array_identifiers=[],
            string_identifiers=[],
        )

    return None


def translate_body(body_expr: str) -> TranslationResult:
    """Translate a mumei atom body expression to a Lean term.

    The supported body surface intentionally mirrors the simple term
    subset used in contracts: arithmetic, conditionals, known pure
    calls, and compact ``match x { ... }`` arms. Empty or unsupported
    bodies are marked partial so callers can fall back to the legacy
    theorem shape.
    """
    stripped = (body_expr or "").strip()
    if not stripped:
        return _make_translation_result(
            stripped,
            lean_expr="",
            identifiers=[],
            is_trivial=False,
            is_partial=True,
            array_identifiers=[],
            string_identifiers=[],
        )
    known = _known_body_pattern(stripped)
    if known is not None:
        return _attach_translator_ir(stripped, known)
    result = translate_contract(stripped)
    if "=>" in stripped and "=>" not in result.lean_expr:
        result.is_partial = True
    return _attach_translator_ir(stripped, result)
