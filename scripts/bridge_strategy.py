"""Proof-strategy selection helpers for bridge metadata."""
from __future__ import annotations

from typing import List

try:
    from .ingest_cert import IngestedAtom
except ImportError:  # pragma: no cover - direct ``python scripts/bridge.py``
    from ingest_cert import IngestedAtom  # type: ignore


def select_proof_strategy(atom: IngestedAtom) -> dict:
    """Select an automated proof strategy based on TranslatorIR metadata.

    Examines the atom's ``lowering_rules`` and ``requires_bridge_lemmas``
    to choose which Lean tactic or proof pattern to attempt first. This
    enables the bridge to emit targeted ``by`` blocks rather than falling
    back to the generic ``mumei_arith`` cascade for every obligation.

    Returns a dict with:
    - ``strategy``: name of the proof strategy
    - ``tactics``: ordered list of Lean tactics to try
    - ``imports``: additional Lean imports required
    - ``hints``: human-readable explanation
    """
    ir = atom.translator_ir
    if not isinstance(ir, dict):
        return {
            "strategy": "default",
            "tactics": ["mumei_arith"],
            "imports": [],
            "hints": "no TranslatorIR metadata; using default cascade",
        }
    rules = ir.get("lowering_rules", [])
    hints_list = ir.get("proof_trace_hints", [])

    tactics: List[str] = []
    imports: List[str] = []
    strategy = "default"

    if "finite_field_lowering" in rules:
        strategy = "finite_field"
        tactics.extend(["unfold MumeiLean.Algebra.mumei_ff_in_field",
                         "constructor", "exact Int.emod_nonneg _ _",
                         "exact Int.emod_lt_of_pos _ _"])
        imports.append("MumeiLean.Algebra")

    if "group_theory_lowering" in rules:
        strategy = "group_theory" if strategy == "default" else f"{strategy}+group"
        tactics.extend(["simp [mul_assoc]", "ring"])
        imports.append("MumeiLean.Algebra")

    if "crypto_primitive_lowering" in rules:
        strategy = "crypto" if strategy == "default" else f"{strategy}+crypto"
        tactics.extend(["unfold MumeiLean.Crypto.hash",
                         "unfold MumeiLean.Crypto.encrypt",
                         "unfold MumeiLean.Crypto.decrypt",
                         "ring"])
        imports.append("MumeiLean.Crypto")

    if "quantifier_skolemize_lowering" in rules:
        strategy = "skolemize" if strategy == "default" else f"{strategy}+skolemize"
        tactics.extend(["rcases", "exact"])
        imports.append("MumeiLean.Quantifiers")

    if "implication_lowering" in rules:
        strategy = "implication" if strategy == "default" else f"{strategy}+implication"
        tactics.extend(["intro", "exact"])
        imports.append("MumeiLean.Quantifiers")

    if "higher_order_predicate_lowering" in rules:
        strategy = "higher_order" if strategy == "default" else f"{strategy}+higher_order"
        tactics.extend(["intro", "apply", "exact"])
        imports.append("MumeiLean.AdvancedPatterns")

    if not tactics:
        tactics = ["mumei_arith"]

    return {
        "strategy": strategy,
        "tactics": tactics,
        "imports": sorted(set(imports)),
        "hints": "; ".join(hints_list) if hints_list else "using default cascade",
    }


def resolve_mathlib_imports(atom: IngestedAtom) -> List[str]:
    """Determine which mathlib4 modules should be imported based on the atom's
    TranslatorIR lowering rules.

    Returns a list of Lean ``import`` strings. This allows ``ingest_cert.py``
    to emit the correct imports at the top of generated Lean files without
    requiring manual specification.
    """
    ir = atom.translator_ir
    if not isinstance(ir, dict):
        return []
    rules = ir.get("lowering_rules", [])
    imports: List[str] = []
    if "finite_field_lowering" in rules:
        imports.extend([
            "import Mathlib.Data.ZMod.Basic",
            "import Mathlib.Data.Int.ModEq",
        ])
    if "group_theory_lowering" in rules:
        imports.append("import Mathlib.Algebra.Group.Basic")
    if "crypto_primitive_lowering" in rules:
        imports.extend([
            "import Mathlib.Data.Int.ModEq",
            "import Mathlib.Data.Nat.Totient",
        ])
    if "integer_overflow_bridge" in rules:
        imports.append("import Mathlib.Tactic")
    return sorted(set(imports))
