"""Generate Lean theorem sources from a mumei ``.proof-cert.json``.

This script is the *ingest* side of the mumei ↔ mumei-lean bridge.
It accepts either:

* a per-module ``ProofCertificate`` JSON
  (``mumei-lang/mumei`` ``mumei-core/src/proof_cert.rs::ProofCertificate``),
* a ``ProofBundle`` JSON
  (``proof_cert.rs::ProofBundle``, distributed as
  ``std-proof-bundle.json`` via SI-5 Phase 3-C),
* or an ``EscalationBundle`` JSON emitted by ``mumei --emit escalation-bundle``.

For every ``AtomCertificate`` whose ``z3_check_result`` is ``"unknown"`` or
whose escalation metadata marks it as a Lean candidate, it emits a Lean
source file under ``--out`` (default ``generated/``)
containing one ``theorem`` per atom of the form::

    theorem <atom_name>_correct
        (x y result : Int) : <requires> → <ensures> := by
      sorry

The generated files are intentionally not committed to the repository
(see ``.gitignore``); ``scripts/bridge.py`` regenerates them on
demand.

Usage::

    python scripts/ingest_cert.py path/to/.proof-cert.json
    python scripts/ingest_cert.py path/to/std-proof-bundle.json --bundle
    python scripts/ingest_cert.py cert.json --out generated --module-prefix Mumei

Returns a non-zero exit code only on hard errors (unreadable input).
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable, List, Optional

try:
    # When invoked as ``python -m scripts.ingest_cert`` or via pytest.
    from .expr_translator import (
        BRIDGE_LEMMA_HASH,
        TRANSLATOR_VERSION,
        TranslationResult,
        contains_identifier,
        translate_body,
        translate_contract,
    )
    from .known_witnesses import KNOWN_LEAN_WITNESSES
except ImportError:  # pragma: no cover - direct ``python scripts/ingest_cert.py``
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    from expr_translator import (  # type: ignore
        BRIDGE_LEMMA_HASH,
        TRANSLATOR_VERSION,
        TranslationResult,
        contains_identifier,
        translate_body,
        translate_contract,
    )
    from known_witnesses import KNOWN_LEAN_WITNESSES  # type: ignore


def _translate_expr(source: str) -> TranslationResult:
    """Translate a mumei expression into a Lean proposition fragment."""
    return translate_contract(source)


@dataclass
class IngestedAtom:
    module_key: str
    """Logical module identifier, e.g. ``std/core`` for bundle entries
    or the certificate ``file`` field stripped of its extension."""

    name: str
    """Atom name from the ``AtomCertificate``."""

    requires_translation: TranslationResult
    ensures_translation: TranslationResult

    raw_requires: str
    raw_ensures: str
    body_summary: str
    body_expr: str
    body_translation: Optional[TranslationResult]

    z3_check_result: str
    z3_result_class: str
    status: str
    escalation_reason: str
    logic_fragment_tag: str
    logic_fragment_tags: List[str]
    proof_hash: str
    translator_version: str
    bridge_lemma_hash: str
    binder_mapping: dict[str, str]
    manual_lemma_reason: Optional[str]
    translator_ir: dict

    @property
    def is_partial_translation(self) -> bool:
        body_partial = (
            self.body_translation.is_partial if self.body_translation else False
        )
        return (
            self.requires_translation.is_partial
            or self.ensures_translation.is_partial
            or body_partial
            or self.manual_lemma_reason is not None
        )


def _classify_input(payload: Any) -> str:
    """Heuristically detect ``"certificate"`` vs ``"bundle"`` JSON.

    The ``ProofBundle`` envelope always has a ``modules`` field, an escalation
    bundle has ``candidates``, and a ``ProofCertificate`` always has ``atoms``.
    """
    if not isinstance(payload, dict):
        raise ValueError(
            "input JSON root must be an object (certificate or bundle)"
        )
    if "modules" in payload and isinstance(payload["modules"], dict):
        return "bundle"
    if "candidates" in payload and isinstance(payload["candidates"], list):
        return "escalation_bundle"
    if "atoms" in payload and isinstance(payload["atoms"], list):
        return "certificate"
    raise ValueError(
        "input JSON does not look like a mumei ProofCertificate, ProofBundle, "
        "or EscalationBundle: missing 'atoms', 'modules', and 'candidates'"
    )


def _module_key_from_certificate(cert: dict) -> str:
    """Best-effort module key for a per-module certificate.

    Strips a ``.mm`` suffix and any leading ``./`` from ``cert["file"]``.
    """
    file = str(cert.get("file", "") or "atom_module")
    if file.endswith(".mm"):
        file = file[:-3]
    if file.startswith("./"):
        file = file[2:]
    return file or "atom_module"


def _iter_certificates(payload: Any) -> Iterable[tuple]:
    """Yield ``(module_key, certificate_dict)`` pairs."""
    kind = _classify_input(payload)
    if kind == "certificate":
        yield _module_key_from_certificate(payload), payload
        return
    if kind == "escalation_bundle":
        yield _module_key_from_certificate(payload), {"atoms": payload["candidates"]}
        return
    # bundle
    for key, cert in payload["modules"].items():
        yield str(key), cert


def collect_unknown_atoms(payload: Any) -> List[IngestedAtom]:
    """Walk a certificate / bundle and return Lean escalation candidates."""
    atoms: List[IngestedAtom] = []
    for module_key, cert in _iter_certificates(payload):
        for atom in cert.get("atoms", []):
            if not isinstance(atom, dict):
                continue
            is_candidate = (
                atom.get("z3_check_result") == "unknown"
                or atom.get("escalation_reason")
            )
            if not is_candidate:
                continue
            requires = atom.get("requires", "") or ""
            ensures = atom.get("ensures", "") or ""
            body_expr = atom.get("body_expr", "") or ""
            body_summary = atom.get("body_summary", "") or ""
            tags = atom.get("logic_fragment_tags", [])
            if not isinstance(tags, list):
                tags = []
            tags = [str(tag) for tag in tags]
            logic_fragment_tag = str(atom.get("logic_fragment_tag", "") or "")
            if logic_fragment_tag and not tags:
                tags.append(logic_fragment_tag)
            requires_translation = _translate_expr(requires)
            ensures_translation = _translate_expr(ensures)
            body_translation = (
                translate_body(str(body_expr)) if str(body_expr).strip() else None
            )
            translator_ir = _translator_ir_payload(
                atom,
                requires_translation,
                ensures_translation,
                body_translation,
            )
            manual_reason = atom.get("manual_lemma_reason")
            if not manual_reason:
                manual_reason = _first_manual_reason(
                    requires_translation,
                    ensures_translation,
                    body_translation,
                )
            atoms.append(
                IngestedAtom(
                    module_key=module_key,
                    name=str(atom.get("name", "atom")),
                    requires_translation=requires_translation,
                    ensures_translation=ensures_translation,
                    raw_requires=requires,
                    raw_ensures=ensures,
                    body_summary=str(body_summary),
                    body_expr=str(body_expr),
                    body_translation=body_translation,
                    z3_check_result=str(atom.get("z3_check_result", "unknown")),
                    z3_result_class=str(
                        atom.get(
                            "z3_result_class",
                            atom.get("z3_check_result", "unknown"),
                        )
                    ),
                    status=str(atom.get("status", "unknown")),
                    escalation_reason=str(atom.get("escalation_reason", "")),
                    logic_fragment_tag=logic_fragment_tag,
                    logic_fragment_tags=tags,
                    proof_hash=str(atom.get("proof_hash", "")),
                    translator_version=str(atom.get("translator_version", TRANSLATOR_VERSION)),
                    bridge_lemma_hash=str(atom.get("bridge_lemma_hash", BRIDGE_LEMMA_HASH)),
                    binder_mapping=_string_dict(atom.get("binder_mapping", {})),
                    manual_lemma_reason=(str(manual_reason) if manual_reason else None),
                    translator_ir=translator_ir,
                )
            )
    return atoms


def _string_dict(value: object) -> dict[str, str]:
    if not isinstance(value, dict):
        return {}
    return {str(k): str(v) for k, v in value.items()}


def _translator_ir_payload(atom: dict, *fallbacks: Optional[TranslationResult]) -> dict:
    raw_ir = atom.get("translator_ir")
    if isinstance(raw_ir, dict):
        return raw_ir
    binders: List[dict] = []
    lowering_rules: List[str] = []
    manual_reason: Optional[str] = None
    theorem_goal = ""
    seen_binders: set[tuple[str, str]] = set()
    for fallback in fallbacks:
        if fallback is None or fallback.translator_ir is None:
            continue
        payload = fallback.translator_ir.to_dict()
        theorem_goal = str(payload.get("theorem_goal") or theorem_goal)
        for binder in payload.get("binders", []):
            if not isinstance(binder, dict):
                continue
            key = (str(binder.get("mumei_name", "")), str(binder.get("lean_name", "")))
            if key in seen_binders:
                continue
            seen_binders.add(key)
            binders.append(binder)
        for rule in payload.get("lowering_rules", []):
            rule_text = str(rule)
            if rule_text not in lowering_rules:
                lowering_rules.append(rule_text)
        if payload.get("manual_lemma_reason"):
            manual_reason = str(payload.get("manual_lemma_reason"))
    result = {
        "sort": "manual_lemma_required" if manual_reason else "contract_obligation",
        "binders": binders,
        "theorem_goal": theorem_goal,
        "provenance_span": {"file": "", "line": 0, "col": 0, "len": 0},
        "lowering_rules": lowering_rules,
    }
    if manual_reason:
        result["manual_lemma_reason"] = manual_reason
    return result


def _first_manual_reason(*translations: Optional[TranslationResult]) -> Optional[str]:
    for translation in translations:
        if translation is not None and translation.manual_lemma_reason:
            return translation.manual_lemma_reason
    return None


def _module_to_lean_namespace(module_key: str, prefix: str) -> str:
    """Map ``std/core`` → ``Generated.Std.Core`` (or ``<prefix>.Std.Core``).

    Lean module name segments must start with an upper-case letter and
    contain only ``[A-Za-z0-9_]``; we sanitise accordingly.
    """
    parts = [p for p in module_key.replace("\\", "/").split("/") if p]
    sanitised: List[str] = []
    for part in parts:
        clean = "".join(c if c.isalnum() or c == "_" else "_" for c in part)
        if not clean:
            clean = "M"
        if clean[0].isdigit():
            clean = "M" + clean
        sanitised.append(clean[:1].upper() + clean[1:])
    return ".".join([prefix] + sanitised) if sanitised else prefix


def _module_to_path(module_key: str, prefix: str) -> Path:
    namespace = _module_to_lean_namespace(module_key, prefix)
    rel = Path(*namespace.split("."))
    return rel.with_suffix(".lean")


def module_to_path(module_key: str, prefix: str) -> Path:
    """Public wrapper around :func:`_module_to_path`.

    Returns the relative ``Generated/<...>.lean`` path that
    :func:`write_modules` would emit for the given ``module_key`` and
    ``prefix``. Exposed so the bridge can attribute build-log
    diagnostics back to the originating payload by file path.
    """
    return _module_to_path(module_key, prefix)


def _atom_result_name(atom_name: str) -> str:
    parts = [p for p in atom_name.split("_") if p]
    if not parts:
        return "atomResult"
    return parts[0] + "".join(part[:1].upper() + part[1:] for part in parts[1:]) + "Result"


_LEAN_IDENTIFIER_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")


def _lean_binder_mapping(atom: IngestedAtom) -> dict[str, str]:
    mapping = dict(atom.binder_mapping)
    raw_binders = (
        atom.translator_ir.get("binders", [])
        if isinstance(atom.translator_ir, dict)
        else []
    )
    if isinstance(raw_binders, list):
        for raw in raw_binders:
            if not isinstance(raw, dict):
                continue
            mumei_name = str(raw.get("mumei_name") or "")
            lean_name = str(raw.get("lean_name") or "")
            if mumei_name and lean_name:
                mapping.setdefault(mumei_name, lean_name)
    return {
        source: target
        for source, target in mapping.items()
        if source and target
    }


def _apply_identifier_mapping(source: str, mapping: dict[str, str]) -> str:
    if not mapping:
        return source
    rendered: List[str] = []
    index = 0
    while index < len(source):
        if source[index] == '"':
            start = index
            index += 1
            while index < len(source):
                if source[index] == "\\":
                    index += 2
                    continue
                if source[index] == '"':
                    index += 1
                    break
                index += 1
            rendered.append(source[start:index])
            continue
        match = _LEAN_IDENTIFIER_RE.match(source, index)
        if match:
            ident = match.group(0)
            rendered.append(mapping.get(ident, ident))
            index = match.end()
            continue
        rendered.append(source[index])
        index += 1
    return "".join(rendered)


def _map_identifier_list(
    identifiers: List[str],
    mapping: dict[str, str],
) -> List[str]:
    mapped: List[str] = []
    for ident in identifiers:
        lean_ident = mapping.get(ident, ident)
        if lean_ident not in mapped:
            mapped.append(lean_ident)
    return mapped


def _decl_parts_from_translator_ir(
    translator_ir: dict,
    binder_mapping: Optional[dict[str, str]] = None,
) -> List[str]:
    raw_binders = (
        translator_ir.get("binders", [])
        if isinstance(translator_ir, dict)
        else []
    )
    if not isinstance(raw_binders, list):
        return []
    binder_mapping = binder_mapping or {}
    grouped: dict[str, List[str]] = {}
    seen: set[str] = set()
    for raw in raw_binders:
        if not isinstance(raw, dict):
            continue
        role = str(raw.get("role") or "free")
        if role in {"quantifier", "refinement_witness"}:
            continue
        mumei_name = str(raw.get("mumei_name") or "")
        lean_name = str(
            binder_mapping.get(mumei_name)
            or raw.get("lean_name")
            or raw.get("mumei_name")
            or ""
        )
        lean_type = str(raw.get("lean_type") or "Int")
        if not lean_name or lean_name in seen:
            continue
        seen.add(lean_name)
        grouped.setdefault(lean_type, []).append(lean_name)
    return [
        f"({' '.join(names)} : {lean_type})"
        for lean_type, names in grouped.items()
    ]


def _decl_parts_for_identifiers(
    identifiers: List[str],
    array_identifiers: List[str],
    string_identifiers: List[str],
    predicate_identifiers: Optional[List[str]] = None,
    predicate_arities: Optional[dict[str, int]] = None,
) -> List[str]:
    predicate_identifiers = predicate_identifiers or []
    predicate_arities = predicate_arities or {}
    scalar = [
        ident for ident in identifiers
        if (
            ident not in array_identifiers
            and ident not in string_identifiers
            and ident not in predicate_identifiers
        )
    ]
    parts: List[str] = []
    if scalar:
        parts.append(f"({' '.join(scalar)} : Int)")
    for pred in predicate_identifiers:
        if pred in identifiers:
            arity = max(1, predicate_arities.get(pred, 1))
            pred_type = " → ".join(["Int"] * arity + ["Prop"])
            parts.append(f"({pred} : {pred_type})")
    for ident in array_identifiers:
        if ident in identifiers:
            parts.append(f"({ident} : List Int)")
    strings = [ident for ident in string_identifiers if ident in identifiers]
    if strings:
        parts.append(f"({' '.join(strings)} : String)")
    return parts


def _body_result_type(source: str, translation: TranslationResult) -> str:
    stripped = (source or "").strip()
    if not stripped:
        return "Int"
    if stripped.startswith('"'):
        return "String"
    if stripped.startswith("["):
        return "List Int"
    if stripped.startswith("forall") or stripped.startswith("exists"):
        return "Prop"
    if stripped in {"true", "false"}:
        return "Prop"
    if any(stripped.startswith(f"{name}(") for name in ("starts_with", "ends_with", "contains", "not_contains")):
        return "Prop"
    if any(stripped.startswith(f"{name}(") for name in translation.predicate_identifiers):
        return "Prop"
    if translation.string_identifiers and not translation.array_identifiers:
        if stripped in translation.string_identifiers:
            return "String"
    return "Int"


def _translator_ir_metadata(atom: IngestedAtom) -> List[str]:
    metadata = [
        f"source_atom={atom.name}",
        f"proof_hash={atom.proof_hash}",
        f"translator_version={atom.translator_version}",
        f"bridge_lemma_hash={atom.bridge_lemma_hash}",
    ]
    sort = atom.translator_ir.get("sort") if isinstance(atom.translator_ir, dict) else None
    if sort:
        metadata.append(f"translator_ir_sort={sort}")
    span = atom.translator_ir.get("provenance_span") if isinstance(atom.translator_ir, dict) else None
    if isinstance(span, dict) and span.get("file"):
        metadata.append(
            "source_span="
            f"{span.get('file')}:{span.get('line', 0)}:{span.get('col', 0)}"
        )
    if atom.manual_lemma_reason:
        metadata.append(f"manual_lemma_reason={atom.manual_lemma_reason}")
    return metadata


def render_theorem(atom: IngestedAtom) -> str:
    """Render a single Lean ``theorem`` declaration for ``atom``."""
    known_delegate = _render_known_witness_delegate(atom)
    if known_delegate is not None:
        return known_delegate

    req = atom.requires_translation
    ens = atom.ensures_translation
    body_tr = atom.body_translation
    binder_mapping = _lean_binder_mapping(atom)

    # Collect identifiers we need to quantify over.
    idents: List[str] = []
    for tr in (req, ens, body_tr):
        if tr is None:
            continue
        for ident in tr.identifiers:
            if ident not in idents:
                idents.append(ident)
    # The token-level translator strips ``result`` out of identifiers
    # via _RESERVED_IDENTS, so we re-add it explicitly when present.
    # Use the tokenizer rather than a substring / whitespace-split test
    # so identifiers like ``results`` or ``no_result`` do not falsely
    # trigger a spurious ``result : Int`` parameter.
    has_result = contains_identifier(
        atom.raw_requires, "result"
    ) or contains_identifier(atom.raw_ensures, "result")

    # Identifiers used in ``arr[i]`` position must be typed as ``List Int``
    # so that ``arr.get! i`` type-checks. Identifiers passed to string
    # predicates are typed as ``String``; the rest are scalar ``Int``.
    # Without this split, generated theorems try to call ``.get!`` on a
    # scalar, which is a Lean type error.
    array_idents: List[str] = []
    for tr in (req, ens, body_tr):
        if tr is None:
            continue
        for ident in tr.array_identifiers:
            if ident not in array_idents:
                array_idents.append(ident)
    string_idents: List[str] = []
    for tr in (req, ens, body_tr):
        if tr is None:
            continue
        for ident in tr.string_identifiers:
            if ident not in string_idents:
                string_idents.append(ident)
    predicate_idents: List[str] = []
    predicate_arities: dict[str, int] = {}
    for tr in (req, ens, body_tr):
        if tr is None:
            continue
        for ident in tr.predicate_identifiers:
            if ident not in predicate_idents:
                predicate_idents.append(ident)
            predicate_arities[ident] = max(
                predicate_arities.get(ident, 1),
                tr.predicate_arities.get(ident, 1),
            )

    result_name = _atom_result_name(atom.name)
    use_body_semantics = (
        has_result
        and body_tr is not None
        and not body_tr.is_partial
        and bool(body_tr.lean_expr.strip())
        and not contains_identifier(atom.body_expr, "result")
    )
    result_type_override = _body_result_type(atom.body_expr, body_tr) if use_body_semantics else None

    scalar_params: List[str] = [
        i for i in idents
        if (
            i not in array_idents
            and i not in string_idents
            and i not in predicate_idents
            and i != "result"
        )
    ]
    result_binder = binder_mapping.get("result", "result")
    if (
        has_result
        and result_type_override is None
        and "result" not in scalar_params
        and "result" not in array_idents
    ):
        scalar_params.append("result")

    decl_parts = (
        []
        if result_type_override is not None
        else _decl_parts_from_translator_ir(atom.translator_ir, binder_mapping)
    )
    if not decl_parts:
        decl_parts = []
        if scalar_params:
            mapped_scalar_params = _map_identifier_list(
                scalar_params,
                binder_mapping,
            )
            decl_parts.append(
                "(" + " ".join(mapped_scalar_params) + " : Int)"
            )
        for pred in predicate_idents:
            if pred != "result":
                arity = max(1, predicate_arities.get(pred, 1))
                pred_type = " → ".join(["Int"] * arity + ["Prop"])
                decl_parts.append(
                    f"({binder_mapping.get(pred, pred)} : {pred_type})"
                )
        for arr in array_idents:
            if arr != "result":
                decl_parts.append(f"({binder_mapping.get(arr, arr)} : List Int)")
        non_result_strings = [s for s in string_idents if s != "result"]
        if non_result_strings:
            mapped_strings = _map_identifier_list(
                non_result_strings,
                binder_mapping,
            )
            decl_parts.append(
                "(" + " ".join(mapped_strings) + " : String)"
            )
        if result_type_override is not None:
            decl_parts.append(f"({result_binder} : {result_type_override})")
    params_decl = " ".join(decl_parts)

    requires_lean = _apply_identifier_mapping(req.lean_expr, binder_mapping)
    ensures_lean = _apply_identifier_mapping(ens.lean_expr, binder_mapping)

    def_params = [i for i in idents if i != "result"]
    def_decl = ""
    h_body_param = ""
    if use_body_semantics:
        body_type = result_type_override or "Int"
        mapped_def_params = _map_identifier_list(def_params, binder_mapping)
        mapped_predicate_arities = {
            binder_mapping.get(name, name): arity
            for name, arity in body_tr.predicate_arities.items()
        }
        def_param_parts = _decl_parts_for_identifiers(
            mapped_def_params,
            _map_identifier_list(body_tr.array_identifiers, binder_mapping),
            _map_identifier_list(body_tr.string_identifiers, binder_mapping),
            _map_identifier_list(body_tr.predicate_identifiers, binder_mapping),
            mapped_predicate_arities,
        )
        def_params_decl = f" {' '.join(def_param_parts)}" if def_param_parts else ""
        mapped_body_expr = _apply_identifier_mapping(
            body_tr.lean_expr,
            binder_mapping,
        )
        def_decl = (
            f"def {result_name}{def_params_decl} : {body_type} :=\n"
            f"  {mapped_body_expr}\n\n"
        )
        result_args = (
            f" {' '.join(mapped_def_params)}" if mapped_def_params else ""
        )
        h_body_param = (
            f" (h_body : {result_binder} = {result_name}{result_args})"
        )

    # Default tactic body: try ``mumei_arith`` (mathlib4-backed
    # ``omega`` / ``linarith`` / ``norm_num`` / ``simp`` cascade). Any
    # obligation this cannot close is left as a Lean build failure so
    # ``scripts/export_cert.py`` can attribute it to the owning atom.
    if use_body_semantics:
        body = f"  rw [h_body]\n  unfold {result_name}\n  mumei_arith_deep"
    else:
        body = "  mumei_arith"
    notes: List[str] = []
    if req.is_partial or ens.is_partial or atom.manual_lemma_reason:
        notes.append(
            "  -- manual_lemma_required: "
            f"{atom.manual_lemma_reason or req.manual_lemma_reason or ens.manual_lemma_reason}"
        )
    if body_tr is not None and not use_body_semantics:
        notes.append("  -- body semantics unsupported; using contract-only fallback")
    if req.is_trivial:
        notes.append("  -- requires is trivially true")

    note_block = "\n".join(notes)
    if note_block:
        note_block += "\n"

    metadata = [f"z3_check_result={atom.z3_check_result}"]
    if atom.z3_result_class:
        metadata.append(f"z3_result_class={atom.z3_result_class}")
    metadata.extend(_translator_ir_metadata(atom))
    if atom.escalation_reason:
        metadata.append(f"escalation_reason={atom.escalation_reason}")
    if atom.logic_fragment_tags:
        metadata.append("logic_fragments=" + ",".join(atom.logic_fragment_tags))
    traceability_comments: List[str] = []
    if atom.escalation_reason:
        traceability_comments.append(
            f"-- mumei_escalation_reason: {atom.escalation_reason}"
        )
    if atom.logic_fragment_tags:
        traceability_comments.append(
            "-- mumei_logic_fragment_tags: " + ",".join(atom.logic_fragment_tags)
        )
    if atom.z3_result_class:
        traceability_comments.append(f"-- mumei_z3_result_class: {atom.z3_result_class}")
    traceability_block = "\n".join(traceability_comments)
    if traceability_block:
        traceability_block += "\n"
    decl = (
        def_decl +
        traceability_block +
        f"/-- Auto-generated from mumei atom `{atom.name}` "
        f"({' ; '.join(metadata)}). -/\n"
        f"theorem {atom.name}_correct {params_decl}{h_body_param} :\n"
        f"    ({requires_lean}) → ({ensures_lean}) := by\n"
        f"{note_block}{body}\n"
    )
    return decl


def _render_known_witness_delegate(atom: IngestedAtom) -> Optional[str]:
    witness = KNOWN_LEAN_WITNESSES.get(atom.name)
    if witness is None or atom.module_key != witness["module_key"]:
        return None
    metadata = [f"z3_check_result={atom.z3_check_result}", "known_witness_used=true"]
    metadata.extend(_translator_ir_metadata(atom))
    if atom.name == "abs_saturating":
        return (
            f"/-- Auto-generated from mumei atom `{atom.name}` "
            f"({' ; '.join(metadata)}). -/\n"
            "theorem abs_saturating_correct (x result : Int)\n"
            "    (h_body : result = MumeiLean.StdMathAbs.absSaturatingResult x) :\n"
            "    (True) → (result ≥ 0) := by\n"
            "  intro _h_req\n"
            "  exact MumeiLean.StdMathAbs.abs_saturating_correct x result h_body\n"
        )
    return None


def render_module(module_key: str, prefix: str, atoms: List[IngestedAtom]) -> str:
    """Render the full Lean source for a module's worth of atoms."""
    namespace = _module_to_lean_namespace(module_key, prefix)
    header = (
        "import MumeiLean\n\n"
        "/-!\n"
        f"# {namespace}\n\n"
        f"Auto-generated by `scripts/ingest_cert.py` for mumei module "
        f"`{module_key}`.\n\n"
        "Do **not** edit this file by hand: it is regenerated on every\n"
        "`bridge.py` invocation. Atoms whose `z3_check_result` is\n"
        "`unknown` in the source `.proof-cert.json` are emitted here as\n"
        "Lean theorem statements that must be discharged by automation;\n"
        "unclosed goals are reported as build failures.\n"
        "-/\n\n"
        f"namespace {namespace}\n\n"
        "open MumeiLean\n\n"
    )
    body = "\n".join(render_theorem(a) for a in atoms)
    footer = f"\nend {namespace}\n"
    return header + body + footer


def write_modules(
    atoms: List[IngestedAtom],
    out_dir: Path,
    module_prefix: str,
) -> List[Path]:
    """Group ``atoms`` by ``module_key`` and write one Lean file each.

    Returns the list of files written.
    """
    by_module: dict[str, List[IngestedAtom]] = {}
    for atom in atoms:
        by_module.setdefault(atom.module_key, []).append(atom)

    written: List[Path] = []
    for module_key, group in sorted(by_module.items()):
        rel = _module_to_path(module_key, module_prefix)
        target = out_dir / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(render_module(module_key, module_prefix, group))
        written.append(target)
    return written


def main(argv: Optional[List[str]] = None) -> int:
    parser = argparse.ArgumentParser(
        description="Translate a mumei .proof-cert.json into Lean theorem sources.",
    )
    parser.add_argument(
        "input",
        type=Path,
        help="Path to a mumei ProofCertificate (.proof-cert.json), "
        "ProofBundle (std-proof-bundle.json), or escalation bundle.",
    )
    parser.add_argument(
        "--bundle",
        action="store_true",
        help="Force interpreting the input as a ProofBundle "
        "(otherwise auto-detected).",
    )
    parser.add_argument(
        "--out",
        type=Path,
        default=Path("generated"),
        help="Output directory for generated Lean sources "
        "(default: generated/).",
    )
    parser.add_argument(
        "--module-prefix",
        default="Generated",
        help="Top-level Lean module prefix for emitted files "
        "(default: Generated).",
    )
    parser.add_argument(
        "--print-summary",
        action="store_true",
        help="Print a one-line summary instead of the list of written files.",
    )
    args = parser.parse_args(argv)

    if not args.input.exists():
        print(f"error: input file does not exist: {args.input}", file=sys.stderr)
        return 2

    payload = json.loads(args.input.read_text())
    if args.bundle and "modules" not in payload:
        print("error: --bundle was specified but input has no 'modules' field",
              file=sys.stderr)
        return 2

    atoms = collect_unknown_atoms(payload)
    written = write_modules(atoms, args.out, args.module_prefix)

    if args.print_summary:
        print(
            f"ingest: {len(atoms)} unknown atoms across "
            f"{len(written)} module(s) written to {args.out}"
        )
    else:
        for path in written:
            print(path)
    return 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
