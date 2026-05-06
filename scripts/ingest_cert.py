"""Generate Lean theorem sources from a mumei ``.proof-cert.json``.

This script is the *ingest* side of the mumei ↔ mumei-lean bridge.
It accepts either:

* a per-module ``ProofCertificate`` JSON
  (``mumei-lang/mumei`` ``mumei-core/src/proof_cert.rs::ProofCertificate``),
* or a ``ProofBundle`` JSON
  (``proof_cert.rs::ProofBundle``, distributed as
  ``std-proof-bundle.json`` via SI-5 Phase 3-C).

For every ``AtomCertificate`` whose ``z3_check_result`` is ``"unknown"``
it emits a Lean source file under ``--out`` (default ``generated/``)
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
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable, List, Optional

try:
    # When invoked as ``python -m scripts.ingest_cert`` or via pytest.
    from .expr_translator import (
        TranslationResult,
        contains_identifier,
        translate_body,
        translate_contract,
    )
except ImportError:  # pragma: no cover - direct ``python scripts/ingest_cert.py``
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    from expr_translator import (  # type: ignore
        TranslationResult,
        contains_identifier,
        translate_body,
        translate_contract,
    )


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
    status: str


def _classify_input(payload: Any) -> str:
    """Heuristically detect ``"certificate"`` vs ``"bundle"`` JSON.

    The ``ProofBundle`` envelope always has a ``modules`` field, while
    a ``ProofCertificate`` always has ``atoms``.
    """
    if not isinstance(payload, dict):
        raise ValueError(
            "input JSON root must be an object (ProofCertificate or ProofBundle)"
        )
    if "modules" in payload and isinstance(payload["modules"], dict):
        return "bundle"
    if "atoms" in payload and isinstance(payload["atoms"], list):
        return "certificate"
    raise ValueError(
        "input JSON does not look like a mumei ProofCertificate or ProofBundle: "
        "missing both 'atoms' and 'modules'"
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
    # bundle
    for key, cert in payload["modules"].items():
        yield str(key), cert


def collect_unknown_atoms(payload: Any) -> List[IngestedAtom]:
    """Walk a ``ProofCertificate`` / ``ProofBundle`` and return all
    ``AtomCertificate`` entries whose ``z3_check_result`` is
    ``"unknown"``.
    """
    atoms: List[IngestedAtom] = []
    for module_key, cert in _iter_certificates(payload):
        for atom in cert.get("atoms", []):
            if not isinstance(atom, dict):
                continue
            if atom.get("z3_check_result") != "unknown":
                continue
            requires = atom.get("requires", "") or ""
            ensures = atom.get("ensures", "") or ""
            body_expr = atom.get("body_expr", "") or ""
            body_summary = atom.get("body_summary", "") or ""
            atoms.append(
                IngestedAtom(
                    module_key=module_key,
                    name=str(atom.get("name", "atom")),
                    requires_translation=_translate_expr(requires),
                    ensures_translation=_translate_expr(ensures),
                    raw_requires=requires,
                    raw_ensures=ensures,
                    body_summary=str(body_summary),
                    body_expr=str(body_expr),
                    body_translation=(
                        translate_body(str(body_expr))
                        if str(body_expr).strip()
                        else None
                    ),
                    z3_check_result=str(atom.get("z3_check_result", "unknown")),
                    status=str(atom.get("status", "unknown")),
                )
            )
    return atoms


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


def render_theorem(atom: IngestedAtom) -> str:
    """Render a single Lean ``theorem`` declaration for ``atom``."""
    req = atom.requires_translation
    ens = atom.ensures_translation
    body_tr = atom.body_translation

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

    scalar_params: List[str] = [
        i for i in idents if i not in array_idents and i not in string_idents
    ]
    if has_result and "result" not in scalar_params and "result" not in array_idents:
        scalar_params.append("result")

    decl_parts: List[str] = []
    if scalar_params:
        decl_parts.append("(" + " ".join(scalar_params) + " : Int)")
    for arr in array_idents:
        decl_parts.append(f"({arr} : List Int)")
    if string_idents:
        decl_parts.append("(" + " ".join(string_idents) + " : String)")
    params_decl = " ".join(decl_parts)

    requires_lean = req.lean_expr
    ensures_lean = ens.lean_expr

    def_params = [i for i in idents if i != "result"]
    def_decl = ""
    h_body_param = ""
    result_name = _atom_result_name(atom.name)
    use_body_semantics = (
        body_tr is not None
        and not body_tr.is_partial
        and bool(body_tr.lean_expr.strip())
        and not contains_identifier(atom.body_expr, "result")
        and not body_tr.array_identifiers
        and not body_tr.string_identifiers
        and not array_idents
        and not string_idents
    )
    if use_body_semantics:
        def_params_decl = f" ({' '.join(def_params)} : Int)" if def_params else ""
        def_decl = (
            f"def {result_name}{def_params_decl} : Int :=\n"
            f"  {body_tr.lean_expr}\n\n"
        )
        result_args = f" {' '.join(def_params)}" if def_params else ""
        h_body_param = f" (h_body : result = {result_name}{result_args})"

    # Default tactic body: try ``mumei_arith`` (mathlib4-backed
    # ``omega`` / ``linarith`` / ``norm_num`` / ``simp`` cascade) on
    # every subgoal, then ``sorry`` whatever it could not close. When
    # ``mumei_arith`` discharges the obligation the ``sorry`` is
    # unreachable and ``lake build`` emits no warning, so
    # ``scripts/export_cert.py`` records the atom as ``lean_verified``.
    if use_body_semantics:
        body = f"  rw [h_body]\n  unfold {result_name}\n  mumei_arith_deep <;> sorry"
    else:
        body = "  mumei_arith <;> sorry"
    notes: List[str] = []
    if req.is_partial or ens.is_partial:
        notes.append(
            "  -- TODO: unproven — translator could not fully encode the contract; "
            "MumeiLean.unproven marks unfinished obligations."
        )
    if body_tr is not None and not use_body_semantics:
        notes.append("  -- body semantics unsupported; using contract-only fallback")
    if req.is_trivial:
        notes.append("  -- requires is trivially true")

    note_block = "\n".join(notes)
    if note_block:
        note_block += "\n"

    decl = (
        def_decl +
        f"/-- Auto-generated from mumei atom `{atom.name}` "
        f"(z3_check_result={atom.z3_check_result}). -/\n"
        f"theorem {atom.name}_correct {params_decl}{h_body_param} :\n"
        f"    ({requires_lean}) → ({ensures_lean}) := by\n"
        f"{note_block}{body}\n"
    )
    return decl


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
        "Lean theorem statements with `sorry` placeholders for the proof\n"
        "body.\n"
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
        help="Path to a mumei ProofCertificate (.proof-cert.json) or "
        "ProofBundle (std-proof-bundle.json).",
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
