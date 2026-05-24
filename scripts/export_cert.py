"""Emit a mumei-compatible ``.lean-cert.json`` from a Lean build run.

This script is the *export* side of the mumei ↔ mumei-lean bridge. It
consumes:

* a copy of the original mumei ``.proof-cert.json`` (so we can preserve
  ``content_hash``, ``proof_hash``, ``dependencies``, ``effects``,
  ``requires``, and ``ensures`` for every atom), and
* the textual output of ``lake build`` plus the list of theorem names
  emitted by ``ingest_cert.py``.

It produces a JSON file matching the mumei ``ProofCertificate`` schema
(see ``mumei-lang/mumei`` ``mumei-core/src/proof_cert.rs``) where:

* atoms whose Lean theorem proved cleanly get ``z3_check_result =
  "lean_verified"`` and ``status = "verified"``;
* atoms that still fail get the original mumei record passed through
  unchanged;
* a top-level ``lean_version`` field is added alongside the existing
  ``mumei_version`` to record the Lean toolchain used.

The mumei resolver (``resolver.rs::verify_import_certificate``)
currently treats anything other than ``"unsat"`` as unproven, so the
new ``"lean_verified"`` value is forward-compatible: future mumei
versions can opt in to recognising it without breaking older ones.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any, Dict, Iterable, List, Optional, Tuple

LEAN_CERT_SCHEMA_VERSION = "1.0-lean"
LEAN_VERIFIED = "lean_verified"
TRANSLATOR_VERSION = "mumei-lean-translator-ir-v1"
BRIDGE_LEMMA_HASH = "d8d270d6429a3e31c608dc109876df4ec99ee1243796430775a5b0ef18b5ac24"
MANUAL_LEMMA_REQUIRED = "manual_lemma_required"

# Lake's ``sorry`` warning lines look like::
#   warning: declaration uses 'sorry'
# preceded by a header line that names the file/decl. We treat *any*
# such warning as a hard failure for the corresponding theorem.
_SORRY_RE = re.compile(r"declaration uses 'sorry'")
# Lake compile-error diagnostics look like::
#   Generated/Foo.lean:42:7: error: <message>
# Any ``error:`` diagnostic in a generated theorem is treated as a
# failure for that theorem (the proof did not type-check).
_ERROR_RE = re.compile(r":\s*error:\s")
# Lake prefixes every diagnostic line with the originating source
# file, e.g. ``Generated/Std/Math.lean:12:0: warning: ...``.
_FILE_PREFIX_RE = re.compile(r"(?:^|\s)([^\s:]+\.lean):(\d+):(\d+):")
# Body-semantics ``def <atom>Result`` blocks emitted by
# ``ingest_cert.render_theorem`` precede their owning ``theorem``. When
# Lean reports an error inside the ``def`` (e.g. a type mismatch in the
# translated body), the backward walk needs to recognise it so the
# failure can be attributed to the originating atom rather than
# triggering the unattributable-failure fallback.
_DEF_RESULT_RE = re.compile(r"\bdef\s+([A-Za-z_][A-Za-z0-9_]*)Result\b")


def _camel_to_snake(name: str) -> str:
    """Convert ``absSaturatingAuto`` back to ``abs_saturating_auto``.

    Mirrors ``ingest_cert._atom_result_name``'s snake_case → camelCase
    transform so we can attribute errors emitted inside a generated
    ``def <atom>Result`` block to the originating atom name.
    """
    return re.sub(r"(?<!^)(?=[A-Z])", "_", name).lower()


def _diagnostic_location(line: str) -> Tuple[Optional[str], Optional[int]]:
    match = _FILE_PREFIX_RE.search(line)
    if match is None:
        return None, None
    return match.group(1), int(match.group(2))


def _name_from_attribution(raw_name: str, from_def: bool) -> str:
    if from_def:
        return _camel_to_snake(raw_name)
    if raw_name.endswith("_correct"):
        return raw_name[: -len("_correct")]
    return raw_name


def _attribution_in_text(lines: List[str], start_idx: int) -> Optional[str]:
    for j in range(start_idx, max(-1, start_idx - 40), -1):
        theorem = re.search(r"theorem\s+([A-Za-z_][A-Za-z0-9_]*)", lines[j])
        if theorem:
            return _name_from_attribution(theorem.group(1), from_def=False)
        result_def = _DEF_RESULT_RE.search(lines[j])
        if result_def:
            return _name_from_attribution(result_def.group(1), from_def=True)
    return None


def _source_path_candidates(
    file_path: str,
    source_root: Optional[Path],
) -> List[Path]:
    raw = Path(file_path)
    candidates: List[Path] = []
    if source_root is not None and not raw.is_absolute():
        candidates.append(source_root / raw)
    candidates.append(raw)
    normalised = Path(file_path.replace("./", ""))
    if normalised != raw:
        if source_root is not None and not normalised.is_absolute():
            candidates.append(source_root / normalised)
        candidates.append(normalised)
    return candidates


def _source_attribution(
    file_path: Optional[str],
    line_no: Optional[int],
    source_root: Optional[Path],
) -> Optional[str]:
    if file_path is None or line_no is None:
        return None
    for candidate in _source_path_candidates(file_path, source_root):
        if not candidate.exists():
            continue
        source_lines = candidate.read_text().splitlines()
        if not source_lines:
            return None
        start_idx = min(max(line_no - 1, 0), len(source_lines) - 1)
        return _attribution_in_text(source_lines, start_idx)
    return None


def _diagnostic_attribution(
    lines: List[str],
    idx: int,
    source_root: Optional[Path],
) -> Tuple[Optional[str], Optional[str]]:
    file_path, line_no = _diagnostic_location(lines[idx])
    source_name = _source_attribution(file_path, line_no, source_root)
    if source_name is not None:
        return file_path, source_name

    log_name = _attribution_in_text(lines, idx)
    if log_name is not None:
        for j in range(idx, max(-1, idx - 40), -1):
            if file_path is None:
                file_path, _line_no = _diagnostic_location(lines[j])
            if file_path is not None:
                break
        return file_path, log_name
    return file_path, None


def _failed_theorem_attributions(
    build_output: str,
    source_root: Optional[Path] = None,
) -> List[Tuple[Optional[str], str]]:
    """Return ``(file_path, theorem_name)`` for every attributable failure.

    ``file_path`` is the Lake diagnostic file (relative to the repo
    root) when present, otherwise ``None``. ``theorem_name`` is the
    de-suffixed atom name (i.e. ``inc`` for ``theorem inc_correct``).
    Use this when callers need to disambiguate same-named atoms across
    multiple input certificates by their originating Lean source file.
    """
    failures: List[Tuple[Optional[str], str]] = []
    seen: set = set()
    lines = build_output.splitlines()
    for idx, line in enumerate(lines):
        if not (_SORRY_RE.search(line) or _ERROR_RE.search(line)):
            continue
        file_path, attribution = _diagnostic_attribution(lines, idx, source_root)
        if attribution is None:
            continue
        key = (file_path, attribution)
        if key in seen:
            continue
        seen.add(key)
        failures.append(key)
    return failures


def _failed_theorem_names(build_output: str) -> List[str]:
    """Extract theorem names that failed to prove cleanly.

    Two failure modes are recognised:

    * ``warning: declaration uses 'sorry'`` — the proof body still
      contains ``sorry``;
    * ``error: ...`` — the generated theorem did not type-check
      (e.g. because the contract translator emitted a partial /
      unsupported expression).

    For each failure line we walk backwards a few lines to find the
    most recent ``theorem <name>`` reference and attribute the failure
    to that atom. This keeps `lake build` exit-code information out of
    the picture: even when ``rc == 0`` (e.g. errors were demoted to
    warnings), any unproven theorem we can attribute is recorded.

    Multi-payload callers that need to disambiguate same-named atoms
    across different generated source files should use
    :func:`_failed_theorem_attributions` directly.
    """
    failures: List[str] = []
    for _file_path, name in _failed_theorem_attributions(build_output):
        if name not in failures:
            failures.append(name)
    return failures


def _has_unattributable_failures(
    build_output: str,
    source_root: Optional[Path] = None,
) -> bool:
    """Return True iff ``build_output`` contains an ``error:`` /
    ``sorry`` diagnostic that cannot be attributed to a specific
    theorem.

    File-level errors (e.g. a failing ``import MumeiLean`` at the top
    of a generated file) appear before any ``theorem`` declaration, so
    the attribution pass cannot pin them to an atom. Callers should
    treat *all* lifted atoms in the affected build as failed when this
    returns ``True`` to avoid silently marking them ``lean_verified``.
    """
    lines = build_output.splitlines()
    for idx, line in enumerate(lines):
        if not (_SORRY_RE.search(line) or _ERROR_RE.search(line)):
            continue
        _file_path, attribution = _diagnostic_attribution(lines, idx, source_root)
        if attribution is None:
            return True
    return False


def _translator_contract_current(atom: dict) -> bool:
    translator_version = atom.get("translator_version", TRANSLATOR_VERSION)
    bridge_lemma_hash = atom.get("bridge_lemma_hash", BRIDGE_LEMMA_HASH)
    return (
        translator_version == TRANSLATOR_VERSION
        and bridge_lemma_hash == BRIDGE_LEMMA_HASH
    )


def _atom_proved(
    atom: dict,
    failed: Iterable[str],
    proved: Iterable[str],
) -> bool:
    """Return True iff ``atom`` was successfully proved on the Lean side.

    ``proved`` lists atoms the caller knows to have been emitted as Lean
    theorems by ``ingest_cert.py``; an atom that was *not* emitted is
    left unchanged (returns False).
    """
    name = atom.get("name")
    if name not in proved:
        return False
    if not _translator_contract_current(atom):
        return False
    if atom.get("manual_lemma_reason"):
        return False
    return name not in failed


def _metadata_for_atom(
    atom: dict,
    status: str,
    atom_metadata: Optional[Dict[str, dict]],
) -> dict:
    name = str(atom.get("name", "atom"))
    metadata = dict((atom_metadata or {}).get(name, {}))
    metadata.setdefault("theorem_name", f"{name}_correct")
    metadata.setdefault("translator_version", TRANSLATOR_VERSION)
    metadata.setdefault("bridge_lemma_hash", BRIDGE_LEMMA_HASH)
    metadata.setdefault("proof_path", "")
    metadata.setdefault("diagnostics", [])
    if atom.get("manual_lemma_reason"):
        metadata.setdefault("manual_lemma_reason", atom.get("manual_lemma_reason"))
    metadata["status"] = status
    return metadata


def _upgrade_atom_list(
    atoms: Iterable[dict],
    proved_set: set,
    failed_set: set,
    atom_metadata: Optional[Dict[str, dict]],
) -> bool:
    upgraded_any = False
    for atom in atoms:
        if not isinstance(atom, dict):
            continue
        name = atom.get("name")
        proved = _atom_proved(atom, failed_set, proved_set)
        metadata = (atom_metadata or {}).get(str(name))
        if proved:
            atom["z3_check_result"] = LEAN_VERIFIED
            atom["status"] = "verified"
            atom["translator_version"] = TRANSLATOR_VERSION
            atom["bridge_lemma_hash"] = BRIDGE_LEMMA_HASH
            atom["lean_metadata"] = _metadata_for_atom(
                atom,
                LEAN_VERIFIED,
                atom_metadata,
            )
            upgraded_any = True
        elif metadata is not None:
            status = str(metadata.get("status", MANUAL_LEMMA_REQUIRED))
            if not _translator_contract_current(atom):
                status = "stale_translator"
            atom["lean_metadata"] = _metadata_for_atom(
                atom,
                status,
                atom_metadata,
            )
    return upgraded_any


def _upgrade_single_certificate(
    cert: dict,
    proved_set: set,
    failed_set: set,
    atom_metadata: Optional[Dict[str, dict]] = None,
) -> bool:
    """Mutate a single per-module certificate in place.

    Returns ``True`` iff at least one atom was upgraded.
    """
    upgraded_any = _upgrade_atom_list(
        cert.get("atoms", []),
        proved_set,
        failed_set,
        atom_metadata,
    )

    if upgraded_any:
        # The mumei certificate_hash is computed over the canonical
        # serialisation; once we mutate atoms it is no longer valid,
        # and the upstream resolver only checks per-atom content
        # hashes, so we drop it explicitly to avoid stale metadata.
        cert.pop("certificate_hash", None)
        # ``all_verified`` flips to true iff every atom is now either
        # ``unsat`` or ``lean_verified`` (and at least one atom exists).
        atoms = cert.get("atoms", [])
        if atoms:
            cert["all_verified"] = all(
                a.get("z3_check_result") in {"unsat", LEAN_VERIFIED}
                for a in atoms
                if isinstance(a, dict)
            )
    return upgraded_any


def upgrade_certificate(
    cert: dict,
    proved_atoms: Iterable[str],
    failed_atoms: Iterable[str],
    lean_version: str,
    atom_metadata: Optional[Dict[str, dict]] = None,
    harness_contract: Optional[Dict[str, Any]] = None,
) -> dict:
    """Return a new certificate dict with successful Lean proofs marked.

    The input ``cert`` is *not* mutated. Atoms whose proof succeeded
    have their ``z3_check_result`` set to ``"lean_verified"`` and
    ``status`` set to ``"verified"``; everything else is preserved
    verbatim.

    Both per-module ``ProofCertificate`` and ``ProofBundle`` envelopes
    are accepted: bundles are detected by the presence of a ``modules``
    dict, and each nested certificate is upgraded independently.
    """
    proved_set = set(proved_atoms)
    failed_set = set(failed_atoms)
    out = json.loads(json.dumps(cert))  # deep copy via JSON round-trip

    if isinstance(out.get("modules"), dict):
        # ProofBundle: recurse into each per-module certificate.
        for nested in out["modules"].values():
            if isinstance(nested, dict):
                _upgrade_single_certificate(
                    nested,
                    proved_set,
                    failed_set,
                    atom_metadata,
                )
    elif isinstance(out.get("candidates"), list):
        if _upgrade_atom_list(
            out["candidates"],
            proved_set,
            failed_set,
            atom_metadata,
        ):
            out.setdefault("summary", {})["lean_verified"] = len(proved_set - failed_set)
    else:
        _upgrade_single_certificate(out, proved_set, failed_set, atom_metadata)

    out["lean_version"] = lean_version
    out["lean_cert_schema_version"] = LEAN_CERT_SCHEMA_VERSION
    if harness_contract is not None:
        out["harness_contract"] = harness_contract
    return out


def _read_text_or_die(path: Path) -> str:
    if not path.exists():
        print(f"error: file does not exist: {path}", file=sys.stderr)
        raise SystemExit(2)
    return path.read_text()


def main(argv: Optional[List[str]] = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Emit a mumei-compatible .lean-cert.json from a lake build run."
        ),
    )
    parser.add_argument(
        "--input-cert",
        type=Path,
        required=True,
        help="Path to the original mumei .proof-cert.json this run is "
        "augmenting.",
    )
    parser.add_argument(
        "--build-log",
        type=Path,
        required=True,
        help="Path to a captured `lake build` stdout/stderr log.",
    )
    parser.add_argument(
        "--proved-atoms",
        type=Path,
        required=True,
        help="Path to a newline-delimited file of atom names that were "
        "emitted as Lean theorems by ingest_cert.py.",
    )
    parser.add_argument(
        "--lean-version",
        default="unknown",
        help="Lean toolchain version string to embed in the output.",
    )
    parser.add_argument(
        "--out",
        type=Path,
        required=True,
        help="Where to write the resulting .lean-cert.json.",
    )
    args = parser.parse_args(argv)

    cert: Dict[str, Any] = json.loads(_read_text_or_die(args.input_cert))
    build_log = _read_text_or_die(args.build_log)
    proved = [
        line.strip() for line in args.proved_atoms.read_text().splitlines()
        if line.strip()
    ]
    failed = _failed_theorem_names(build_log)
    if _has_unattributable_failures(build_log):
        # File-level failures (e.g. a failing ``import``) cannot be
        # attributed to a specific theorem; fall back to marking every
        # lifted atom as failed so we never emit a false
        # ``lean_verified`` certification.
        print(
            "warning: build log contains failures that could not be "
            "attributed to a specific theorem; treating all lifted "
            "atoms as failed.",
            file=sys.stderr,
        )
        failed = list({*failed, *proved})

    upgraded = upgrade_certificate(
        cert=cert,
        proved_atoms=proved,
        failed_atoms=failed,
        lean_version=args.lean_version,
    )

    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(upgraded, indent=2, ensure_ascii=False) + "\n")
    print(f"wrote {args.out} ({len(upgraded.get('atoms', []))} atoms; "
          f"{sum(1 for a in upgraded.get('atoms', []) if a.get('z3_check_result') == LEAN_VERIFIED)} "
          f"lean_verified, {len(failed)} failed)")
    return 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
