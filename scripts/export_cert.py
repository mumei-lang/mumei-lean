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
_FILE_PREFIX_RE = re.compile(r"^([^\s:]+\.lean):\d+:\d+:")
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


def _failed_theorem_attributions(
    build_output: str,
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
        file_match = _FILE_PREFIX_RE.match(line)
        file_path: Optional[str] = file_match.group(1) if file_match else None
        attribution: Optional[str] = None
        attribution_from_def = False
        for j in range(idx, max(-1, idx - 12), -1):
            if file_path is None:
                fm = _FILE_PREFIX_RE.match(lines[j])
                if fm:
                    file_path = fm.group(1)
            m = re.search(r"theorem\s+([A-Za-z_][A-Za-z0-9_]*)", lines[j])
            if m:
                attribution = m.group(1)
                break
            dm = _DEF_RESULT_RE.search(lines[j])
            if dm:
                # Errors inside a body-semantics ``def`` block belong
                # to the atom named by the camelCase prefix of the
                # ``def``'s identifier (without the ``Result`` suffix).
                # ``_camel_to_snake`` already returns the originating
                # atom name verbatim, so we mark this attribution as
                # "from def" to skip the ``_correct`` suffix stripping
                # that only applies to ``theorem <atom>_correct`` names.
                attribution = _camel_to_snake(dm.group(1))
                attribution_from_def = True
                break
        if not attribution:
            continue
        if not attribution_from_def and attribution.endswith("_correct"):
            name = attribution[: -len("_correct")]
        else:
            name = attribution
        key = (file_path, name)
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


def _has_unattributable_failures(build_output: str) -> bool:
    """Return True iff ``build_output`` contains an ``error:`` /
    ``sorry`` diagnostic that cannot be attributed to a specific
    theorem.

    File-level errors (e.g. a failing ``import MumeiLean`` at the top
    of a generated file) appear before any ``theorem`` declaration, so
    the backward-walk in :func:`_failed_theorem_names` cannot pin them
    to an atom. Callers should treat *all* lifted atoms in the affected
    build as failed when this returns ``True`` to avoid silently
    marking them ``lean_verified``.
    """
    lines = build_output.splitlines()
    for idx, line in enumerate(lines):
        if not (_SORRY_RE.search(line) or _ERROR_RE.search(line)):
            continue
        attributed = False
        for j in range(idx, max(-1, idx - 12), -1):
            if re.search(r"theorem\s+([A-Za-z_][A-Za-z0-9_]*)", lines[j]):
                attributed = True
                break
            if _DEF_RESULT_RE.search(lines[j]):
                attributed = True
                break
        if not attributed:
            return True
    return False


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
    return name not in failed


def _upgrade_single_certificate(
    cert: dict,
    proved_set: set,
    failed_set: set,
) -> bool:
    """Mutate a single per-module certificate in place.

    Returns ``True`` iff at least one atom was upgraded.
    """
    upgraded_any = False
    for atom in cert.get("atoms", []):
        if not isinstance(atom, dict):
            continue
        if not _atom_proved(atom, failed_set, proved_set):
            continue
        atom["z3_check_result"] = LEAN_VERIFIED
        atom["status"] = "verified"
        upgraded_any = True

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
                _upgrade_single_certificate(nested, proved_set, failed_set)
    else:
        _upgrade_single_certificate(out, proved_set, failed_set)

    out["lean_version"] = lean_version
    out["lean_cert_schema_version"] = LEAN_CERT_SCHEMA_VERSION
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
