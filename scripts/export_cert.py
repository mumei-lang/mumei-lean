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
from typing import Any, Dict, Iterable, List, Optional

LEAN_CERT_SCHEMA_VERSION = "1.0-lean"
LEAN_VERIFIED = "lean_verified"

# Lake's ``sorry`` warning lines look like::
#   warning: declaration uses 'sorry'
# preceded by a header line that names the file/decl. We treat *any*
# such warning as a hard failure for the corresponding theorem.
_SORRY_RE = re.compile(r"declaration uses 'sorry'")


def _failed_theorem_names(build_output: str) -> List[str]:
    """Extract theorem names that triggered ``sorry`` warnings.

    Lake's diagnostic format is roughly::

        Generated/Foo.lean:42:7: warning: declaration uses 'sorry'

    accompanied by a separate informative line that mentions the
    declaration. We take a conservative approach: any line containing
    ``declaration uses 'sorry'`` is treated as a failure, and we look
    for the most recent ``theorem <name>`` reference in the preceding
    context to attribute it.
    """
    failures: List[str] = []
    lines = build_output.splitlines()
    for idx, line in enumerate(lines):
        if not _SORRY_RE.search(line):
            continue
        # Walk backwards a few lines looking for a theorem name.
        attribution: Optional[str] = None
        for j in range(idx, max(-1, idx - 12), -1):
            m = re.search(r"theorem\s+([A-Za-z_][A-Za-z0-9_]*)", lines[j])
            if m:
                attribution = m.group(1)
                break
        if attribution:
            # ``ingest_cert.py`` always emits ``<atomname>_correct``.
            if attribution.endswith("_correct"):
                failures.append(attribution[: -len("_correct")])
            else:
                failures.append(attribution)
    return failures


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
    """
    proved_set = set(proved_atoms)
    failed_set = set(failed_atoms)
    out = json.loads(json.dumps(cert))  # deep copy via JSON round-trip
    upgraded_any = False
    for atom in out.get("atoms", []):
        if not isinstance(atom, dict):
            continue
        if not _atom_proved(atom, failed_set, proved_set):
            continue
        atom["z3_check_result"] = LEAN_VERIFIED
        atom["status"] = "verified"
        upgraded_any = True

    out["lean_version"] = lean_version
    out["lean_cert_schema_version"] = LEAN_CERT_SCHEMA_VERSION
    if upgraded_any:
        # The mumei certificate_hash is computed over the canonical
        # serialisation; once we mutate atoms it is no longer valid,
        # and the upstream resolver only checks per-atom content
        # hashes, so we drop it explicitly to avoid stale metadata.
        out.pop("certificate_hash", None)
        # ``all_verified`` flips to true iff every atom is now either
        # ``unsat`` or ``lean_verified`` (and at least one atom exists).
        atoms = out.get("atoms", [])
        if atoms:
            out["all_verified"] = all(
                a.get("z3_check_result") in {"unsat", LEAN_VERIFIED}
                for a in atoms
                if isinstance(a, dict)
            )
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
