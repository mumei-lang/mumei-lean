"""Helpers for scanning bridge inputs for Lean candidates."""
from __future__ import annotations

import json
from pathlib import Path
from typing import List, Tuple

try:
    from .proofcert import Z3CheckResult
except ImportError:  # pragma: no cover - direct ``python scripts/bridge_scan.py``
    from proofcert import Z3CheckResult  # type: ignore


def _load_cert(path: Path) -> dict:
    return json.loads(path.read_text())


def _is_unknown_lean_candidate(atom: dict) -> bool:
    z3_check = atom.get("z3_check_result", "")
    escalation = atom.get("escalation_reason", "") or ""
    return (
        z3_check == Z3CheckResult.UNKNOWN.value
        or atom.get("z3_result_class") == "unknown"
        or z3_check == "spurious_candidate"
        or escalation == "spurious_candidate"
    )


def _scan_unknown_certs(std_certs_dir: Path) -> List[Tuple[Path, dict]]:
    """Return a list of ``(path, certificate_dict)`` for each per-module
    cert under ``std_certs_dir`` that contains at least one ``unknown``
    atom.
    """
    found: List[Tuple[Path, dict]] = []
    if not std_certs_dir.exists():
        return found
    for path in sorted(std_certs_dir.rglob("*.json")):
        try:
            payload = json.loads(path.read_text())
        except (OSError, json.JSONDecodeError):
            continue
        atoms = payload.get("atoms")
        if not isinstance(atoms, list):
            continue
        if any(
            isinstance(a, dict) and _is_unknown_lean_candidate(a)
            for a in atoms
        ):
            found.append((path, payload))
    return found
