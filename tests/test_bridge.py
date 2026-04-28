"""Tests for ``scripts.bridge``."""
from __future__ import annotations

import json
from pathlib import Path

from bridge import _scan_unknown_certs, main


def _atom(name: str, z3: str = "unknown") -> dict:
    return {
        "name": name,
        "requires": "x > 0",
        "ensures": "result >= x",
        "z3_check_result": z3,
        "status": "unknown" if z3 == "unknown" else "verified",
        "content_hash": "h",
        "proof_hash": "p",
        "dependencies": [],
        "effects": [],
    }


def _cert(file: str, atoms: list) -> dict:
    return {
        "version": "1.0",
        "timestamp": "2026-04-28T00:00:00Z",
        "mumei_version": "0.5.6",
        "z3_version": "4.12.2",
        "file": file,
        "atoms": atoms,
        "package_name": "x",
        "package_version": "0",
        "certificate_hash": "",
        "all_verified": False,
    }


def test_scan_unknown_certs_finds_only_unknown(tmp_path: Path):
    certs_dir = tmp_path / "std" / "certs"
    certs_dir.mkdir(parents=True)
    (certs_dir / "ok.json").write_text(
        json.dumps(_cert("std/ok.mm", [_atom("a", z3="unsat")]))
    )
    (certs_dir / "todo.json").write_text(
        json.dumps(_cert("std/todo.mm", [_atom("b", z3="unknown")]))
    )
    found = _scan_unknown_certs(certs_dir)
    assert [p.name for p, _ in found] == ["todo.json"]


def test_main_dry_run_writes_generated_files(tmp_path: Path):
    cert_path = tmp_path / "cert.json"
    cert_path.write_text(
        json.dumps(_cert("std/math.mm", [_atom("inc", z3="unknown")]))
    )
    out_dir = tmp_path / "generated"
    rc = main(
        [
            "--cert", str(cert_path),
            "--out-dir", str(out_dir),
            "--module-prefix", "Gen",
            "--no-build",
        ]
    )
    assert rc == 0
    assert (out_dir / "Gen" / "Std" / "Math.lean").exists()


def test_main_scan_unknown_returns_zero_when_dir_empty(tmp_path: Path):
    rc = main(
        [
            "--scan-unknown", str(tmp_path),
            "--out-dir", str(tmp_path / "g"),
            "--no-build",
            "--no-export",
        ]
    )
    assert rc == 0
