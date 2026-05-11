"""Bridge integration smoke tests for reusable proof-pattern certificates."""
from __future__ import annotations

import json
from pathlib import Path

import bridge
from bridge import main


def _pattern_cert() -> dict:
    return {
        "version": "1.0",
        "timestamp": "2026-05-11T00:00:00Z",
        "mumei_version": "0.5.6",
        "z3_version": "4.12.2",
        "file": "std/math/patterns.mm",
        "atoms": [
            {
                "name": "clamp_preserves_order",
                "requires": "min_val <= max_val",
                "ensures": "result >= min_val && result <= max_val",
                "body_expr": "if x < min_val { min_val } else { if x > max_val { max_val } else { x } }",
                "z3_check_result": "unknown",
                "status": "unknown",
                "content_hash": "h-clamp",
                "proof_hash": "p-clamp",
                "dependencies": [],
                "effects": [],
            },
            {
                "name": "bounded_mul_with_overflow_check",
                "requires": "a >= 0 && b >= 0 && a * b <= limit",
                "ensures": "result == a * b && result <= limit",
                "body_expr": "a * b",
                "z3_check_result": "unknown",
                "status": "unknown",
                "content_hash": "h-mul",
                "proof_hash": "p-mul",
                "dependencies": [],
                "effects": [],
            },
        ],
        "package_name": "std-math-patterns",
        "package_version": "0",
        "certificate_hash": "",
        "all_verified": False,
    }


def test_patterns_bridge_generates_lean_sources_and_export_path(tmp_path: Path) -> None:
    cert_path = tmp_path / "patterns.proof.json"
    cert_path.write_text(json.dumps(_pattern_cert()))
    out_dir = tmp_path / "generated"
    lean_cert = tmp_path / "patterns.lean-cert.json"

    rc = main(
        [
            "--cert",
            str(cert_path),
            "--out-dir",
            str(out_dir),
            "--module-prefix",
            "Generated",
            "--lean-cert-out",
            str(lean_cert),
            "--no-build",
        ]
    )

    assert rc == 0
    generated = out_dir / "Generated" / "Std" / "Math" / "Patterns.lean"
    text = generated.read_text()
    assert "clamp_preserves_order_correct" in text
    assert "bounded_mul_with_overflow_check_correct" in text
    assert "TODO: unproven" not in text
    assert not lean_cert.exists()


def test_patterns_bridge_exports_lean_verified_certificate(
    tmp_path: Path,
    monkeypatch,
) -> None:
    def fake_lake_build(repo_dir: Path, log_path: Path) -> int:
        log_path.parent.mkdir(parents=True, exist_ok=True)
        log_path.write_text("")
        return 0

    monkeypatch.setattr(bridge, "_run_lake_build", fake_lake_build)
    cert_path = tmp_path / "patterns.proof.json"
    cert_path.write_text(json.dumps(_pattern_cert()))
    lean_cert = tmp_path / "patterns.lean-cert.json"

    rc = main(
        [
            "--cert",
            str(cert_path),
            "--out-dir",
            str(tmp_path / "generated"),
            "--module-prefix",
            "Generated",
            "--lean-cert-out",
            str(lean_cert),
        ]
    )

    assert rc == 0
    payload = json.loads(lean_cert.read_text())
    statuses = {atom["name"]: atom["z3_check_result"] for atom in payload["atoms"]}
    assert statuses["clamp_preserves_order"] == "lean_verified"
    assert statuses["bounded_mul_with_overflow_check"] == "lean_verified"
