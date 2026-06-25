"""Live subprocess E2E coverage for ``scripts/bridge.py`` Lean exports."""
from __future__ import annotations

import json
import os
import shutil
import subprocess
import sys
from pathlib import Path

import pytest


REPO_ROOT = Path(__file__).resolve().parents[1]
FIXTURES = Path(__file__).resolve().parent / "fixtures"
BRIDGE = REPO_ROOT / "scripts" / "bridge.py"
GENERATED_ABS = REPO_ROOT / "generated" / "Generated" / "Std" / "Math" / "Abs.lean"


def _bridge_env() -> dict[str, str]:
    env = os.environ.copy()
    elan_bin = Path.home() / ".elan" / "bin"
    env["PATH"] = f"{elan_bin}:{env.get('PATH', '')}"
    return env


def _without_lake_env() -> dict[str, str]:
    env = os.environ.copy()
    paths = [
        path
        for path in env.get("PATH", "").split(os.pathsep)
        if path and shutil.which("lake", path=path) is None
    ]
    env["PATH"] = os.pathsep.join(paths) or "/usr/bin:/bin"
    return env


def _run_bridge(
    *args: str,
    env: dict[str, str] | None = None,
) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(BRIDGE), *args],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        env=env or _bridge_env(),
        check=False,
    )


def _assert_bridge_ok(proc: subprocess.CompletedProcess[str]) -> None:
    assert proc.returncode == 0, (
        f"bridge exited {proc.returncode}\n"
        f"stdout:\n{proc.stdout}\n"
        f"stderr:\n{proc.stderr}"
    )


def _cleanup_generated_abs() -> None:
    GENERATED_ABS.unlink(missing_ok=True)
    current = GENERATED_ABS.parent
    generated_root = REPO_ROOT / "generated" / "Generated"
    while current != generated_root and current.exists():
        try:
            current.rmdir()
        except OSError:
            break
        current = current.parent


@pytest.mark.lake_available
def test_lean_fallback_upgrades_unknown_to_lean_verified(lake_available, tmp_path: Path):
    src = (REPO_ROOT / "MumeiLean" / "StdMathAbs.lean").read_text()
    assert "theorem abs_saturating_correct" in src

    out_cert = tmp_path / "abs_saturating.lean-cert.json"
    out_dir = REPO_ROOT / "generated"
    summary = tmp_path / "summary.json"
    _cleanup_generated_abs()
    try:
        proc = _run_bridge(
            "--cert",
            str(FIXTURES / "abs_saturating.proof-cert.json"),
            "--out-dir",
            str(out_dir),
            "--lean-cert-out",
            str(out_cert),
            "--summary-json",
            str(summary),
        )

        _assert_bridge_ok(proc)
        assert GENERATED_ABS.exists()
        generated_src = GENERATED_ABS.read_text()
        assert "namespace Generated.Std.Math.Abs" in generated_src
        assert "theorem abs_saturating_correct" in generated_src
        payload = json.loads(out_cert.read_text())
        assert payload["atoms"][0]["z3_check_result"] == "lean_verified"
        assert payload["atoms"][0]["lean_metadata"]["proof_path"].endswith(
            "generated/Generated/Std/Math/Abs.lean"
        )
        assert payload["atoms"][0]["lean_metadata"]["known_witness_used"] is False
        assert payload["atoms"][0]["lean_metadata"]["lean_module"] == "Generated.Std.Math.Abs"
        assert (
            payload["atoms"][0]["lean_metadata"]["lean_theorem_name"]
            == "Generated.Std.Math.Abs.abs_saturating_correct"
        )
        assert payload["all_verified"] is True
        summary_payload = json.loads(summary.read_text())
        assert summary_payload["lean_fallback"]["proved"] >= 1
        assert summary_payload["details"][0]["lean_fallback"]["proved"] >= 1
        assert summary_payload["metrics"]["lean_successes"] > 0
        assert (
            summary_payload["metrics"]["by_atom"]["abs_saturating"]["status"]
            == "lean_verified"
        )
        assert (
            summary_payload["metrics"]["by_atom"]["abs_saturating"]["known_witness_used"]
            is False
        )
    finally:
        _cleanup_generated_abs()


def test_bridge_no_build_dry_run(tmp_path: Path):
    out_cert = tmp_path / "abs_saturating.no-build.lean-cert.json"
    proc = _run_bridge(
        "--cert",
        str(FIXTURES / "abs_saturating.proof-cert.json"),
        "--out-dir",
        str(tmp_path / "generated"),
        "--lean-cert-out",
        str(out_cert),
        "--no-build",
        env=_without_lake_env(),
    )

    _assert_bridge_ok(proc)
    payload = json.loads(out_cert.read_text())
    atom = payload["atoms"][0]
    metadata = atom["lean_result_metadata"]
    assert atom["z3_check_result"] != "lean_verified"
    assert metadata["status"] == "manual_lemma_required"
    assert metadata["z3_result_class"] == "unknown"
    assert metadata["translator_ir"]["sort"] == "contract_obligation"
    assert metadata["logic_fragment_tags"] == []
    assert metadata["manual_lemma_reason"] is None
    assert metadata["translator_version"] == "mumei-lean-translator-ir-v1"
    assert (
        metadata["bridge_lemma_hash"]
        == "a8fd0b115fd29a6e87190bd041dbd5ab7a09ec89af6ac5b10ef152a1a0c0f643"
    )
    assert payload["all_verified"] is False


def test_bridge_scan_unknown(tmp_path: Path):
    scan_root = tmp_path / "fixtures"
    certs_dir = scan_root / "std" / "certs"
    certs_dir.mkdir(parents=True)
    (certs_dir / "math.json").write_text(
        (FIXTURES / "abs_saturating.proof-cert.json").read_text()
    )
    summary = tmp_path / "summary.json"

    proc = _run_bridge(
        "--scan-unknown",
        str(scan_root),
        "--out-dir",
        str(tmp_path / "generated"),
        "--summary-json",
        str(summary),
        "--no-build",
        "--no-export",
        env=_without_lake_env(),
    )

    _assert_bridge_ok(proc)
    payload = json.loads(summary.read_text())
    assert payload["total_unknown"] >= 1


@pytest.mark.lake_available
def test_bridge_escalation_bundle(lake_available, tmp_path: Path):
    out_cert = tmp_path / "abs_saturating.escalation.lean-cert.json"
    _cleanup_generated_abs()
    try:
        proc = _run_bridge(
            "--escalation-bundle",
            str(FIXTURES / "abs_saturating.escalation-bundle.json"),
            "--lean-cert-out",
            str(out_cert),
        )

        _assert_bridge_ok(proc)
        payload = json.loads(out_cert.read_text())
        candidate = payload["candidates"][0]
        assert candidate["name"] == "abs_saturating"
        assert candidate["z3_check_result"] == "lean_verified"
        assert candidate["lean_metadata"]["known_witness_used"] is False
    finally:
        _cleanup_generated_abs()
