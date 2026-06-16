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


@pytest.mark.lake_available
def test_bridge_known_witness_abs_saturating(lake_available, tmp_path: Path):
    src = (REPO_ROOT / "MumeiLean" / "StdMathAbs.lean").read_text()
    assert "theorem abs_saturating_correct" in src

    out_cert = tmp_path / "abs_saturating.lean-cert.json"
    out_dir = tmp_path / "generated"
    summary = tmp_path / "summary.json"
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
    payload = json.loads(out_cert.read_text())
    assert payload["atoms"][0]["z3_check_result"] == "lean_verified"
    assert (
        payload["atoms"][0]["lean_metadata"]["proof_path"]
        == "MumeiLean/StdMathAbs.lean"
    )
    assert payload["atoms"][0]["lean_metadata"]["known_witness_used"] is True
    assert payload["atoms"][0]["lean_metadata"]["lean_module"] == "MumeiLean.StdMathAbs"
    assert payload["all_verified"] is True
    assert not (out_dir / "Generated" / "Std" / "Math" / "Abs.lean").exists()
    summary_payload = json.loads(summary.read_text())
    assert summary_payload["lean_fallback"]["proved"] >= 1
    assert summary_payload["metrics"]["lean_successes"] > 0
    assert summary_payload["metrics"]["by_atom"]["abs_saturating"]["status"] == "lean_verified"
    assert summary_payload["metrics"]["by_atom"]["abs_saturating"]["known_witness_used"] is True


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
    assert payload["atoms"][0]["z3_check_result"] != "lean_verified"
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
