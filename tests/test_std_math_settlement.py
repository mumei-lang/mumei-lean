"""Tests for the ``MumeiLean.StdMathSettlement`` proof library."""
from __future__ import annotations

import os
import shutil
import subprocess
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parent.parent
STD_MATH_SETTLEMENT_LEAN = REPO_ROOT / "MumeiLean" / "StdMathSettlement.lean"


def _lake_env() -> dict[str, str]:
    env = os.environ.copy()
    elan_bin = Path.home() / ".elan" / "bin"
    env["PATH"] = f"{elan_bin}:{env.get('PATH', '')}"
    return env


def _have_lake() -> bool:
    return shutil.which("lake", path=_lake_env()["PATH"]) is not None


def test_std_math_settlement_declares_expected_patterns():
    src = STD_MATH_SETTLEMENT_LEAN.read_text()
    for declaration in (
        "theorem safe_add_bounded",
        "theorem conservation_law",
        "theorem monotone_transfer",
    ):
        assert declaration in src
    assert "omega" in src
    assert "sorry" not in src


@pytest.mark.skipif(not _have_lake(),
                    reason="lake not on PATH; skipping live Lean build")
@pytest.mark.skipif(os.environ.get("MUMEI_LEAN_SKIP_LIVE") == "1",
                    reason="MUMEI_LEAN_SKIP_LIVE=1 set")
def test_std_math_settlement_builds_without_sorry_warnings():
    proc = subprocess.run(
        ["lake", "build", "MumeiLean.StdMathSettlement"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        timeout=600,
        env=_lake_env(),
    )
    combined = f"{proc.stdout}\n{proc.stderr}"
    assert proc.returncode == 0, (
        f"lake build MumeiLean.StdMathSettlement exited {proc.returncode}\n{combined}"
    )
    assert "declaration uses 'sorry'" not in combined
    assert "declaration uses sorry" not in combined
