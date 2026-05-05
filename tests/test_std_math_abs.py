"""Tests for real std-library Lean proof witnesses."""
from __future__ import annotations

import os
import shutil
import subprocess
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parent.parent
STD_MATH_ABS_LEAN = REPO_ROOT / "MumeiLean" / "StdMathAbs.lean"


def _lake_env() -> dict[str, str]:
    env = os.environ.copy()
    elan_bin = Path.home() / ".elan" / "bin"
    env["PATH"] = f"{elan_bin}:{env.get('PATH', '')}"
    return env


def _have_lake() -> bool:
    return shutil.which("lake", path=_lake_env()["PATH"]) is not None


def test_std_math_abs_declares_expected_proofs():
    src = STD_MATH_ABS_LEAN.read_text()
    for declaration in (
        "theorem abs_saturating_correct",
        "theorem fixed_point_abs_correct",
        "theorem fixed_point_from_int_correct",
        "theorem list_length_correct",
    ):
        assert declaration in src
    assert "std/math/abs.mm::abs_saturating" in src
    assert "std/list.mm::list_length" in src
    assert "omega" in src
    assert "norm_num" in src
    assert "by sorry" not in src
    assert "by\n  sorry" not in src


@pytest.mark.skipif(not _have_lake(),
                    reason="lake not on PATH; skipping live Lean build")
@pytest.mark.skipif(os.environ.get("MUMEI_LEAN_SKIP_LIVE") == "1",
                    reason="MUMEI_LEAN_SKIP_LIVE=1 set")
def test_std_math_abs_lean_builds_without_sorry_warnings():
    proc = subprocess.run(
        ["lake", "build", "MumeiLean.StdMathAbs"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        timeout=600,
        env=_lake_env(),
    )
    combined = f"{proc.stdout}\n{proc.stderr}"
    assert proc.returncode == 0, (
        f"lake build MumeiLean.StdMathAbs exited {proc.returncode}\n{combined}"
    )
    assert "declaration uses 'sorry'" not in combined
    assert "declaration uses sorry" not in combined
