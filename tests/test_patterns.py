"""Tests for the reusable ``MumeiLean.Patterns`` proof library."""
from __future__ import annotations

import os
import shutil
import subprocess
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parent.parent
PATTERNS_LEAN = REPO_ROOT / "MumeiLean" / "Patterns.lean"


def _lake_env() -> dict[str, str]:
    env = os.environ.copy()
    elan_bin = Path.home() / ".elan" / "bin"
    env["PATH"] = f"{elan_bin}:{env.get('PATH', '')}"
    return env


def _have_lake() -> bool:
    return shutil.which("lake", path=_lake_env()["PATH"]) is not None


def test_patterns_lean_declares_expected_library():
    src = PATTERNS_LEAN.read_text()
    for declaration in (
        "theorem add_bounded",
        "theorem repeated_add_bounded",
        "theorem transfer_preserves_sum",
        "theorem list_transfer_preserves_sum",
        "theorem monotone_comp",
        "theorem counter_monotone",
    ):
        assert declaration in src
    assert "List.set" in src or ".set" in src
    assert ".sum" in src
    assert "by sorry" not in src
    assert "by\n  sorry" not in src


@pytest.mark.skipif(not _have_lake(),
                    reason="lake not on PATH; skipping live Lean build")
@pytest.mark.skipif(os.environ.get("MUMEI_LEAN_SKIP_LIVE") == "1",
                    reason="MUMEI_LEAN_SKIP_LIVE=1 set")
def test_patterns_lean_builds_without_sorry_warnings():
    proc = subprocess.run(
        ["lake", "build", "MumeiLean.Patterns"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        timeout=600,
        env=_lake_env(),
    )
    combined = f"{proc.stdout}\n{proc.stderr}"
    assert proc.returncode == 0, (
        f"lake build MumeiLean.Patterns exited {proc.returncode}\n{combined}"
    )
    assert "declaration uses 'sorry'" not in combined
    assert "declaration uses sorry" not in combined
