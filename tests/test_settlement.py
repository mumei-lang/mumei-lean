"""Tests for the ``MumeiLean.Settlement`` RTGS proof module."""
from __future__ import annotations

import os
import shutil
import subprocess
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parent.parent
SETTLEMENT_LEAN = REPO_ROOT / "MumeiLean" / "Settlement.lean"


def _lake_env() -> dict[str, str]:
    env = os.environ.copy()
    elan_bin = Path.home() / ".elan" / "bin"
    env["PATH"] = f"{elan_bin}:{env.get('PATH', '')}"
    return env


def _have_lake() -> bool:
    return shutil.which("lake", path=_lake_env()["PATH"]) is not None


def test_settlement_lean_declares_expected_rtgs_proofs():
    src = SETTLEMENT_LEAN.read_text()
    for declaration in (
        "inductive State",
        "inductive Op",
        "def step",
        "def run",
        "theorem no_settlement_without_validate",
        "structure Transfer",
        "def apply_transfer",
        "theorem single_transfer_preserves_sum",
        "inductive TransferTrace",
        "theorem balance_conservation",
        "MumeiLean.Patterns.list_transfer_preserves_sum",
    ):
        assert declaration in src
    assert "Op.reject" in src or ".reject" in src
    assert "by sorry" not in src
    assert "by\n  sorry" not in src


@pytest.mark.skipif(not _have_lake(),
                    reason="lake not on PATH; skipping live Lean build")
@pytest.mark.skipif(os.environ.get("MUMEI_LEAN_SKIP_LIVE") == "1",
                    reason="MUMEI_LEAN_SKIP_LIVE=1 set")
def test_settlement_lean_builds_without_sorry_warnings():
    proc = subprocess.run(
        ["lake", "build", "MumeiLean.Settlement"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        timeout=600,
        env=_lake_env(),
    )
    combined = f"{proc.stdout}\n{proc.stderr}"
    assert proc.returncode == 0, (
        f"lake build MumeiLean.Settlement exited {proc.returncode}\n{combined}"
    )
    assert "declaration uses 'sorry'" not in combined
    assert "declaration uses sorry" not in combined
