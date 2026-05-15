"""Tests for the reusable ``MumeiLean.Crypto`` proof library."""
from __future__ import annotations

import os
import shutil
import subprocess
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parent.parent
CRYPTO_LEAN = REPO_ROOT / "MumeiLean" / "Crypto.lean"
CRYPTO_HELPERS_LEAN = REPO_ROOT / "MumeiLean" / "CryptoHelpers.lean"


def _lake_env() -> dict[str, str]:
    env = os.environ.copy()
    elan_bin = Path.home() / ".elan" / "bin"
    env["PATH"] = f"{elan_bin}:{env.get('PATH', '')}"
    return env


def _have_lake() -> bool:
    return shutil.which("lake", path=_lake_env()["PATH"]) is not None


def test_crypto_lean_declares_expected_library():
    src = CRYPTO_LEAN.read_text()
    for declaration in (
        "theorem rsa_signature_correct",
        "theorem rsa_signature_identity_exponents",
        "theorem rsa_signature_verifies_of_modEq",
        "theorem field_add_preserves",
        "theorem field_mul_preserves",
    ):
        assert declaration in src
    assert "by\n  sorry" not in src


def test_crypto_helpers_define_translator_targets():
    src = CRYPTO_HELPERS_LEAN.read_text()
    for declaration in ("def mumei_mod", "def mumei_pow", "def mumei_phi"):
        assert declaration in src
    assert "Nat.totient" in src
    assert "by\n  sorry" not in src


@pytest.mark.skipif(not _have_lake(),
                    reason="lake not on PATH; skipping live Lean build")
@pytest.mark.skipif(os.environ.get("MUMEI_LEAN_SKIP_LIVE") == "1",
                    reason="MUMEI_LEAN_SKIP_LIVE=1 set")
def test_crypto_modules_build_without_sorry_warnings():
    for target in ("MumeiLean.CryptoHelpers", "MumeiLean.Crypto"):
        proc = subprocess.run(
            ["lake", "build", target],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            timeout=600,
            env=_lake_env(),
        )
        combined = f"{proc.stdout}\n{proc.stderr}"
        assert proc.returncode == 0, (
            f"lake build {target} exited {proc.returncode}\n{combined}"
        )
        assert "declaration uses 'sorry'" not in combined
        assert "declaration uses sorry" not in combined
