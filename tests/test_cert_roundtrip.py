"""Tests for the native Lean ``CertParser`` / ``CertWriter`` pair.

The Lean side (``MumeiLean.CertParser`` / ``MumeiLean.CertWriter``)
exposes a self-contained round trip:

    parse  : String  → Except String ProofCertificateData
    write  : ProofCertificateData × results × leanVersion → String

These tests exercise that round trip by:

1. Asserting the static *shape* of both Lean modules — i.e. that the
   key declarations and JSON keys are present in the source. This
   guards against accidental skeleton regressions even on machines
   without a Lean toolchain.
2. Optionally invoking ``lake env lean --run`` against
   ``tests/fixtures/cert_roundtrip_driver.lean`` to perform the real
   round trip. Skipped (rather than failed) when ``lake`` is not on
   PATH so the Python suite stays green on minimal setups; CI's
   ``lean-build`` job exercises the toolchain path.
"""
from __future__ import annotations

import json
import os
import shutil
import subprocess
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parent.parent
PARSER_LEAN = REPO_ROOT / "MumeiLean" / "CertParser.lean"
WRITER_LEAN = REPO_ROOT / "MumeiLean" / "CertWriter.lean"
DRIVER_LEAN = REPO_ROOT / "tests" / "fixtures" / "cert_roundtrip_driver.lean"
PILOT_FIXTURE = REPO_ROOT / "tests" / "fixtures" / "pilot_proof_cert.json"


# ---------------------------------------------------------------------------
# Static shape tests — always run.
# ---------------------------------------------------------------------------


def test_cert_parser_lean_has_real_implementation():
    """CertParser must define a real Lean.Json-backed parser."""
    src = PARSER_LEAN.read_text()
    assert "import Lean.Data.Json" in src
    assert "def parseProofCertificate" in src
    assert "def parseAtomCertificate" in src
    # The old skeleton bailed out with this message; ensure the new
    # implementation no longer ships it as the *body* of
    # ``parseProofCertificate``.
    assert "not yet implemented" not in src
    # Sanity-check we read the canonical mumei JSON keys.
    for key in (
        "version",
        "mumei_version",
        "z3_version",
        "file",
        "z3_check_result",
        "content_hash",
        "proof_hash",
        "all_verified",
    ):
        assert f'"{key}"' in src, f"CertParser must read JSON key {key!r}"


def test_cert_writer_lean_has_real_implementation():
    """CertWriter must serialise to mumei's `ProofCertificate` schema."""
    src = WRITER_LEAN.read_text()
    assert "def writeLeanCertificate" in src
    assert "def writeLeanCertificateJson" in src
    assert "def applyResult" in src
    # The writer must add `lean_version` alongside `mumei_version` and
    # keep the canonical snake_case keys mumei resolvers expect.
    for key in (
        "version",
        "mumei_version",
        "lean_version",
        "z3_version",
        "file",
        "z3_check_result",
        "all_verified",
    ):
        assert f'"{key}"' in src, f"CertWriter must emit JSON key {key!r}"


def test_cert_writer_marks_lean_verified_for_proved_atoms():
    """The writer flips ``z3_check_result`` to ``"lean_verified"``."""
    src = WRITER_LEAN.read_text()
    # ``ProofResult.toZ3CheckResult`` (in MumeiLean.Basic) returns
    # "lean_verified" for the verified case, and CertWriter routes
    # that through ``applyResult`` to update the atom record.
    basic_src = (REPO_ROOT / "MumeiLean" / "Basic.lean").read_text()
    assert "\"lean_verified\"" in basic_src
    assert "applyResult" in src
    assert "toZ3CheckResult" in src


# ---------------------------------------------------------------------------
# Live round-trip — only when a Lean toolchain is reachable.
# ---------------------------------------------------------------------------


def _have_lake() -> bool:
    return shutil.which("lake") is not None


@pytest.mark.skipif(not _have_lake(),
                    reason="lake not on PATH; skipping live Lean round-trip")
@pytest.mark.skipif(os.environ.get("MUMEI_LEAN_SKIP_LIVE") == "1",
                    reason="MUMEI_LEAN_SKIP_LIVE=1 set")
def test_lean_parser_and_writer_round_trip(tmp_path: Path):
    """Drive the parser/writer end-to-end with the pilot fixture."""
    proc = subprocess.run(
        ["lake", "env", "lean", "--run", str(DRIVER_LEAN), str(PILOT_FIXTURE)],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        timeout=600,
    )
    assert proc.returncode == 0, (
        f"lake env lean exited {proc.returncode}\n"
        f"stdout:\n{proc.stdout}\nstderr:\n{proc.stderr}"
    )
    summary = json.loads(proc.stdout.strip().splitlines()[-1])
    assert summary["input_atom_count"] == summary["output_atom_count"] > 0
    assert summary["file"] == "std/pilot.mm"
    assert summary["first_atom_z3"] == "lean_verified"

    # The string the writer produced must itself be valid JSON in
    # mumei's schema.
    written = json.loads(summary["written_json"])
    assert written["lean_version"] == "lean4-test"
    assert written["all_verified"] is True
    for atom in written["atoms"]:
        assert atom["z3_check_result"] == "lean_verified"
        assert atom["status"] == "verified"
