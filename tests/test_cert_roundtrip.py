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

import expr_translator

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
        "lean_cert_schema_version",
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


@pytest.mark.skipif(not _have_lake(),
                    reason="lake not on PATH; skipping live Lean round-trip")
@pytest.mark.skipif(os.environ.get("MUMEI_LEAN_SKIP_LIVE") == "1",
                    reason="MUMEI_LEAN_SKIP_LIVE=1 set")
def test_lean_round_trip_preserves_python_bridge_metadata(tmp_path: Path):
    """Contract metadata and escalation timing survive the native path.

    The Python bridge (`scripts/bridge.py`) attaches `translator_version`,
    `bridge_lemma_hash`, and the measured `lean_solver_time_s` to each
    atom; the native parser/writer pair must forward all three so a
    certificate can be regenerated in Lean without losing the harness
    contract or the escalation cost mumei's benchmark consumes.
    """
    cert = json.loads(PILOT_FIXTURE.read_text())
    for atom in cert["atoms"]:
        atom["translator_version"] = expr_translator.TRANSLATOR_VERSION
        atom["bridge_lemma_hash"] = expr_translator.BRIDGE_LEMMA_HASH
        atom["lean_result_metadata"] = {
            "status": "lean_verified",
            "theorem_name": f"{atom['name']}_correct",
            "translator_version": expr_translator.TRANSLATOR_VERSION,
            "bridge_lemma_hash": expr_translator.BRIDGE_LEMMA_HASH,
            "proof_path": f"lean/{atom['name']}.lean",
            "lean_solver_time_s": 1.25,
            "diagnostics": ["escalation_reason=quantified_reasoning"],
        }
    cert_path = tmp_path / "with_metadata.proof-cert.json"
    cert_path.write_text(json.dumps(cert))

    proc = subprocess.run(
        ["lake", "env", "lean", "--run", str(DRIVER_LEAN), str(cert_path)],
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
    assert (
        summary["first_atom_translator_version"]
        == expr_translator.TRANSLATOR_VERSION
    )
    assert float(summary["first_atom_lean_solver_time_s"]) == pytest.approx(1.25)

    written = json.loads(summary["written_json"])
    for atom in written["atoms"]:
        assert atom["translator_version"] == expr_translator.TRANSLATOR_VERSION
        assert atom["bridge_lemma_hash"] == expr_translator.BRIDGE_LEMMA_HASH
        metadata = atom["lean_result_metadata"]
        assert metadata["lean_solver_time_s"] == pytest.approx(1.25)
        assert metadata["status"] == "lean_verified"


def test_cert_writer_preserves_unknown_escalation_metadata_shape():
    """The writer must emit — and never rewrite — escalation metadata."""
    src = WRITER_LEAN.read_text()
    for key in ("z3_result_class", "escalation_reason", "logic_fragment_tags"):
        assert f'"{key}"' in src, f"CertWriter must emit JSON key {key!r}"
    # ``applyResult`` upgrades the verdict fields only; the escalation
    # attribution mumei's benchmark consumes stays as parsed.
    assert "z3ResultClass :=" not in src


@pytest.mark.skipif(not _have_lake(),
                    reason="lake not on PATH; skipping live Lean round-trip")
@pytest.mark.skipif(os.environ.get("MUMEI_LEAN_SKIP_LIVE") == "1",
                    reason="MUMEI_LEAN_SKIP_LIVE=1 set")
def test_lean_round_trip_preserves_unknown_escalation_metadata(tmp_path: Path):
    """`z3_result_class` / `escalation_reason` / `logic_fragment_tags` survive.

    The Python bridge routes `unknown` atoms to Lean and keeps the
    escalation attribution on the exported atom even after the verdict is
    upgraded to `lean_verified`; the native parser/writer pair must behave
    identically or `scripts/bridge_metrics.py` loses its per-fragment and
    per-`z3_result_class` breakdown.
    """
    cert = json.loads(PILOT_FIXTURE.read_text())
    tags = ["finite_field", "nonlinear_arithmetic"]
    for atom in cert["atoms"]:
        atom["z3_result_class"] = "unknown"
        atom["escalation_reason"] = "z3_unknown"
        atom["logic_fragment_tags"] = tags
    cert_path = tmp_path / "with_escalation_metadata.proof-cert.json"
    cert_path.write_text(json.dumps(cert))

    proc = subprocess.run(
        ["lake", "env", "lean", "--run", str(DRIVER_LEAN), str(cert_path)],
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
    # Parsed back out of the *written* certificate, so this covers both
    # directions of the round trip.
    assert summary["first_atom_z3"] == "lean_verified"
    assert summary["first_atom_z3_result_class"] == "unknown"
    assert summary["first_atom_escalation_reason"] == "z3_unknown"
    assert summary["first_atom_logic_fragment_tags"] == tags

    written = json.loads(summary["written_json"])
    for atom in written["atoms"]:
        assert atom["z3_check_result"] == "lean_verified"
        assert atom["z3_result_class"] == "unknown"
        assert atom["escalation_reason"] == "z3_unknown"
        assert atom["logic_fragment_tags"] == tags
