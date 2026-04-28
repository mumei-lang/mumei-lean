"""Tests for ``scripts.export_cert``."""
from __future__ import annotations

import json
from pathlib import Path

from export_cert import (
    LEAN_VERIFIED,
    _failed_theorem_names,
    main,
    upgrade_certificate,
)


def _atom(name: str, z3: str = "unknown") -> dict:
    return {
        "name": name,
        "requires": "x > 0",
        "ensures": "result >= x",
        "z3_check_result": z3,
        "status": "unknown" if z3 == "unknown" else "verified",
        "content_hash": "h",
        "proof_hash": "p",
        "dependencies": [],
        "effects": [],
    }


def _certificate(atoms: list) -> dict:
    return {
        "version": "1.0",
        "timestamp": "2026-04-28T00:00:00Z",
        "mumei_version": "0.5.6",
        "z3_version": "4.12.2",
        "file": "math.mm",
        "atoms": atoms,
        "package_name": "test",
        "package_version": "0.0.0",
        "certificate_hash": "deadbeef",
        "all_verified": False,
    }


def test_failed_theorem_names_picks_up_sorry_warnings():
    log = """\
[1/4] Building Generated.Std.Math
Generated/Std/Math.lean:12:0: theorem inc_correct
Generated/Std/Math.lean:12:0: warning: declaration uses 'sorry'
[2/4] Building Generated.Std.Math
Generated/Std/Math.lean:30:0: theorem dec_correct
Generated/Std/Math.lean:30:0: warning: declaration uses 'sorry'
[3/4] Built (Generated.Std.Math)
"""
    failures = _failed_theorem_names(log)
    assert sorted(failures) == ["dec", "inc"]


def test_upgrade_certificate_marks_proven_atoms():
    cert = _certificate([_atom("inc"), _atom("dec")])
    upgraded = upgrade_certificate(
        cert=cert,
        proved_atoms=["inc", "dec"],
        failed_atoms=["dec"],
        lean_version="leanprover/lean4:v4.15.0",
    )
    by_name = {a["name"]: a for a in upgraded["atoms"]}
    assert by_name["inc"]["z3_check_result"] == LEAN_VERIFIED
    assert by_name["inc"]["status"] == "verified"
    # dec failed; should be left as-is
    assert by_name["dec"]["z3_check_result"] == "unknown"
    assert upgraded["lean_version"] == "leanprover/lean4:v4.15.0"


def test_upgrade_certificate_drops_stale_certificate_hash():
    cert = _certificate([_atom("inc")])
    cert["certificate_hash"] = "stale"
    upgraded = upgrade_certificate(
        cert=cert,
        proved_atoms=["inc"],
        failed_atoms=[],
        lean_version="x",
    )
    assert "certificate_hash" not in upgraded


def test_upgrade_certificate_does_not_mutate_input():
    cert = _certificate([_atom("inc")])
    upgrade_certificate(
        cert=cert,
        proved_atoms=["inc"],
        failed_atoms=[],
        lean_version="x",
    )
    # Original input still has unknown atom.
    assert cert["atoms"][0]["z3_check_result"] == "unknown"


def test_all_verified_flips_when_every_atom_is_proved():
    cert = _certificate([_atom("inc"), _atom("dec", z3="unsat")])
    upgraded = upgrade_certificate(
        cert=cert,
        proved_atoms=["inc"],
        failed_atoms=[],
        lean_version="x",
    )
    assert upgraded["all_verified"] is True


def test_failed_theorem_names_picks_up_compile_errors():
    log = """\
Generated/Std/Math.lean:12:0: theorem broken_correct
Generated/Std/Math.lean:12:5: error: unknown identifier 'foo'
"""
    failures = _failed_theorem_names(log)
    assert failures == ["broken"]


def test_upgrade_certificate_handles_bundle():
    bundle = {
        "bundle_version": "1.0",
        "modules": {
            "std/math": _certificate([_atom("inc")]),
            "std/list": _certificate([_atom("len")]),
        },
        "summary": {},
    }
    upgraded = upgrade_certificate(
        cert=bundle,
        proved_atoms=["inc", "len"],
        failed_atoms=["len"],
        lean_version="x",
    )
    inc = upgraded["modules"]["std/math"]["atoms"][0]
    length = upgraded["modules"]["std/list"]["atoms"][0]
    assert inc["z3_check_result"] == LEAN_VERIFIED
    assert length["z3_check_result"] == "unknown"
    assert upgraded["lean_version"] == "x"


def test_main_end_to_end(tmp_path: Path):
    cert_path = tmp_path / "cert.json"
    cert_path.write_text(json.dumps(_certificate([_atom("inc"), _atom("dec")])))

    log_path = tmp_path / "log.txt"
    log_path.write_text(
        "Generated/M.lean:1:0: theorem dec_correct\n"
        "Generated/M.lean:1:0: warning: declaration uses 'sorry'\n"
    )
    proved = tmp_path / "proved.txt"
    proved.write_text("inc\ndec\n")
    out = tmp_path / "out.json"
    rc = main(
        [
            "--input-cert", str(cert_path),
            "--build-log", str(log_path),
            "--proved-atoms", str(proved),
            "--out", str(out),
            "--lean-version", "leanprover/lean4:v4.15.0",
        ]
    )
    assert rc == 0
    upgraded = json.loads(out.read_text())
    by_name = {a["name"]: a for a in upgraded["atoms"]}
    assert by_name["inc"]["z3_check_result"] == LEAN_VERIFIED
    assert by_name["dec"]["z3_check_result"] == "unknown"
