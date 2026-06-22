"""Tests for ``scripts.export_cert``."""
from __future__ import annotations

import json
from pathlib import Path

from export_cert import (
    BRIDGE_LEMMA_HASH,
    LEAN_VERIFIED,
    TRANSLATOR_VERSION,
    _failed_theorem_attributions,
    _failed_theorem_names,
    _has_unattributable_failures,
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
        "mumei_version": "0.6.0",
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


def test_upgrade_certificate_known_witness_override_marks_atom_verified():
    cert = _certificate([_atom("abs_saturating")])
    upgraded = upgrade_certificate(
        cert=cert,
        proved_atoms=[],
        failed_atoms=["abs_saturating"],
        lean_version="leanprover/lean4:v4.15.0",
        known_witness_override=["abs_saturating"],
        atom_metadata={
            "abs_saturating": {
                "status": LEAN_VERIFIED,
                "proof_path": "MumeiLean/StdMathAbs.lean",
            }
        },
    )
    atom = upgraded["atoms"][0]
    assert atom["z3_check_result"] == LEAN_VERIFIED
    assert atom["status"] == "verified"
    assert atom["lean_metadata"]["proof_path"] == "MumeiLean/StdMathAbs.lean"


def test_upgrade_certificate_known_witness_override_requires_unknown_candidate():
    cert = _certificate([_atom("abs_saturating", z3="unsat")])

    upgraded = upgrade_certificate(
        cert=cert,
        proved_atoms=[],
        failed_atoms=[],
        lean_version="leanprover/lean4:v4.15.0",
        known_witness_override=["abs_saturating"],
    )

    atom = upgraded["atoms"][0]
    assert atom["z3_check_result"] == "unsat"
    assert "lean_metadata" not in atom


def test_upgrade_certificate_promotes_generated_known_witness_attribution():
    cert = _certificate([_atom("abs_saturating")])
    upgraded = upgrade_certificate(
        cert=cert,
        proved_atoms=["Generated.Std.Math.Abs.abs_saturating_correct"],
        failed_atoms=[],
        lean_version="leanprover/lean4:v4.15.0",
    )
    atom = upgraded["atoms"][0]
    assert atom["z3_check_result"] == LEAN_VERIFIED
    assert atom["lean_metadata"]["known_witness_used"] is True
    assert atom["lean_metadata"]["lean_module"] == "MumeiLean.StdMathAbs"
    assert atom["lean_metadata"]["lean_theorem_name"] == "abs_saturating_correct"


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


def test_upgrade_certificate_can_attach_harness_contract():
    cert = _certificate([_atom("inc")])
    harness_contract = {"policy": "mumei-lean-bridge-harness/v1"}
    upgraded = upgrade_certificate(
        cert=cert,
        proved_atoms=["inc"],
        failed_atoms=[],
        lean_version="x",
        harness_contract=harness_contract,
    )
    assert upgraded["harness_contract"] == harness_contract


def test_upgrade_certificate_does_not_promote_manual_metadata():
    cert = _certificate([_atom("unknown_placeholder")])
    upgraded = upgrade_certificate(
        cert=cert,
        proved_atoms=["unknown_placeholder"],
        failed_atoms=[],
        lean_version="x",
        atom_metadata={
            "unknown_placeholder": {
                "status": "manual_lemma_required",
                "manual_lemma_reason": (
                    "unknown_obligation_requires_manual_lemma"
                ),
            },
        },
    )
    atom = upgraded["atoms"][0]
    assert atom["z3_check_result"] == "unknown"
    assert atom["status"] == "unknown"
    assert atom["lean_metadata"]["status"] == "manual_lemma_required"


def test_upgrade_certificate_only_promotes_unknown_candidates():
    cert = _certificate([_atom("closed", z3="unsat")])

    upgraded = upgrade_certificate(
        cert=cert,
        proved_atoms=["closed"],
        failed_atoms=[],
        lean_version="x",
        atom_metadata={"closed": {"status": LEAN_VERIFIED}},
    )

    atom = upgraded["atoms"][0]
    assert atom["z3_check_result"] == "unsat"
    assert "lean_metadata" not in atom


def test_upgrade_certificate_marks_stale_translator_metadata_unproven():
    cert = _certificate(
        [
            {
                **_atom("stale"),
                "translator_version": TRANSLATOR_VERSION,
                "bridge_lemma_hash": BRIDGE_LEMMA_HASH,
            }
        ]
    )

    upgraded = upgrade_certificate(
        cert=cert,
        proved_atoms=["stale"],
        failed_atoms=[],
        lean_version="x",
        atom_metadata={
            "stale": {
                "status": LEAN_VERIFIED,
                "translator_version": "old-translator",
                "bridge_lemma_hash": BRIDGE_LEMMA_HASH,
            }
        },
    )

    atom = upgraded["atoms"][0]
    assert atom["z3_check_result"] == "unknown"
    assert atom["lean_result_metadata"]["status"] == "stale_translator"
    assert atom["lean_result_metadata"]["translator_version"] == "old-translator"


def test_upgrade_certificate_preserves_sc_rtgs_escalation_metadata():
    cert = _certificate([_atom("withdraw_guard")])
    upgraded = upgrade_certificate(
        cert=cert,
        proved_atoms=["withdraw_guard"],
        failed_atoms=[],
        lean_version="x",
        atom_metadata={
            "withdraw_guard": {
                "status": LEAN_VERIFIED,
                "logic_fragment_tags": ["smart_contract"],
            },
        },
    )
    atom = upgraded["atoms"][0]

    assert atom["unknown_obligation_domain"] == "smart_contract"
    assert atom["escalation_reason"] == "sc"
    assert atom["lean_metadata"]["unknown_obligation_domain"] == "smart_contract"
    assert atom["lean_metadata"]["escalation_reason"] == "sc"


def test_failed_theorem_names_picks_up_compile_errors():
    log = """\
Generated/Std/Math.lean:12:0: theorem broken_correct
Generated/Std/Math.lean:12:5: error: unknown identifier 'foo'
"""
    failures = _failed_theorem_names(log)
    assert failures == ["broken"]


def test_has_unattributable_failures_detects_file_level_errors():
    log = (
        "Generated/Std/Math.lean:1:0: error: unknown module 'MumeiLean'\n"
        "Generated/Std/Math.lean:5:0: theorem inc_correct\n"
    )
    assert _has_unattributable_failures(log) is True


def test_has_unattributable_failures_false_when_all_attributed():
    log = (
        "Generated/Std/Math.lean:5:0: theorem inc_correct\n"
        "Generated/Std/Math.lean:5:0: warning: declaration uses 'sorry'\n"
    )
    assert _has_unattributable_failures(log) is False


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


def test_upgrade_certificate_handles_escalation_bundle_metadata():
    bundle = {
        "version": "1.0",
        "file": "std/math.mm",
        "summary": {},
        "candidates": [
            {
                **_atom("inc"),
                "escalation_reason": "z3_unknown",
                "logic_fragment_tags": ["quantifier_alternation"],
            },
            {**_atom("manual"), "escalation_reason": "manual_review"},
        ],
    }
    upgraded = upgrade_certificate(
        cert=bundle,
        proved_atoms=["inc", "manual"],
        failed_atoms=["manual"],
        lean_version="x",
        atom_metadata={
            "inc": {"status": LEAN_VERIFIED, "proof_path": "Generated/Math.lean"},
            "manual": {"status": "manual_required"},
        },
    )
    by_name = {a["name"]: a for a in upgraded["candidates"]}
    assert by_name["inc"]["z3_check_result"] == LEAN_VERIFIED
    assert by_name["inc"]["lean_metadata"]["proof_path"] == "Generated/Math.lean"
    assert by_name["inc"]["lean_result_metadata"]["proof_path"] == "Generated/Math.lean"
    assert by_name["manual"]["z3_check_result"] == "unknown"
    assert by_name["manual"]["lean_metadata"]["status"] == "manual_required"
    assert by_name["manual"]["lean_result_metadata"]["status"] == "manual_required"


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


def test_failed_theorem_attributions_includes_file_path():
    log = (
        "Generated/Std/Math.lean:12:0: theorem inc_correct\n"
        "Generated/Std/Math.lean:12:0: warning: declaration uses 'sorry'\n"
        "Generated/Std/List.lean:30:0: theorem inc_correct\n"
        "Generated/Std/List.lean:30:5: error: unknown identifier 'foo'\n"
    )
    attributions = _failed_theorem_attributions(log)
    assert ("Generated/Std/Math.lean", "inc") in attributions
    assert ("Generated/Std/List.lean", "inc") in attributions
    # Same theorem name in two different files must produce two
    # distinct attributions, not be deduped down to one entry.
    assert len(attributions) == 2


def test_failed_theorem_names_attributes_errors_inside_def_result_block():
    # ``ingest_cert.render_theorem`` emits ``def <atom>Result`` ahead of
    # the owning ``theorem`` when body semantics are enabled. An error
    # inside the ``def`` would otherwise hit no ``theorem`` keyword on
    # the backward walk and be misattributed as a file-level failure.
    log = (
        "Generated/Std/Math/Abs.lean:5:0: def absSaturatingAutoResult\n"
        "Generated/Std/Math/Abs.lean:5:7: error: type mismatch\n"
    )
    failures = _failed_theorem_names(log)
    assert failures == ["abs_saturating_auto"]
    # And the unattributable-failure fallback must not fire.
    assert _has_unattributable_failures(log) is False


def test_failed_theorem_names_preserves_correct_suffix_from_def_result_block():
    log = (
        "Generated/Std/Math/Abs.lean:5:0: def checkCorrectResult\n"
        "Generated/Std/Math/Abs.lean:5:7: error: type mismatch\n"
    )
    failures = _failed_theorem_names(log)
    assert failures == ["check_correct"]


def test_failed_theorem_attributions_emits_none_when_no_file_prefix():
    # Older / non-Lake-formatted logs may surface ``error:`` /
    # ``sorry`` lines without a ``file:line:col:`` prefix; the
    # attribution should still record the theorem name with
    # ``file_path=None`` so callers can apply it conservatively.
    log = (
        "theorem orphan_correct\n"
        "warning: declaration uses 'sorry'\n"
    )
    attributions = _failed_theorem_attributions(log)
    assert attributions == [(None, "orphan")]


def test_failed_theorem_attributions_reads_source_for_declaration_sorry(tmp_path: Path):
    source = tmp_path / "generated" / "Generated" / "Std" / "Math" / "Abs.lean"
    source.parent.mkdir(parents=True)
    source.write_text(
        "import MumeiLean\n\n"
        "theorem abs_saturating_correct (x result : Int) :\n"
        "    (True) → (result ≥ 0) := by\n"
        "  mumei_arith <;> sorry\n"
    )
    log = (
        "warning: ./generated/Generated/Std/Math/Abs.lean:3:8: "
        "declaration uses 'sorry'\n"
    )
    attributions = _failed_theorem_attributions(log, source_root=tmp_path)
    assert attributions == [("./generated/Generated/Std/Math/Abs.lean", "abs_saturating")]
    assert _has_unattributable_failures(log, source_root=tmp_path) is False


def test_failed_theorem_attributions_maps_generated_known_witness_name():
    log = (
        "Generated/Std/Math/Abs.lean:5:0: theorem "
        "Generated.Std.Math.Abs.abs_saturating_correct\n"
        "Generated/Std/Math/Abs.lean:5:0: warning: declaration uses 'sorry'\n"
    )
    assert _failed_theorem_attributions(log) == [
        ("Generated/Std/Math/Abs.lean", "abs_saturating")
    ]
