"""Tests for ``scripts.export_cert``."""
from __future__ import annotations

import json
from pathlib import Path

import pytest

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
        # mumei stamps the translator contract on every atom; certs that
        # predate it are treated as stale, so fixtures must set both.
        "translator_version": TRANSLATOR_VERSION,
        "bridge_lemma_hash": BRIDGE_LEMMA_HASH,
    }


def _trusted_atom(name: str) -> dict:
    return {**_atom(name, z3="skipped"), "status": "trusted"}


#: Contract fields stamped by `_metadata_for_atoms` on every emitted
#: `lean_result_metadata` entry — metadata fixtures asserting promotion must
#: carry them or the stale-translator gate correctly rejects the result.
_CONTRACT = {
    "translator_version": TRANSLATOR_VERSION,
    "bridge_lemma_hash": BRIDGE_LEMMA_HASH,
}


def _meta(**kw) -> dict:
    return {**_CONTRACT, **kw}


def _certificate(atoms: list) -> dict:
    return {
        "version": "1.0",
        "timestamp": "2026-04-28T00:00:00Z",
        "mumei_version": "0.6.12",
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
            "abs_saturating": _meta(
                status=LEAN_VERIFIED,
                proof_path="MumeiLean/StdMathAbs.lean",
            ),
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


def _upgrade_with_lean_atom(atoms: list) -> dict:
    upgraded = upgrade_certificate(
        cert=_certificate([_atom("candidate"), *atoms]),
        proved_atoms=["candidate"],
        failed_atoms=[],
        lean_version="x",
    )
    candidate = next(atom for atom in upgraded["atoms"] if atom["name"] == "candidate")
    assert candidate["z3_check_result"] == LEAN_VERIFIED
    return upgraded


def test_all_verified_counts_trusted_and_unsat_atoms():
    unsat = {**_atom("unsat", z3="unsat"), "spec_validation_result": {}}
    upgraded = _upgrade_with_lean_atom(
        [_trusted_atom("trusted"), unsat]
    )
    assert upgraded["all_verified"] is True


def test_all_verified_rejects_unknown_atoms_alongside_trusted_atoms():
    upgraded = _upgrade_with_lean_atom([_trusted_atom("trusted"), _atom("unknown")])
    assert upgraded["all_verified"] is False


def test_all_verified_preserves_input_when_no_atom_is_upgraded():
    cert = _certificate([_trusted_atom("trusted")])
    upgraded = upgrade_certificate(
        cert=cert,
        proved_atoms=[],
        failed_atoms=[],
        lean_version="x",
    )
    assert upgraded["all_verified"] is cert["all_verified"] is False


def test_all_verified_keeps_legacy_unsat_verified_atoms():
    upgraded = _upgrade_with_lean_atom([_atom("legacy", z3="unsat")])
    assert upgraded["all_verified"] is True


def test_all_verified_rejects_verified_status_with_skipped_z3_result():
    upgraded = _upgrade_with_lean_atom([_atom("skipped", z3="skipped")])
    assert upgraded["all_verified"] is False


def test_all_verified_rejects_trusted_atom_with_unsatisfiable_spec():
    trusted = {
        **_trusted_atom("trusted"),
        "spec_validation_result": {"is_satisfiable": False},
    }
    upgraded = _upgrade_with_lean_atom([trusted])
    assert upgraded["all_verified"] is False


def test_all_verified_rejects_unsat_atom_with_unsatisfiable_spec():
    unsat = {
        **_atom("unsat", z3="unsat"),
        "spec_validation_result": {"is_satisfiable": False},
    }
    upgraded = _upgrade_with_lean_atom([unsat])
    assert upgraded["all_verified"] is False


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
    assert json.loads(upgraded["harness_contract"]) == harness_contract


def test_upgrade_certificate_does_not_promote_manual_metadata():
    cert = _certificate([_atom("unknown_placeholder")])
    upgraded = upgrade_certificate(
        cert=cert,
        proved_atoms=["unknown_placeholder"],
        failed_atoms=[],
        lean_version="x",
        atom_metadata={
            "unknown_placeholder": _meta(
                status="manual_lemma_required",
                manual_lemma_reason=(
                    "unknown_obligation_requires_manual_lemma"
                ),
            ),
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
        atom_metadata={"closed": _meta(status=LEAN_VERIFIED)},
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


def test_upgrade_certificate_promotes_spurious_candidate_path():
    """PR3 path 7 (exists_pivot_partition) is a ``spurious_candidate`` atom.

    The export path must treat it as an escalation candidate and promote it to
    ``lean_verified`` with the pinned contract constants attached."""
    cert = _certificate(
        [{**_atom("exists_pivot_partition", z3="spurious_candidate"),
          "escalation_reason": "spurious_candidate"}]
    )
    upgraded = upgrade_certificate(
        cert=cert,
        proved_atoms=["exists_pivot_partition"],
        failed_atoms=[],
        lean_version="x",
        atom_metadata={
            "exists_pivot_partition": _meta(
                status=LEAN_VERIFIED,
                proof_path="Generated/Std/List.lean",
            ),
        },
    )
    atom = upgraded["atoms"][0]
    assert atom["z3_check_result"] == LEAN_VERIFIED
    assert atom["status"] == "verified"
    assert atom["lean_result_metadata"]["translator_version"] == TRANSLATOR_VERSION
    assert atom["lean_result_metadata"]["bridge_lemma_hash"] == BRIDGE_LEMMA_HASH


def test_upgrade_certificate_preserves_sc_rtgs_escalation_metadata():
    cert = _certificate([_atom("withdraw_guard")])
    upgraded = upgrade_certificate(
        cert=cert,
        proved_atoms=["withdraw_guard"],
        failed_atoms=[],
        lean_version="x",
        atom_metadata={
            "withdraw_guard": _meta(
                status=LEAN_VERIFIED,
                logic_fragment_tags=["smart_contract"],
            ),
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
            "inc": _meta(status=LEAN_VERIFIED, proof_path="Generated/Math.lean"),
            "manual": _meta(status="manual_required"),
        },
    )
    by_name = {a["name"]: a for a in upgraded["candidates"]}
    assert by_name["inc"]["z3_check_result"] == LEAN_VERIFIED
    assert by_name["inc"]["lean_metadata"]["proof_path"] == "Generated/Math.lean"
    assert by_name["inc"]["lean_result_metadata"]["proof_path"] == "Generated/Math.lean"
    assert by_name["manual"]["z3_check_result"] == "unknown"
    assert by_name["manual"]["lean_metadata"]["status"] == "manual_required"
    assert by_name["manual"]["lean_result_metadata"]["status"] == "manual_required"


def test_dual_check_success_preserves_z3_proof_fields_and_all_verified():
    unsat = _atom("already_proved", z3="unsat")
    unsat["escalation_reason"] = "preserve-me"
    unsat["lean_metadata"] = {"source": "lean_metadata"}
    unsat["lean_result_metadata"] = {"source": "lean_result_metadata"}
    cert = _certificate([unsat, _trusted_atom("trusted")])
    cert["all_verified"] = False
    dual_metadata = _meta(
        status=LEAN_VERIFIED,
        theorem_name="already_proved_correct",
        proof_path="Generated/Math.lean",
        kernel_axioms=["propext"],
        axiom_audit="passed",
    )

    upgraded = upgrade_certificate(
        cert=cert,
        proved_atoms=["already_proved"],
        failed_atoms=[],
        lean_version="lean",
        atom_metadata={"already_proved": dual_metadata},
        dual_check=True,
    )
    atom = upgraded["atoms"][0]

    assert atom["lean_dual_check"]["status"] == LEAN_VERIFIED
    assert atom["lean_dual_check"]["theorem_name"] == "already_proved_correct"
    assert atom["lean_dual_check"]["proof_path"] == "Generated/Math.lean"
    assert atom["lean_dual_check"]["kernel_axioms"] == ["propext"]
    assert atom["lean_dual_check"]["axiom_audit"] == "passed"
    assert atom["z3_check_result"] == "unsat"
    assert atom["status"] == "verified"
    assert atom["translator_version"] == TRANSLATOR_VERSION
    assert atom["bridge_lemma_hash"] == BRIDGE_LEMMA_HASH
    assert atom["escalation_reason"] == "preserve-me"
    assert atom["lean_metadata"] == {"source": "lean_metadata"}
    assert atom["lean_result_metadata"] == {"source": "lean_result_metadata"}
    assert upgraded["all_verified"] is False
    assert "certificate_hash" not in upgraded
    assert upgraded["atoms"][1] == cert["atoms"][1]


@pytest.mark.parametrize(
    ("source_update", "metadata_update", "proved", "failed", "expected"),
    [
        ({}, {"status": "manual_lemma_required"}, ["dual"], [], "failed"),
        (
            {},
            {"status": "manual_lemma_required"},
            ["dual"],
            ["dual"],
            "failed",
        ),
        (
            {"manual_lemma_reason": "requires a domain lemma"},
            {"status": "manual_lemma_required"},
            ["dual"],
            [],
            "manual_lemma_required",
        ),
        ({}, {"status": "partial_translation"}, ["dual"], [], "partial_translation"),
        ({}, {"status": LEAN_VERIFIED}, ["dual"], [], "failed"),
        (
            {"translator_version": "old-translator"},
            {"status": LEAN_VERIFIED, "translator_version": "old-translator"},
            ["dual"],
            ["dual"],
            "stale_translator",
        ),
        ({}, {"status": LEAN_VERIFIED}, ["dual"], ["dual"], "failed"),
    ],
)
def test_dual_check_nonverified_attempts_are_recorded(
    source_update, metadata_update, proved, failed, expected
):
    atom = {**_atom("dual", z3="unsat"), **source_update}
    cert = _certificate([atom])
    cert["all_verified"] = False
    metadata = _meta(theorem_name="dual_correct", proof_path="Generated/Math.lean")
    metadata.update(metadata_update)

    upgraded = upgrade_certificate(
        cert=cert,
        proved_atoms=proved,
        failed_atoms=failed,
        lean_version="lean",
        atom_metadata={"dual": metadata},
        dual_check=True,
    )
    dual = upgraded["atoms"][0]["lean_dual_check"]

    assert dual["status"] == expected
    assert upgraded["atoms"][0]["z3_check_result"] == "unsat"
    assert upgraded["atoms"][0]["status"] == "verified"
    assert upgraded["all_verified"] is False
    assert "certificate_hash" not in upgraded


def test_dual_check_rejected_axiom_audit_is_preserved_but_not_counted_as_passed():
    rejected = _meta(
        status=LEAN_VERIFIED,
        theorem_name="dual_correct",
        proof_path="Generated/Math.lean",
        kernel_axioms=["User.assumption"],
        axiom_audit="rejected",
    )
    upgraded = upgrade_certificate(
        cert={
            "file": "math.mm",
            "candidates": [_atom("dual", z3="unsat")],
            "summary": {},
        },
        proved_atoms=["dual"],
        failed_atoms=[],
        lean_version="lean",
        atom_metadata={"dual": rejected},
        dual_check=True,
    )

    assert upgraded["candidates"][0]["lean_dual_check"]["axiom_audit"] == "rejected"
    assert upgraded["candidates"][0]["lean_dual_check"]["status"] == "failed"
    assert upgraded["summary"]["dual_checked"] == 1
    assert upgraded["summary"]["dual_check_passed"] == 0


def test_dual_check_does_not_change_unknown_upgrade_or_default_output():
    cert = _certificate(
        [
            _atom("unsat", z3="unsat"),
            _atom("unknown"),
            _trusted_atom("trusted"),
        ]
    )
    off_implicit = upgrade_certificate(
        cert, ["unsat", "unknown"], [], "lean"
    )
    off_explicit = upgrade_certificate(
        cert, ["unsat", "unknown"], [], "lean", dual_check=False
    )
    assert off_implicit == off_explicit
    assert "lean_dual_check" not in off_explicit["atoms"][0]

    metadata = _meta(
        status=LEAN_VERIFIED,
        theorem_name="unknown_correct",
        proof_path="Generated/Math.lean",
    )
    on = upgrade_certificate(
        cert,
        ["unsat", "unknown"],
        [],
        "lean",
        atom_metadata={"unknown": metadata},
        dual_check=True,
    )
    assert on["atoms"][0]["z3_check_result"] == "unsat"
    assert "lean_dual_check" not in on["atoms"][1]
    assert on["atoms"][1]["z3_check_result"] == LEAN_VERIFIED


def test_dual_check_handles_module_and_candidate_envelopes():
    metadata = _meta(
        status=LEAN_VERIFIED,
        theorem_name="dual_correct",
        proof_path="Generated/Math.lean",
        kernel_axioms=[],
        axiom_audit="passed",
    )
    cert = _certificate([_atom("dual", z3="unsat")])
    bundle = {
        "bundle_version": "1.0",
        "modules": {"std/math": cert},
        "summary": {},
    }
    upgraded_bundle = upgrade_certificate(
        bundle,
        ["dual"],
        [],
        "lean",
        atom_metadata={"dual": metadata},
        dual_check=True,
    )
    assert (
        upgraded_bundle["modules"]["std/math"]["atoms"][0]["lean_dual_check"][
            "status"
        ]
        == LEAN_VERIFIED
    )
    assert upgraded_bundle["summary"]["dual_check_passed"] == 1

    candidates = {
        "file": "std/math.mm",
        "candidates": [_atom("dual", z3="unsat")],
        "summary": {},
        "certificate_hash": "stale",
    }
    upgraded_candidates = upgrade_certificate(
        candidates,
        ["dual"],
        [],
        "lean",
        atom_metadata={"dual": metadata},
        dual_check=True,
    )
    assert upgraded_candidates["candidates"][0]["lean_dual_check"]["status"] == LEAN_VERIFIED
    assert upgraded_candidates["summary"]["dual_checked"] == 1
    assert upgraded_candidates["summary"]["dual_check_passed"] == 1
    assert "certificate_hash" not in upgraded_candidates


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


def _manual_reason_cert() -> dict:
    return _certificate(
        [{**_atom("inc"), "manual_lemma_reason": "template_catalog_miss"}]
    )


def _upgrade_with_metadata(metadata: dict) -> str:
    upgraded = upgrade_certificate(
        cert=_manual_reason_cert(),
        proved_atoms=["inc"],
        failed_atoms=[],
        lean_version="leanprover/lean4:v4.15.0",
        atom_metadata={"inc": {**_CONTRACT, **metadata}},
    )
    return upgraded["atoms"][0]["z3_check_result"]


def test_manual_lemma_reason_blocks_promotion_without_supersession():
    assert _upgrade_with_metadata({"status": LEAN_VERIFIED}) == "unknown"
    # A provenance block that does not name the source reason is not enough.
    assert (
        _upgrade_with_metadata(
            {"status": LEAN_VERIFIED, "external_proof": {"source": "ai_generated_proof"}}
        )
        == "unknown"
    )
    assert (
        _upgrade_with_metadata(
            {
                "status": LEAN_VERIFIED,
                "external_proof": {"supersedes_manual_lemma_reason": "other_reason"},
            }
        )
        == "unknown"
    )


def test_manual_lemma_reason_superseded_by_external_proof_or_tactic_search():
    assert (
        _upgrade_with_metadata(
            {
                "status": LEAN_VERIFIED,
                "external_proof": {
                    "source": "ai_generated_proof",
                    "supersedes_manual_lemma_reason": "template_catalog_miss",
                },
            }
        )
        == LEAN_VERIFIED
    )
    assert (
        _upgrade_with_metadata(
            {
                "status": LEAN_VERIFIED,
                "tactic_search": {
                    "adopted_tactic": "omega",
                    "supersedes_manual_lemma_reason": "template_catalog_miss",
                },
            }
        )
        == LEAN_VERIFIED
    )
    # A failed build never promotes, whatever the provenance says.
    assert (
        _upgrade_with_metadata(
            {
                "status": "manual_lemma_required",
                "external_proof": {
                    "supersedes_manual_lemma_reason": "template_catalog_miss"
                },
            }
        )
        == "unknown"
    )
