"""Tests for ``scripts.external_proof`` and its injection path (spec §13)."""
from __future__ import annotations

import json
from pathlib import Path

import pytest

import bridge
from external_proof import (
    AI_GENERATED_PROOF,
    ExternalProof,
    apply_external_proofs,
    load_external_proofs,
    parse_external_proofs,
    reject_external_proof,
    reject_unsound_tactic_script,
)
from ingest_cert import collect_unknown_atoms, main as ingest_main, render_theorem
from tactic_search import STAGE_BUILD_FAILURE, STAGE_RESIDUAL, is_search_eligible


def _cert(atoms: list) -> dict:
    return {
        "version": "1.0",
        "timestamp": "2026-04-28T00:00:00Z",
        "mumei_version": "0.6.12",
        "z3_version": "4.12.2",
        "file": "std/quintic.mm",
        "atoms": atoms,
    }


def _unknown_atom(name: str = "quintic_pos", **overrides) -> dict:
    atom = {
        "name": name,
        "requires": "x > 0",
        "ensures": "result > 0",
        "body_expr": "{ x * x * x * x * x }",
        "z3_check_result": "unknown",
        "z3_result_class": "unknown",
        "status": "unknown",
        "content_hash": "",
        "proof_hash": "",
    }
    atom.update(overrides)
    return atom


GOOD_SCRIPT = "intro hx\nsubst h_body\nunfold quinticPosResult\nexact mul_pos hx hx"


@pytest.mark.parametrize(
    ("script", "reason"),
    [
        ("", "empty_source"),
        ("intro h\n  sorry", "forbidden_token:sorry"),
        ("admit", "forbidden_token:admit"),
        ("native_decide", "forbidden_token:native_decide"),
        ("set_option maxHeartbeats 0 in omega", "forbidden_token:set_option"),
        ("theorem evil : True := trivial", "forbidden_token:declaration"),
        ("run_tac do pure ()", "forbidden_token:run_tac"),
        ("omega", None),
    ],
)
def test_reject_unsound_tactic_script(script: str, reason):
    assert reject_unsound_tactic_script(script) == reason


def test_reject_external_proof_shape_rules():
    both = ExternalProof(atom="a", tactic_script="omega", witness_lemma="foo")
    assert reject_external_proof(both) == (
        "exactly_one_of_tactic_script_or_witness_lemma_required"
    )
    neither = ExternalProof(atom="a")
    assert reject_external_proof(neither) == (
        "exactly_one_of_tactic_script_or_witness_lemma_required"
    )
    bad_name = ExternalProof(atom="a", witness_lemma="foo; sorry")
    assert reject_external_proof(bad_name) == "invalid_witness_lemma_name"
    bad_source = ExternalProof(atom="a", tactic_script="omega", source="oracle")
    assert reject_external_proof(bad_source) == "unknown_source:oracle"
    assert reject_external_proof(ExternalProof(atom="a", witness_lemma="Std.foo")) is None


def test_parse_external_proofs_accepts_both_shapes():
    proofs = parse_external_proofs(
        {"proofs": [{"atom": "a", "tactic_script": "omega", "attempts": "2"}]}
    )
    assert proofs == [ExternalProof(atom="a", tactic_script="omega", attempts=2)]
    assert parse_external_proofs([{"atom": "b", "witness_lemma": "L"}]) == [
        ExternalProof(atom="b", witness_lemma="L")
    ]
    with pytest.raises(ValueError):
        parse_external_proofs({"proofs": [{"tactic_script": "omega"}]})


def test_render_body_and_provenance_are_deterministic():
    proof = ExternalProof(atom="a", tactic_script="\nintro h\n\n  omega\n", attempts=1)
    assert proof.render_body() == "  intro h\n\n    omega"
    assert proof.provenance() == {
        "source": AI_GENERATED_PROOF,
        "script_sha256": proof.script_sha256,
        "attempts": 1,
    }
    witness = ExternalProof(atom="a", witness_lemma="Std.foo")
    assert witness.render_body() == "  exact Std.foo"
    assert witness.provenance()["witness_lemma"] == "Std.foo"


def test_external_proof_replaces_only_the_proof_body():
    [atom] = collect_unknown_atoms(_cert([_unknown_atom()]))
    baseline = render_theorem(atom)
    apply_external_proofs(atom and [atom], [ExternalProof(atom="quintic_pos", tactic_script=GOOD_SCRIPT)])
    rendered = render_theorem(atom)
    header = (
        "theorem quintic_pos_correct (x : Int) (result : Int) "
        "(h_body : result = quinticPosResult x) :\n    (x > 0) → (result > 0) := by\n"
    )
    assert header in baseline and header in rendered
    assert "mumei_arith_deep" in baseline
    assert "mumei_arith_deep" not in rendered
    assert (
        f"  -- external_proof: source=ai_generated_proof sha256={atom.external_proof.script_sha256}\n"
        "  intro hx\n  subst h_body\n  unfold quinticPosResult\n  exact mul_pos hx hx\n"
    ) in rendered
    assert "sorry" not in rendered


def test_rejected_proof_is_never_rendered():
    [atom] = collect_unknown_atoms(_cert([_unknown_atom()]))
    rejections = apply_external_proofs(
        [atom], [ExternalProof(atom="quintic_pos", tactic_script="sorry")]
    )
    assert rejections.rejections == {"quintic_pos": "forbidden_token:sorry"}
    assert atom.external_proof is None
    assert atom.external_proof_rejection == "forbidden_token:sorry"
    assert "sorry" not in render_theorem(atom)


def test_module_key_scopes_the_proof_to_one_atom():
    [atom] = collect_unknown_atoms(_cert([_unknown_atom()]))
    apply_external_proofs(
        [atom],
        [ExternalProof(atom="quintic_pos", module_key="other/module", tactic_script="omega")],
    )
    assert atom.external_proof is None
    apply_external_proofs(
        [atom],
        [ExternalProof(atom="quintic_pos", module_key="std/quintic", tactic_script="omega")],
    )
    assert atom.external_proof is not None


def test_external_proof_does_not_hide_partial_statements():
    """An unfaithful statement stays partial even with a proof attached."""
    [atom] = collect_unknown_atoms(
        _cert([_unknown_atom(ensures="unknown_obligation(result, x)")])
    )
    assert atom.manual_lemma_reason is not None
    assert atom.is_partial_translation
    apply_external_proofs(
        [atom], [ExternalProof(atom="quintic_pos", tactic_script="omega")]
    )
    assert atom.ensures_translation.is_partial
    assert atom.is_partial_translation
    assert bridge._candidate_status(atom, ["quintic_pos_correct"], []) == "partial_translation"


def test_external_proof_supersedes_manual_lemma_only_after_a_real_build():
    [atom] = collect_unknown_atoms(_cert([_unknown_atom()]))
    atom.manual_lemma_reason = "template_catalog_miss"
    assert bridge._candidate_status(atom, ["quintic_pos_correct"], []) == (
        "manual_lemma_required"
    )
    apply_external_proofs(
        [atom], [ExternalProof(atom="quintic_pos", tactic_script=GOOD_SCRIPT, attempts=2)]
    )
    assert not is_search_eligible(atom, STAGE_RESIDUAL)
    assert not is_search_eligible(atom, STAGE_BUILD_FAILURE)
    # Build failure: no promotion, provenance says the AI proof was not used.
    failed = bridge._candidate_status(atom, ["quintic_pos_correct"], ["quintic_pos_correct"])
    assert failed == "manual_lemma_required"
    meta = bridge._candidate_metadata(atom, Path("generated"), "Generated", failed)
    assert meta["ai_proof_used"] is False
    assert meta["ai_proof_attempts"] == 2
    assert meta["manual_lemma_reason"] == "template_catalog_miss"
    assert meta["external_proof"]["source"] == AI_GENERATED_PROOF
    # Build success: promoted, manual reason kept as provenance only.
    ok = bridge._candidate_status(atom, ["quintic_pos_correct"], [])
    assert ok == "lean_verified"
    meta = bridge._candidate_metadata(atom, Path("generated"), "Generated", ok)
    assert meta["ai_proof_used"] is True
    assert meta.get("manual_lemma_reason") is None
    assert meta["external_proof"]["supersedes_manual_lemma_reason"] == "template_catalog_miss"
    assert meta["translator_version"] == bridge.TRANSLATOR_VERSION
    assert meta["bridge_lemma_hash"] == bridge.BRIDGE_LEMMA_HASH


def test_handwritten_witness_is_not_reported_as_ai_proof():
    [atom] = collect_unknown_atoms(_cert([_unknown_atom()]))
    apply_external_proofs(
        [atom],
        [ExternalProof(atom="quintic_pos", witness_lemma="Std.quintic_pos", source="handwritten_witness")],
    )
    meta = bridge._candidate_metadata(atom, Path("generated"), "Generated", "lean_verified")
    assert meta["ai_proof_used"] is False
    assert meta["external_proof"]["witness_lemma"] == "Std.quintic_pos"
    assert "ai_proof_attempts" not in meta


def test_rejected_proof_metadata_never_claims_ai_proof():
    [atom] = collect_unknown_atoms(_cert([_unknown_atom()]))
    apply_external_proofs([atom], [ExternalProof(atom="quintic_pos", tactic_script="admit")])
    meta = bridge._candidate_metadata(atom, Path("generated"), "Generated", "manual_lemma_required")
    assert meta["ai_proof_used"] is False
    assert meta["external_proof"] == {"rejected": "forbidden_token:admit"}
    assert "external_proof_rejected=forbidden_token:admit" in meta["diagnostics"]


def test_atoms_without_external_proofs_keep_their_metadata_shape():
    [atom] = collect_unknown_atoms(_cert([_unknown_atom()]))
    meta = bridge._candidate_metadata(atom, Path("generated"), "Generated", "lean_verified")
    assert "ai_proof_used" not in meta
    assert "external_proof" not in meta


def test_ingest_cli_injects_external_proofs(tmp_path: Path, capsys):
    cert = tmp_path / "cert.json"
    cert.write_text(json.dumps(_cert([_unknown_atom(), _unknown_atom("other")])))
    proofs = tmp_path / "proofs.json"
    proofs.write_text(
        json.dumps(
            {
                "proofs": [
                    {"atom": "quintic_pos", "tactic_script": GOOD_SCRIPT},
                    {"atom": "other", "tactic_script": "sorry"},
                ]
            }
        )
    )
    assert load_external_proofs(proofs)[0].atom == "quintic_pos"
    rc = ingest_main([str(cert), "--out", str(tmp_path / "gen"), "--external-proofs", str(proofs)])
    assert rc == 0
    err = capsys.readouterr().err
    assert "external proof for other rejected: forbidden_token:sorry" in err
    src = (tmp_path / "gen" / "Generated" / "Std" / "Quintic.lean").read_text()
    assert "exact mul_pos hx hx" in src
    assert "sorry" not in src
    assert src.count("mumei_arith_deep") == 1


def test_external_proof_supersession_survives_the_export_gate():
    """The lean-cert gate (``export_cert._atom_proved``) honours the
    ``supersedes_manual_lemma_reason`` provenance and promotes; without it the
    source ``manual_lemma_reason`` keeps blocking."""
    from export_cert import upgrade_certificate

    cert = _cert([_unknown_atom(manual_lemma_reason="template_catalog_miss")])
    [atom] = collect_unknown_atoms(cert)
    assert atom.manual_lemma_reason == "template_catalog_miss"
    apply_external_proofs(
        [atom], [ExternalProof(atom="quintic_pos", tactic_script=GOOD_SCRIPT)]
    )
    metadata = bridge._metadata_for_atoms(
        [atom], Path("generated"), "Generated", ["quintic_pos"], []
    )
    upgraded = upgrade_certificate(
        cert=cert,
        proved_atoms=["quintic_pos"],
        failed_atoms=[],
        lean_version="leanprover/lean4:v4.15.0",
        atom_metadata=metadata,
    )
    assert upgraded["atoms"][0]["z3_check_result"] == "lean_verified"
    assert upgraded["atoms"][0]["lean_metadata"]["ai_proof_used"] is True

    failed_metadata = bridge._metadata_for_atoms(
        [atom], Path("generated"), "Generated", ["quintic_pos"], ["quintic_pos"]
    )
    still_unknown = upgrade_certificate(
        cert=cert,
        proved_atoms=["quintic_pos"],
        failed_atoms=["quintic_pos"],
        lean_version="leanprover/lean4:v4.15.0",
        atom_metadata=failed_metadata,
    )
    assert still_unknown["atoms"][0]["z3_check_result"] == "unknown"


def test_duplicate_proofs_for_one_atom_are_rejected_regardless_of_order():
    from external_proof import REJECT_DUPLICATE

    good = ExternalProof(atom="quintic_pos", tactic_script=GOOD_SCRIPT)
    bad = ExternalProof(atom="quintic_pos", tactic_script="sorry")
    for proofs in ([good, bad], [bad, good]):
        [atom] = collect_unknown_atoms(_cert([_unknown_atom()]))
        applied = apply_external_proofs([atom], proofs)
        assert atom.external_proof is None
        assert atom.external_proof_rejection == REJECT_DUPLICATE
        assert applied.rejections == {"quintic_pos": REJECT_DUPLICATE}
        assert applied.unmatched(proofs) == []
        assert "external_proof" not in render_theorem(atom)


def test_unmatched_proofs_are_reported_not_dropped(tmp_path: Path, capsys):
    [atom] = collect_unknown_atoms(_cert([_unknown_atom()]))
    stray = ExternalProof(atom="misspelled", tactic_script=GOOD_SCRIPT)
    scoped = ExternalProof(
        atom="quintic_pos", tactic_script=GOOD_SCRIPT, module_key="std/other.mm"
    )
    applied = apply_external_proofs([atom], [stray, scoped])
    assert atom.external_proof is None
    assert applied.rejections == {}
    assert applied.unmatched([stray, scoped]) == [stray, scoped]

    cert = tmp_path / "cert.json"
    cert.write_text(json.dumps(_cert([_unknown_atom()])))
    proofs = tmp_path / "proofs.json"
    proofs.write_text(
        json.dumps({"proofs": [{"atom": "misspelled", "tactic_script": GOOD_SCRIPT}]})
    )
    assert ingest_main(
        [str(cert), "--out", str(tmp_path / "gen"), "--external-proofs", str(proofs)]
    ) == 0
    assert "external proof for misspelled matched no collected atom" in capsys.readouterr().err


def test_custom_bridge_proof_atoms_never_take_or_claim_an_external_proof():
    from external_proof import REJECT_CUSTOM_BRIDGE_PROOF
    from ingest_cert import external_proof_rendered

    fixture = Path(__file__).parent / "fixtures" / "guard_trace_demo.proof-cert.json"
    atoms = collect_unknown_atoms(json.loads(fixture.read_text()))
    target = next(atom for atom in atoms if atom.has_custom_bridge_proof)
    proof = ExternalProof(atom=target.name, tactic_script="simp")
    applied = apply_external_proofs(atoms, [proof], renders_override=external_proof_rendered)
    assert target.external_proof is None
    assert target.external_proof_rejection == REJECT_CUSTOM_BRIDGE_PROOF
    assert applied.rejections == {target.name: REJECT_CUSTOM_BRIDGE_PROOF}
    assert "external_proof" not in render_theorem(target)
    meta = bridge._candidate_metadata(target, Path("generated"), "Generated", "lean_verified")
    assert meta["ai_proof_used"] is False
    assert meta["external_proof"] == {"rejected": REJECT_CUSTOM_BRIDGE_PROOF}


def test_external_proof_not_rendered_is_rejected():
    """A renderer that ignores ``proof_body_override`` (known-witness delegate)
    must not leave the proof attached, otherwise ``ai_proof_used`` would be
    derived from text Lean never saw."""
    from external_proof import REJECT_NOT_RENDERED
    from ingest_cert import external_proof_rendered

    fixture = Path(__file__).parent / "fixtures" / "abs_saturating.proof-cert.json"
    atoms = collect_unknown_atoms(json.loads(fixture.read_text()))
    target = next(atom for atom in atoms if atom.name == "abs_saturating")
    assert not target.has_custom_bridge_proof
    proof = ExternalProof(atom="abs_saturating", tactic_script="omega")
    applied = apply_external_proofs(atoms, [proof], renders_override=external_proof_rendered)
    assert target.external_proof is None
    assert applied.rejections == {"abs_saturating": REJECT_NOT_RENDERED}
    assert "external_proof" not in render_theorem(target)
    # The generic renderer does carry the override, so it is confirmed there.
    [plain] = collect_unknown_atoms(_cert([_unknown_atom()]))
    apply_external_proofs(
        [plain],
        [ExternalProof(atom="quintic_pos", tactic_script=GOOD_SCRIPT)],
        renders_override=external_proof_rendered,
    )
    assert plain.external_proof is not None
    assert external_proof_rendered(plain)
