"""Unit coverage for the automatic tactic search (spec §12).

The live path that actually adopts a tactic and exports ``lean_verified`` is
covered by ``tests/test_lean_bridge_e2e.py``; these tests pin the offline
behaviour: eligibility, probe rendering, diagnostic classification, timeout
handling and the conservative fallbacks.
"""
from __future__ import annotations

import dataclasses
import json
import subprocess
from pathlib import Path

import pytest

from ingest_cert import collect_unknown_atoms, render_theorem
from tactic_search import (
    STAGE_BUILD_FAILURE,
    STAGE_RESIDUAL,
    TACTIC_CANDIDATES,
    apply_search_result,
    build_probe_module,
    candidate_tactic_block,
    is_search_eligible,
    search_tactic,
)


FIXTURES = Path(__file__).resolve().parent / "fixtures"
FF_DISTRIB_FIXTURE = (
    FIXTURES / "std_algebra_finite_field_ff_mul_add_distributive.proof-cert.json"
)
UNKNOWN_OBLIGATION_CERT = {
    "version": "1",
    "file": "residual.mm",
    "atoms": [
        {
            "name": "residual_obligation",
            "z3_check_result": "unknown",
            "z3_result_class": "unknown",
            "status": "unknown",
            "requires": "x > 0",
            "ensures": "unknown_obligation(result, x)",
            "body_expr": "{ x }",
            "body_summary": "{ x }",
        }
    ],
}


def _distrib_atom():
    payload = json.loads(FF_DISTRIB_FIXTURE.read_text())
    [atom] = collect_unknown_atoms(payload)
    return atom


def _residual_atom():
    [atom] = collect_unknown_atoms(UNKNOWN_OBLIGATION_CERT)
    return atom


def test_ladder_widens_the_arithmetic_prefix_without_reordering_it():
    """Spec §12.2: the new classes are appended, not interleaved."""
    ladder = [candidate_id for candidate_id, _ in TACTIC_CANDIDATES]
    assert ladder[:12] == [
        "omega",
        "linarith",
        "nlinarith",
        "positivity",
        "norm_num",
        "ring",
        "field_simp",
        "decide",
        "simp_arith",
        "mumei_field",
        "mumei_ff_mod",
        "aesop",
    ]
    assert ladder[12:] == ["tauto", "mumei_list", "mumei_order", "mumei_induct"]
    assert len(set(ladder)) == len(ladder)


def test_unfaithful_residual_atom_is_never_probed():
    """An untranslatable statement stays manual: probing it would be unsound."""
    atom = _residual_atom()
    assert atom.manual_lemma_reason == "unknown_obligation_requires_manual_lemma"
    assert atom.ensures_translation.is_partial is True
    assert atom.has_faithful_statement is False
    assert is_search_eligible(atom, STAGE_RESIDUAL) is False
    assert is_search_eligible(atom, STAGE_BUILD_FAILURE) is False


def test_faithful_residual_atom_is_eligible_for_the_residual_stage():
    atom = dataclasses.replace(
        _distrib_atom(),
        manual_lemma_reason="unknown_obligation_requires_manual_lemma",
    )
    assert atom.has_faithful_statement is True
    assert atom.is_partial_translation is True
    assert is_search_eligible(atom, STAGE_RESIDUAL) is True


def test_adopting_a_tactic_preserves_the_manual_lemma_reason():
    atom = dataclasses.replace(
        _distrib_atom(),
        manual_lemma_reason="unknown_obligation_requires_manual_lemma",
    )
    atom.auto_tactic = candidate_tactic_block("omega")
    # Provenance is never erased: only the *proof path* changes.
    assert atom.manual_lemma_reason == "unknown_obligation_requires_manual_lemma"
    assert atom.is_partial_translation is False
    rendered = render_theorem(atom)
    assert "(intros; omega)" in rendered
    assert "manual_lemma_required" not in rendered
    assert "sorry" not in rendered


def test_generic_fallback_atom_is_eligible_for_the_build_failure_stage():
    atom = _distrib_atom()
    assert atom.manual_lemma_reason is None
    assert is_search_eligible(atom, STAGE_RESIDUAL) is False
    assert is_search_eligible(atom, STAGE_BUILD_FAILURE) is True


def test_probe_module_covers_every_candidate_with_disjoint_spans():
    atom = _distrib_atom()
    source, spans = build_probe_module(atom)
    assert set(spans) == {candidate_id for candidate_id, _ in TACTIC_CANDIDATES}
    lines = source.splitlines()
    for candidate_id, tactic in TACTIC_CANDIDATES:
        start, end = spans[candidate_id]
        span = "\n".join(lines[start - 1 : end])
        assert f"({'intros; ' + tactic})" in span
        assert "set_option maxHeartbeats 400000 in" in span
    ordered = sorted(spans.values())
    for (_, end), (next_start, _) in zip(ordered, ordered[1:]):
        assert end < next_start


def test_search_reports_timeout_without_adopting(monkeypatch, tmp_path: Path):
    atom = _distrib_atom()

    def _timeout(*args, **kwargs):
        raise subprocess.TimeoutExpired(cmd="lake", timeout=kwargs["timeout"])

    monkeypatch.setattr(subprocess, "run", _timeout)
    result = search_tactic(
        atom,
        stage=STAGE_BUILD_FAILURE,
        probe_dir=tmp_path,
        timeout_s=0.5,
    )
    assert result.timed_out is True
    assert result.adopted_tactic is None
    assert result.exhausted is False
    assert apply_search_result(atom, result).auto_tactic is None


def test_search_without_lake_is_skipped(monkeypatch, tmp_path: Path):
    atom = _distrib_atom()

    def _missing(*args, **kwargs):
        raise FileNotFoundError("lake")

    monkeypatch.setattr(subprocess, "run", _missing)
    result = search_tactic(
        atom,
        stage=STAGE_BUILD_FAILURE,
        probe_dir=tmp_path,
        timeout_s=1.0,
    )
    assert result.skipped_reason == "lake_missing"
    assert result.adopted_tactic is None


def test_search_adopts_the_first_candidate_without_diagnostics(
    monkeypatch, tmp_path: Path
):
    atom = _distrib_atom()
    _, spans = build_probe_module(atom)
    failing = [
        candidate_id
        for candidate_id, _ in TACTIC_CANDIDATES
        if candidate_id != "ring"
    ]

    class _Proc:
        returncode = 1
        stdout = "\n".join(
            f"{tmp_path}/probe.lean:{spans[candidate_id][0] + 10}:2: "
            "error: tactic failed"
            for candidate_id in failing
        )
        stderr = ""

    monkeypatch.setattr(subprocess, "run", lambda *a, **k: _Proc())
    result = search_tactic(
        atom,
        stage=STAGE_BUILD_FAILURE,
        probe_dir=tmp_path,
        timeout_s=5.0,
    )
    assert result.adopted_tactic == "ring"
    assert result.exhausted is False
    assert apply_search_result(atom, result).auto_tactic == "(intros; ring1)"


def test_sorry_warning_disqualifies_a_candidate(monkeypatch, tmp_path: Path):
    atom = _distrib_atom()
    _, spans = build_probe_module(atom)

    class _Proc:
        returncode = 0
        stdout = "\n".join(
            f"{tmp_path}/probe.lean:{start + 10}:2: warning: declaration uses 'sorry'"
            for start, _ in spans.values()
        )
        stderr = ""

    monkeypatch.setattr(subprocess, "run", lambda *a, **k: _Proc())
    result = search_tactic(
        atom,
        stage=STAGE_BUILD_FAILURE,
        probe_dir=tmp_path,
        timeout_s=5.0,
    )
    assert result.adopted_tactic is None
    assert result.exhausted is True


def test_unknown_stage_is_rejected():
    with pytest.raises(ValueError):
        is_search_eligible(_distrib_atom(), "not_a_stage")
