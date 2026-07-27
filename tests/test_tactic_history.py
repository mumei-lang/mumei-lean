"""Coverage for the learned candidate order of the tactic search (spec §12.5).

Learning is only allowed to *permute* the ladder, so these tests pin the three
properties that make the permutation safe: it is a permutation, it is a pure
function of the pinned artifact, and a malformed artifact learns nothing.
"""
from __future__ import annotations

import json
import subprocess
from pathlib import Path

from bridge import (
    _atom_key,
    _record_tactic_search_history,
    _run_tactic_search_stage,
)
from ingest_cert import collect_unknown_atoms
from tactic_history import (
    HISTORY_PATH,
    HISTORY_SCHEMA,
    TacticSearchHistory,
    load_history,
    save_history,
)
from tactic_search import (
    STAGE_BUILD_FAILURE,
    STAGE_RESIDUAL,
    TACTIC_CANDIDATES,
    TacticSearchResult,
    ladder_for,
    obligation_class_of,
    search_tactic,
)

FIXTURES = Path(__file__).resolve().parent / "fixtures"
FF_DISTRIB_FIXTURE = (
    FIXTURES / "std_algebra_finite_field_ff_mul_add_distributive.proof-cert.json"
)
GUARD_COLLAPSE_FIXTURE = (
    FIXTURES / "std_core_predicates_guard_collapse.proof-cert.json"
)


def _atom(fixture: Path):
    [atom] = collect_unknown_atoms(json.loads(fixture.read_text()))
    return atom


def _history(*entries: dict) -> TacticSearchHistory:
    history = TacticSearchHistory()
    for entry in entries:
        history.record_success(
            obligation_class=entry["obligation_class"],
            stage=entry["stage"],
            candidate=entry["candidate"],
        )
    return history


def test_pinned_history_matches_the_schema_and_the_current_ladder():
    payload = json.loads(HISTORY_PATH.read_text())
    assert payload["schema"] == HISTORY_SCHEMA
    known = {candidate_id for candidate_id, _ in TACTIC_CANDIDATES}
    assert payload["entries"]
    for entry in payload["entries"]:
        assert entry["candidate"] in known
        assert entry["stage"] in (STAGE_RESIDUAL, STAGE_BUILD_FAILURE)
        assert entry["successes"] >= 1


def test_learned_order_promotes_the_recorded_candidate_of_that_class():
    atom = _atom(FF_DISTRIB_FIXTURE)
    history = _history(
        {
            "obligation_class": obligation_class_of(atom),
            "stage": STAGE_BUILD_FAILURE,
            "candidate": "mumei_ff_mod",
        }
    )
    ladder = ladder_for(atom, stage=STAGE_BUILD_FAILURE, history=history)
    assert ladder[0][0] == "mumei_ff_mod"


def test_learned_order_is_a_permutation_that_keeps_ties_in_ladder_order():
    atom = _atom(FF_DISTRIB_FIXTURE)
    history = _history(
        {
            "obligation_class": obligation_class_of(atom),
            "stage": STAGE_BUILD_FAILURE,
            "candidate": "mumei_ff_mod",
        }
    )
    ladder = ladder_for(atom, stage=STAGE_BUILD_FAILURE, history=history)
    assert sorted(ladder) == sorted(TACTIC_CANDIDATES)
    tail = [candidate_id for candidate_id, _ in ladder[1:]]
    assert tail == [
        candidate_id
        for candidate_id, _ in TACTIC_CANDIDATES
        if candidate_id != "mumei_ff_mod"
    ]


def test_learning_is_scoped_to_the_obligation_class_and_stage():
    atom = _atom(FF_DISTRIB_FIXTURE)
    history = _history(
        {
            "obligation_class": "propositional",
            "stage": STAGE_BUILD_FAILURE,
            "candidate": "tauto",
        },
        {
            "obligation_class": obligation_class_of(atom),
            "stage": STAGE_RESIDUAL,
            "candidate": "aesop",
        },
    )
    ladder = ladder_for(atom, stage=STAGE_BUILD_FAILURE, history=history)
    assert ladder == TACTIC_CANDIDATES


def test_unknown_recorded_candidate_is_ignored():
    atom = _atom(GUARD_COLLAPSE_FIXTURE)
    history = _history(
        {
            "obligation_class": obligation_class_of(atom),
            "stage": STAGE_BUILD_FAILURE,
            "candidate": "a_tactic_that_left_the_ladder",
        }
    )
    assert ladder_for(atom, stage=STAGE_BUILD_FAILURE, history=history) == (
        TACTIC_CANDIDATES
    )


def test_missing_or_malformed_history_learns_nothing(tmp_path: Path):
    missing = tmp_path / "absent.json"
    assert load_history(missing).is_empty

    not_json = tmp_path / "broken.json"
    not_json.write_text("{not json", encoding="utf-8")
    assert load_history(not_json).is_empty

    wrong_schema = tmp_path / "wrong.json"
    wrong_schema.write_text(json.dumps({"schema": "other/v9", "entries": []}))
    assert load_history(wrong_schema).is_empty

    invalid_entries = tmp_path / "invalid.json"
    invalid_entries.write_text(
        json.dumps(
            {
                "schema": HISTORY_SCHEMA,
                "entries": [
                    "not an object",
                    {"candidate": "omega"},
                    {"candidate": "omega", "stage": STAGE_RESIDUAL, "successes": 0},
                    {"candidate": 7, "stage": STAGE_RESIDUAL, "successes": 3},
                ],
            }
        )
    )
    assert load_history(invalid_entries).is_empty


def test_history_round_trip_is_canonical_and_fingerprinted(tmp_path: Path):
    history = _history(
        {
            "obligation_class": "propositional",
            "stage": STAGE_BUILD_FAILURE,
            "candidate": "tauto",
        },
        {
            "obligation_class": "finite_field",
            "stage": STAGE_BUILD_FAILURE,
            "candidate": "mumei_ff_mod",
        },
    )
    path = save_history(history, tmp_path / "history.json")
    payload = json.loads(path.read_text())
    assert [entry["obligation_class"] for entry in payload["entries"]] == [
        "finite_field",
        "propositional",
    ]
    reloaded = load_history(path)
    assert reloaded.fingerprint == history.fingerprint
    assert reloaded.to_payload() == history.to_payload()


def test_search_records_the_ranking_it_used(monkeypatch, tmp_path: Path):
    atom = _atom(FF_DISTRIB_FIXTURE)
    history = _history(
        {
            "obligation_class": obligation_class_of(atom),
            "stage": STAGE_BUILD_FAILURE,
            "candidate": "mumei_ff_mod",
        }
    )
    save_history(history, tmp_path / "history.json")

    class _Proc:
        returncode = 0
        stdout = ""
        stderr = ""

    monkeypatch.setattr(subprocess, "run", lambda *a, **k: _Proc())
    result = search_tactic(
        atom,
        stage=STAGE_BUILD_FAILURE,
        probe_dir=tmp_path,
        timeout_s=5.0,
        history=history,
    )
    assert result.adopted_tactic == "mumei_ff_mod"
    assert result.candidates_tried == ["mumei_ff_mod"]
    assert result.history_ranked is True
    assert result.history_fingerprint == history.fingerprint
    assert result.as_metadata()["history_fingerprint"] == history.fingerprint


def test_search_without_history_probes_the_declared_ladder(monkeypatch, tmp_path: Path):
    atom = _atom(FF_DISTRIB_FIXTURE)

    class _Proc:
        returncode = 0
        stdout = ""
        stderr = ""

    monkeypatch.setattr(subprocess, "run", lambda *a, **k: _Proc())
    result = search_tactic(
        atom,
        stage=STAGE_BUILD_FAILURE,
        probe_dir=tmp_path,
        timeout_s=5.0,
    )
    assert result.adopted_tactic == TACTIC_CANDIDATES[0][0]
    assert result.history_ranked is False
    assert result.history_fingerprint is None


def test_history_ranked_is_false_when_this_obligation_was_not_reordered(
    monkeypatch, tmp_path: Path
):
    """Spec §12.4: the flag reports a ranking, not the mere existence of one."""
    atom = _atom(FF_DISTRIB_FIXTURE)
    history = _history(
        {
            "obligation_class": "propositional",
            "stage": STAGE_BUILD_FAILURE,
            "candidate": "tauto",
        }
    )
    assert not history.is_empty

    class _Proc:
        returncode = 0
        stdout = ""
        stderr = ""

    monkeypatch.setattr(subprocess, "run", lambda *a, **k: _Proc())
    result = search_tactic(
        atom,
        stage=STAGE_BUILD_FAILURE,
        probe_dir=tmp_path,
        timeout_s=5.0,
        history=history,
    )
    assert result.adopted_tactic == TACTIC_CANDIDATES[0][0]
    assert result.history_ranked is False
    assert result.history_fingerprint is None


def _stage_run(atom, history, path: Path, monkeypatch, capsys) -> str:
    class _Proc:
        returncode = 0
        stdout = ""
        stderr = ""

    monkeypatch.setattr(subprocess, "run", lambda *a, **k: _Proc())
    _run_tactic_search_stage(
        [atom],
        STAGE_BUILD_FAILURE,
        lake_cmd=["lake"],
        timeout_s=5.0,
        results={},
        repo_dir=path,
        history=history,
        history_path=path / "history.json",
    )
    return capsys.readouterr().out


def test_ranking_is_announced_only_when_an_obligation_was_reordered(
    monkeypatch, tmp_path: Path, capsys
):
    """The log must not claim a ranking the search did not apply."""
    unrelated = _history(
        {
            "obligation_class": "finite_field",
            "stage": STAGE_BUILD_FAILURE,
            "candidate": "mumei_ff_mod",
        }
    )
    assert not unrelated.is_empty
    assert "ladder ranked by" not in _stage_run(
        _atom(GUARD_COLLAPSE_FIXTURE), unrelated, tmp_path, monkeypatch, capsys
    )

    atom = _atom(GUARD_COLLAPSE_FIXTURE)
    applicable = _history(
        {
            "obligation_class": obligation_class_of(atom),
            "stage": STAGE_BUILD_FAILURE,
            "candidate": "tauto",
        }
    )
    out = _stage_run(atom, applicable, tmp_path, monkeypatch, capsys)
    assert "ladder ranked by" in out
    assert str(tmp_path / "history.json") in out


def test_recording_merges_into_the_artifact_instead_of_replacing_it(tmp_path: Path):
    """Spec §12.5 rule 4: recording is additive, never a truncating rewrite."""
    atom = _atom(GUARD_COLLAPSE_FIXTURE)
    path = save_history(
        _history(
            {
                "obligation_class": "finite_field",
                "stage": STAGE_BUILD_FAILURE,
                "candidate": "mumei_ff_mod",
            }
        ),
        tmp_path / "history.json",
    )
    result = TacticSearchResult(
        atom_name=atom.name,
        stage=STAGE_BUILD_FAILURE,
        adopted_tactic="tauto",
        candidates_tried=["tauto"],
        search_time_s=0.1,
        exhausted=False,
        timed_out=False,
    )
    # A run that probed the declared order (``--no-tactic-search-history``)
    # still merges its successes into the pinned artifact.
    _record_tactic_search_history(
        history_path=path,
        atoms_per_payload=[[atom]],
        failed_per_payload=[[]],
        results={_atom_key(atom): result},
    )
    merged = load_history(path)
    assert merged.successes[("finite_field", STAGE_BUILD_FAILURE)] == {
        "mumei_ff_mod": 1
    }
    assert merged.successes[
        (obligation_class_of(atom), STAGE_BUILD_FAILURE)
    ] == {"tauto": 1}
