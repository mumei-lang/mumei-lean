"""Coverage for the learned candidate order of the tactic search (spec §12.5).

Learning is only allowed to *permute* the ladder, so these tests pin the three
properties that make the permutation safe: it is a permutation, it is a pure
function of the pinned artifact, and a malformed artifact learns nothing.
"""
from __future__ import annotations

import json
import subprocess
from pathlib import Path

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
