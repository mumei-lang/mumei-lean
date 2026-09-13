"""Structured, atom-level build failure JSON (B-3) from ``export_cert``."""
from __future__ import annotations

import json
from pathlib import Path

import pytest

import bridge
from export_cert import (
    FAILURE_KIND_IMPORT_ERROR,
    FAILURE_KIND_OTHER,
    FAILURE_KIND_SORRY,
    FAILURE_KIND_TYPE_MISMATCH,
    FAILURE_KIND_UNKNOWN_IDENTIFIER,
    FAILURE_KIND_UNSOLVED_GOALS,
    _failed_theorem_attributions,
    _has_unattributable_failures,
    build_failure_report,
    classify_failure_kind,
    structured_build_failures,
)
from ingest_cert import collect_unknown_atoms, write_modules

FIXTURES = Path(__file__).resolve().parent / "fixtures"
LOGS = FIXTURES / "build_logs"
QUINTIC_CERT = FIXTURES / "std_quintic_external_proof.proof-cert.json"


@pytest.fixture
def source_root(tmp_path: Path) -> Path:
    """Render the quintic fixture so log paths resolve to real theorem sources."""
    payload = json.loads(QUINTIC_CERT.read_text())
    write_modules(collect_unknown_atoms(payload), tmp_path / "generated", "Generated")
    return tmp_path


@pytest.mark.parametrize(
    ("message", "kind"),
    [
        ("unsolved goals", FAILURE_KIND_UNSOLVED_GOALS),
        ("type mismatch", FAILURE_KIND_TYPE_MISMATCH),
        ("application type mismatch", FAILURE_KIND_TYPE_MISMATCH),
        ("failed to synthesize\n  Singleton ℤ ℤ", FAILURE_KIND_TYPE_MISMATCH),
        ("unknown module prefix 'Foo'", FAILURE_KIND_IMPORT_ERROR),
        ("object file './.lake/build/lib/Foo.olean' of module Foo does not exist", FAILURE_KIND_IMPORT_ERROR),
        ("declaration uses 'sorry'", FAILURE_KIND_SORRY),
        ("unknown identifier 'Std.Quintic.no_such_lemma'", FAILURE_KIND_UNKNOWN_IDENTIFIER),
        ("linarith failed to find a contradiction", FAILURE_KIND_OTHER),
    ],
)
def test_classify_failure_kind(message: str, kind: str):
    assert classify_failure_kind(message) == kind


@pytest.mark.parametrize(
    ("log_name", "kind", "line", "column"),
    [
        ("quintic_unsolved_goals.log", FAILURE_KIND_UNSOLVED_GOALS, 27, 30),
        ("quintic_type_mismatch.log", FAILURE_KIND_TYPE_MISMATCH, 30, 2),
    ],
)
def test_atom_level_failures_are_attributed(
    source_root: Path, log_name: str, kind: str, line: int, column: int
):
    log = (LOGS / log_name).read_text()
    report = build_failure_report(log, source_root=source_root)
    assert report["unattributed"] == []
    assert report["failures"] == [
        {
            "atom": "quintic_pos",
            "file": "./././generated/Generated/Std/Quintic.lean",
            "line": line,
            "column": column,
            "kind": kind,
            "message": report["failures"][0]["message"],
        }
    ]
    assert report["failures"][0]["message"].startswith(kind.replace("_", " "))
    # Same attribution the promotion gate uses.
    assert _failed_theorem_attributions(log, source_root=source_root) == [
        ("./././generated/Generated/Std/Quintic.lean", "quintic_pos")
    ]


def test_import_error_is_file_level_and_unattributed(source_root: Path):
    log = (LOGS / "quintic_import_error.log").read_text()
    report = build_failure_report(log, source_root=source_root)
    assert report["failures"] == []
    assert [(e["kind"], e["atom"], e["line"]) for e in report["unattributed"]] == [
        (FAILURE_KIND_IMPORT_ERROR, None, 2)
    ]
    assert _has_unattributable_failures(log, source_root=source_root)


def test_lake_infrastructure_lines_are_not_failures():
    log = "error: Lean exited with code 1\nerror: build failed\n"
    assert structured_build_failures(log) == []


def test_structured_json_is_deterministic(source_root: Path):
    """Identical logs → byte-identical JSON, independent of line order noise."""
    logs = [path.read_text() for path in sorted(LOGS.glob("quintic_*.log"))]
    combined = "\n".join(logs)
    first = json.dumps(build_failure_report(combined, source_root=source_root), sort_keys=True)
    second = json.dumps(build_failure_report(combined, source_root=source_root), sort_keys=True)
    assert first == second
    # Reversing the order of the concatenated logs must not change the output.
    reversed_combined = "\n".join(reversed(logs))
    third = json.dumps(build_failure_report(reversed_combined, source_root=source_root), sort_keys=True)
    assert first == third
    # Duplicated diagnostics collapse to one entry.
    duplicated = combined + "\n" + combined
    fourth = json.dumps(build_failure_report(duplicated, source_root=source_root), sort_keys=True)
    assert first == fourth
    payload = json.loads(first)
    assert [e["kind"] for e in payload["failures"]] == [
        FAILURE_KIND_UNSOLVED_GOALS,
        FAILURE_KIND_TYPE_MISMATCH,
    ]
    assert [e["kind"] for e in payload["unattributed"]] == [FAILURE_KIND_IMPORT_ERROR]


def test_metadata_carries_build_failures_only_for_failed_atoms(source_root: Path):
    [atom] = collect_unknown_atoms(json.loads(QUINTIC_CERT.read_text()))
    log = (LOGS / "quintic_unsolved_goals.log").read_text()
    failures = build_failure_report(log, source_root=source_root)["failures"]
    failed = bridge._metadata_for_atoms(
        [atom], Path("generated"), "Generated", ["quintic_pos"], ["quintic_pos"],
        build_failures=failures,
    )["quintic_pos"]
    assert failed["status"] == "manual_lemma_required"
    assert failed["build_failures"] == failures
    assert "build_failure=unsolved_goals" in failed["diagnostics"]
    proved = bridge._metadata_for_atoms(
        [atom], Path("generated"), "Generated", ["quintic_pos"], [],
        build_failures=failures,
    )["quintic_pos"]
    assert proved["status"] == "lean_verified"
    assert "build_failures" not in proved
