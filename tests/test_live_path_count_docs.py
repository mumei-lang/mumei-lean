"""Regression guard for the live generated theorem-path count contract."""

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def test_live_generated_theorem_path_count_is_consistent_across_docs():
    contract = (ROOT / "docs" / "LEAN_HARNESS_CONTRACT.md").read_text()
    architecture = (ROOT / "docs" / "ARCHITECTURE.md").read_text()
    skill_reference = (
        ROOT / ".agents/skills/testing-mumei-lean-live-generated/references/live-generated-theorem-paths.md"
    ).read_text()

    for document in (contract, architecture, skill_reference):
        assert "twenty live generated theorem paths" in document
        assert "eighteen live generated theorem paths" not in document
