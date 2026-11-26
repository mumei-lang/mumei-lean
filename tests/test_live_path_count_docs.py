"""Regression guard for the live generated theorem-path count contract."""

import re
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

    heading = re.search(
        r"^## Live Generated Theorem Paths \((\d+) total\)$",
        skill_reference,
        re.MULTILINE,
    )
    assert heading is not None
    assert int(heading.group(1)) == 20
    lines = skill_reference.splitlines()
    start = next(i for i, line in enumerate(lines) if line.startswith("1. `"))
    entries = []
    for line in lines[start:]:
        if re.match(r"^\d+\. `", line):
            entries.append(line)
        elif not line.strip():
            continue
        else:
            break
    assert len(entries) == 20
    assert [int(line.split(".", 1)[0]) for line in entries] == list(range(1, 21))
