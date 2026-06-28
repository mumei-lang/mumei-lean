"""Docs-level contract vocabulary regression tests for the Lean bridge."""
from __future__ import annotations

from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
DOCS_UNDER_CONTRACT = [
    REPO_ROOT / "README.md",
    REPO_ROOT / "docs" / "LEAN_HARNESS_CONTRACT.md",
    REPO_ROOT / "docs" / "INTEGRATION.md",
]
LEAN_CONTRACT_TERMS = [
    "lean_verified",
    "stale_translator",
    "translator_version",
    "bridge_lemma_hash",
]
NON_UNKNOWN_CASES = ["`sat`", "`unsat`", "parser failure", "parser failures"]


def _paragraphs(text: str) -> list[tuple[int, str]]:
    paragraphs: list[tuple[int, str]] = []
    current: list[str] = []
    start_line = 1
    for line_number, line in enumerate(text.splitlines(), 1):
        if line.strip():
            if not current:
                start_line = line_number
            current.append(line.strip())
        elif current:
            paragraphs.append((start_line, " ".join(current)))
            current = []
    if current:
        paragraphs.append((start_line, " ".join(current)))
    return paragraphs


def test_docs_define_lean_verified_with_current_translator_metadata() -> None:
    failures: list[str] = []
    for path in DOCS_UNDER_CONTRACT:
        text = path.read_text(encoding="utf-8")
        for term in LEAN_CONTRACT_TERMS:
            if term not in text:
                failures.append(f"{path.relative_to(REPO_ROOT)} is missing `{term}`")
        if "Z3 `unknown`" not in text and "z3 `unknown`" not in text.lower():
            failures.append(f"{path.relative_to(REPO_ROOT)} does not anchor Lean promotion to Z3 `unknown`")
    assert failures == []


def test_docs_do_not_route_sat_unsat_parser_failures_to_lean_fallback() -> None:
    failures: list[str] = []
    for path in DOCS_UNDER_CONTRACT:
        text = path.read_text(encoding="utf-8")
        for line_number, paragraph in _paragraphs(text):
            normalized = paragraph.lower()
            mentions_non_unknown = any(case in normalized for case in NON_UNKNOWN_CASES)
            mentions_lean_fallback = "lean" in normalized and any(
                word in normalized for word in ("fallback", "escalat", "promot")
            )
            denies_fallback = any(
                phrase in normalized
                for phrase in (
                    "must not",
                    "not ",
                    "only promoted lean path",
                    "z3 `unknown` only",
                    "only for z3 `unknown`",
                    "only when z3 returns `unknown`",
                    "not lean candidates",
                )
            )
            if mentions_non_unknown and mentions_lean_fallback and not denies_fallback:
                failures.append(
                    f"{path.relative_to(REPO_ROOT)}:{line_number} appears to describe sat/unsat/parser failure as Lean fallback"
                )
    assert failures == []
