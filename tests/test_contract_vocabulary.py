"""Docs + code-surface contract vocabulary regression tests for the Lean bridge.

Coverage:
- Docs text: LEAN_CONTRACT_TERMS presence and sat/unsat routing guard.
- Code constants: TRANSLATOR_VERSION / BRIDGE_LEMMA_HASH in export_cert.py
  must match the pinned values in docs/LEAN_HARNESS_CONTRACT.md (bidirectional
  drift detection).
- Code-surface drift: docstrings, argparse help, and user-visible strings in
  bridge scripts must not introduce Lean vocabulary aliases.
"""
from __future__ import annotations

import ast
import re
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

# ---------------------------------------------------------------------------
# Code-surface constants: scripts whose contract constants must stay in sync
# with docs/LEAN_HARNESS_CONTRACT.md.
# ---------------------------------------------------------------------------
EXPORT_CERT_PATH = REPO_ROOT / "scripts" / "export_cert.py"
EXPR_TRANSLATOR_PATH = REPO_ROOT / "scripts" / "expr_translator.py"
HARNESS_CONTRACT_DOC = REPO_ROOT / "docs" / "LEAN_HARNESS_CONTRACT.md"

# Pinned contract constants (L2 safety net).  These literals are the single
# expected value for the bridge contract.  Any PR that bumps the translator
# version or bridge lemma hash (e.g. when a new backing lemma is added) MUST
# update these literals together with every constant-defining script and every
# pinned doc in the same diff — that is precisely what these tests enforce.
EXPECTED_TRANSLATOR_VERSION = "mumei-lean-translator-ir-v2"
EXPECTED_BRIDGE_LEMMA_HASH = (
    "fec31244e29b7d6bd4790b0a25bceb7fce6bdf8f0b18d74d1c0ccdec8ecdc49d"
)

# Every Python script that defines the contract constants as module globals.
CONSTANT_DEFINING_SCRIPTS = [EXPORT_CERT_PATH, EXPR_TRANSLATOR_PATH]

# Every doc that pins the contract constants in a `translator_version = ...` /
# `bridge_lemma_hash = ...` sentence.
PINNED_CONTRACT_DOCS = [
    REPO_ROOT / "docs" / "LEAN_HARNESS_CONTRACT.md",
    REPO_ROOT / "docs" / "LEAN_TRANSLATOR_SPEC.md",
    REPO_ROOT / "docs" / "BRIDGE_HARNESS_SPEC.md",
    REPO_ROOT / "docs" / "INTEGRATION.md",
]

# Python bridge scripts whose code surface (docstrings, argparse help,
# user-visible output strings) is checked for Lean vocabulary alias drift.
BRIDGE_SCRIPTS = [
    REPO_ROOT / "scripts" / "export_cert.py",
    REPO_ROOT / "scripts" / "bridge.py",
    REPO_ROOT / "scripts" / "ingest_cert.py",
    REPO_ROOT / "scripts" / "bridge_harness.py",
]

# Forbidden aliases for each canonical Lean contract term.  Only checked in
# key-like contexts to avoid false positives on ordinary English prose.
LEAN_FORBIDDEN_ALIASES: dict[str, list[str]] = {
    "lean_verified": ["lean_proved", "verified_by_lean", "lean_proven"],
    "stale_translator": ["translator_stale", "stale_bridge", "outdated_translator"],
    "translator_version": ["bridge_version", "version_translator", "translator_ver"],
    "bridge_lemma_hash": ["lemma_hash", "bridge_hash", "hash_bridge_lemma"],
}

# Regex for the pinned contract constants line in LEAN_HARNESS_CONTRACT.md.
# Values may be surrounded by backticks in markdown, so we strip non-alnum
# trailing characters and capture only the value body.
_DOC_TRANSLATOR_RE = re.compile(
    r"translator_version\s*=\s*([A-Za-z0-9_-]+)"
)
_DOC_BRIDGE_HASH_RE = re.compile(
    r"bridge_lemma_hash\s*=\s*([0-9a-fA-F]+)"
)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

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


def _extract_module_constants(path: Path) -> dict[str, str]:
    """Extract top-level string constant assignments from a Python file via AST.

    Handles both plain ``X = "..."`` and annotated ``X: str = "..."``.
    """
    source = path.read_text(encoding="utf-8")
    tree = ast.parse(source, filename=str(path))
    constants: dict[str, str] = {}
    for node in ast.iter_child_nodes(tree):
        if isinstance(node, ast.Assign):
            if len(node.targets) != 1:
                continue
            target = node.targets[0]
            if not isinstance(target, ast.Name):
                continue
            if isinstance(node.value, ast.Constant) and isinstance(node.value.value, str):
                constants[target.id] = node.value.value
        elif isinstance(node, ast.AnnAssign):
            target = node.target
            if not isinstance(target, ast.Name):
                continue
            if (
                node.value is not None
                and isinstance(node.value, ast.Constant)
                and isinstance(node.value.value, str)
            ):
                constants[target.id] = node.value.value
    return constants


def _extract_doc_pinned_values(path: Path) -> dict[str, str]:
    """Extract translator_version and bridge_lemma_hash from the contract doc."""
    text = path.read_text(encoding="utf-8")
    values: dict[str, str] = {}
    m = _DOC_TRANSLATOR_RE.search(text)
    if m:
        values["translator_version"] = m.group(1)
    m = _DOC_BRIDGE_HASH_RE.search(text)
    if m:
        values["bridge_lemma_hash"] = m.group(1)
    return values


def _find_all_doc_pinned_values(path: Path) -> dict[str, list[str]]:
    """Return every pinned translator_version / bridge_lemma_hash occurrence.

    Unlike ``_extract_doc_pinned_values`` (first match only), this collects all
    occurrences so a doc that repeats the pinned sentence cannot drift on a
    later line.
    """
    text = path.read_text(encoding="utf-8")
    return {
        "translator_version": _DOC_TRANSLATOR_RE.findall(text),
        "bridge_lemma_hash": _DOC_BRIDGE_HASH_RE.findall(text),
    }


def _is_key_context(line: str, alias: str) -> bool:
    """Return True if *alias* appears in a key-like context on *line*.

    Key-like contexts (matching mumei-demo ``_is_key_context``):
    - backtick-quoted: `alias`
    - JSON key style: "alias": or 'alias':
    - CONSTANT_NAME style: ALIAS (all-uppercase with underscores)
    - bare identifier in assignment: alias =
    """
    escaped = re.escape(alias)
    key_patterns = [
        re.compile(rf"`{escaped}`"),
        re.compile(rf'"\s*{escaped}\s*"\s*:'),
        re.compile(rf"'\s*{escaped}\s*'\s*:"),
        re.compile(rf"(?m)^\s*[-*]?\s*{escaped}\s*:"),
        re.compile(rf"\b{re.escape(alias.upper())}\b"),
        re.compile(rf"\b{escaped}\s*="),
    ]
    return any(p.search(line) for p in key_patterns)


def _collect_code_surface_strings(path: Path) -> list[tuple[int, str]]:
    """Collect user-visible string surfaces from a Python script.

    Returns (line_number, text) pairs for:
    - module/function/class docstrings
    - argparse ``help=`` keyword values
    - ``print(...)`` / ``sys.stderr`` string arguments
    """
    source = path.read_text(encoding="utf-8")
    tree = ast.parse(source, filename=str(path))
    surfaces: list[tuple[int, str]] = []

    for node in ast.walk(tree):
        # Docstrings
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef, ast.Module)):
            body = node.body
            if body and isinstance(body[0], ast.Expr) and isinstance(body[0].value, ast.Constant):
                val = body[0].value
                if isinstance(val.value, str):
                    surfaces.append((val.lineno, val.value))

        # argparse help= keyword arguments
        if isinstance(node, ast.Call):
            for kw in node.keywords:
                if kw.arg == "help" and isinstance(kw.value, ast.Constant) and isinstance(kw.value.value, str):
                    surfaces.append((kw.value.lineno, kw.value.value))

        # print(...) and sys.stderr.write(...) string literals
        if isinstance(node, ast.Call):
            func = node.func
            is_print = isinstance(func, ast.Name) and func.id == "print"
            is_stderr_write = (
                isinstance(func, ast.Attribute)
                and func.attr == "write"
            )
            if is_print or is_stderr_write:
                for arg in node.args:
                    if isinstance(arg, ast.Constant) and isinstance(arg.value, str):
                        surfaces.append((arg.lineno, arg.value))
                    elif isinstance(arg, ast.JoinedStr):
                        for val in arg.values:
                            if isinstance(val, ast.Constant) and isinstance(val.value, str):
                                surfaces.append((val.lineno, val.value))

    return surfaces


# ---------------------------------------------------------------------------
# Tests — docs text
# ---------------------------------------------------------------------------

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


# ---------------------------------------------------------------------------
# Tests — code constant ↔ document pinned value bidirectional drift
# ---------------------------------------------------------------------------

def test_code_constants_match_doc_pinned_values() -> None:
    """TRANSLATOR_VERSION and BRIDGE_LEMMA_HASH in export_cert.py must exactly
    match the values pinned in docs/LEAN_HARNESS_CONTRACT.md line 33.

    If either side changes independently, this test fails — ensuring
    bidirectional drift detection.
    """
    code_consts = _extract_module_constants(EXPORT_CERT_PATH)
    doc_values = _extract_doc_pinned_values(HARNESS_CONTRACT_DOC)

    failures: list[str] = []

    code_tv = code_consts.get("TRANSLATOR_VERSION")
    doc_tv = doc_values.get("translator_version")
    if code_tv is None:
        failures.append("export_cert.py is missing TRANSLATOR_VERSION constant")
    if doc_tv is None:
        failures.append("LEAN_HARNESS_CONTRACT.md is missing translator_version pinned value")
    if code_tv is not None and doc_tv is not None and code_tv != doc_tv:
        failures.append(
            f"TRANSLATOR_VERSION drift: code={code_tv!r} != doc={doc_tv!r}"
        )

    code_bh = code_consts.get("BRIDGE_LEMMA_HASH")
    doc_bh = doc_values.get("bridge_lemma_hash")
    if code_bh is None:
        failures.append("export_cert.py is missing BRIDGE_LEMMA_HASH constant")
    if doc_bh is None:
        failures.append("LEAN_HARNESS_CONTRACT.md is missing bridge_lemma_hash pinned value")
    if code_bh is not None and doc_bh is not None and code_bh != doc_bh:
        failures.append(
            f"BRIDGE_LEMMA_HASH drift: code={code_bh!r} != doc={doc_bh!r}"
        )

    code_lv = code_consts.get("LEAN_VERIFIED")
    if code_lv is None:
        failures.append("export_cert.py is missing LEAN_VERIFIED constant")
    elif code_lv != "lean_verified":
        failures.append(
            f"LEAN_VERIFIED value changed: {code_lv!r} != 'lean_verified'"
        )

    assert failures == [], "\n".join(failures)


def test_pinned_contract_constants_match_expected_literals() -> None:
    """L2 safety net: every constant-defining script and every pinned doc must
    equal the exact expected literals.

    ``test_code_constants_match_doc_pinned_values`` only checks that code and
    doc agree with *each other*; a coordinated typo would slip through.  This
    test additionally anchors both sides to a single expected literal and fans
    the check out across all constant-defining scripts (``export_cert.py``,
    ``expr_translator.py``) and all pinned docs.  A PR that intentionally bumps
    the translator version or bridge lemma hash must update these expected
    literals here in the same diff, which is the intended coupling with PR3.
    """
    failures: list[str] = []

    for path in CONSTANT_DEFINING_SCRIPTS:
        consts = _extract_module_constants(path)
        rel = path.relative_to(REPO_ROOT)
        tv = consts.get("TRANSLATOR_VERSION")
        bh = consts.get("BRIDGE_LEMMA_HASH")
        if tv != EXPECTED_TRANSLATOR_VERSION:
            failures.append(
                f"{rel}: TRANSLATOR_VERSION={tv!r} != expected "
                f"{EXPECTED_TRANSLATOR_VERSION!r}"
            )
        if bh != EXPECTED_BRIDGE_LEMMA_HASH:
            failures.append(
                f"{rel}: BRIDGE_LEMMA_HASH={bh!r} != expected "
                f"{EXPECTED_BRIDGE_LEMMA_HASH!r}"
            )

    for path in PINNED_CONTRACT_DOCS:
        if not path.exists():
            failures.append(f"{path.relative_to(REPO_ROOT)}: pinned doc missing")
            continue
        rel = path.relative_to(REPO_ROOT)
        found = _find_all_doc_pinned_values(path)
        tvs = found["translator_version"]
        bhs = found["bridge_lemma_hash"]
        if not tvs:
            failures.append(f"{rel}: missing pinned translator_version value")
        if not bhs:
            failures.append(f"{rel}: missing pinned bridge_lemma_hash value")
        for value in tvs:
            if value != EXPECTED_TRANSLATOR_VERSION:
                failures.append(
                    f"{rel}: pinned translator_version={value!r} != expected "
                    f"{EXPECTED_TRANSLATOR_VERSION!r}"
                )
        for value in bhs:
            if value != EXPECTED_BRIDGE_LEMMA_HASH:
                failures.append(
                    f"{rel}: pinned bridge_lemma_hash={value!r} != expected "
                    f"{EXPECTED_BRIDGE_LEMMA_HASH!r}"
                )

    assert failures == [], "\n".join(failures)


def test_constant_defining_scripts_agree_with_each_other() -> None:
    """export_cert.py and expr_translator.py must not diverge on the contract
    constants, since both feed the same certificate acceptance path."""
    values: dict[str, dict[str, str | None]] = {}
    for path in CONSTANT_DEFINING_SCRIPTS:
        consts = _extract_module_constants(path)
        values[path.relative_to(REPO_ROOT).as_posix()] = {
            "TRANSLATOR_VERSION": consts.get("TRANSLATOR_VERSION"),
            "BRIDGE_LEMMA_HASH": consts.get("BRIDGE_LEMMA_HASH"),
        }
    distinct_tv = {v["TRANSLATOR_VERSION"] for v in values.values()}
    distinct_bh = {v["BRIDGE_LEMMA_HASH"] for v in values.values()}
    assert len(distinct_tv) == 1, f"TRANSLATOR_VERSION diverges: {values}"
    assert len(distinct_bh) == 1, f"BRIDGE_LEMMA_HASH diverges: {values}"


# ---------------------------------------------------------------------------
# Tests — Lean vocabulary alias drift in Python bridge code surfaces
# ---------------------------------------------------------------------------

def test_bridge_code_surfaces_no_lean_vocabulary_alias_drift() -> None:
    """Docstrings, argparse help, and print strings in the bridge scripts must
    not introduce forbidden aliases for the four Lean contract terms.

    Only key-like contexts are checked to avoid false positives on ordinary
    English prose (e.g. "the bridge hash is computed from ...").
    """
    # Precompile word-boundary patterns for all forbidden aliases.
    alias_patterns: list[tuple[str, re.Pattern[str]]] = [
        (
            alias,
            re.compile(
                rf"(?<![A-Za-z0-9_]){re.escape(alias)}(?![A-Za-z0-9_])",
                re.IGNORECASE,
            ),
        )
        for aliases in LEAN_FORBIDDEN_ALIASES.values()
        for alias in aliases
    ]

    failures: list[str] = []
    for script_path in BRIDGE_SCRIPTS:
        if not script_path.exists():
            failures.append(f"{script_path.relative_to(REPO_ROOT)}: bridge script missing")
            continue
        rel = script_path.relative_to(REPO_ROOT)
        surfaces = _collect_code_surface_strings(script_path)
        for lineno, text in surfaces:
            for alias, pattern in alias_patterns:
                for line in text.splitlines():
                    if not pattern.search(line):
                        continue
                    if _is_key_context(line, alias):
                        failures.append(
                            f"{rel}:{lineno}: forbidden alias `{alias}` "
                            f"in key-like context"
                        )
                        break
    assert failures == [], "\n".join(failures)
