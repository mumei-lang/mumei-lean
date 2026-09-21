#!/usr/bin/env python3
"""Check and regenerate the Lean bridge contract constants."""
from __future__ import annotations

import argparse
import os
import re
import shutil
from pathlib import Path
from typing import Pattern

from expr_translator import bridge_lemma_hash_for, load_bridge_lemma_catalog

REPO_ROOT = Path(__file__).resolve().parents[1]
CATALOG = REPO_ROOT / "bridge_lemma_catalog.json"
TRANSLATOR_RE = re.compile(r'(?m)^TRANSLATOR_VERSION = "([^"]*)"$')
HASH_RE = re.compile(r'(?m)^BRIDGE_LEMMA_HASH = "([^"]*)"$')
CERT_TRANSLATOR_RE = re.compile(r'(?m)^def currentTranslatorVersion : String := "([^"]*)"$')
CERT_HASH_RE = re.compile(
    r'(?m)^def currentBridgeLemmaHash : String :=\s*\n\s*"([^"]*)"'
)
DOC_TRANSLATOR_RE = re.compile(
    r'(?m)Current contract constants are `translator_version = (\S+?)` and `bridge_lemma_hash = [0-9a-f]+`'
)
DOC_HASH_RE = re.compile(
    r'(?m)Current contract constants are `translator_version = \S+?` and `bridge_lemma_hash = ([0-9a-f]+)`'
)
RUST_TRANSLATOR_RE = re.compile(r'(?m)^pub const LEAN_TRANSLATOR_VERSION: &str = "([^"]*)";')
RUST_HASH_RE = re.compile(r'(?m)^pub const LEAN_BRIDGE_LEMMA_HASH: &str =\s*\n\s*"([^"]*)";')
JSON_TRANSLATOR_RE = re.compile(r'(?m)"translator_version"\s*:\s*"([^"]*)"')
JSON_HASH_RE = re.compile(r'(?m)"bridge_lemma_hash"\s*:\s*"([^"]*)"')
AGENT_TRANSLATOR_RE = re.compile(
    r'(?m)^_SOLIDITY_GUARD_TRACE_TRANSLATOR_VERSION = "([^"]*)"$'
)
AGENT_HASH_RE = re.compile(
    r'(?m)^_SOLIDITY_GUARD_TRACE_BRIDGE_LEMMA_HASH = "([^"]*)"$'
)


def _repo_arg(value: str | None, env_name: str, fallback: Path) -> Path | None:
    if value:
        candidate = Path(value).resolve()
        return candidate if candidate.exists() else None
    if os.environ.get(env_name):
        candidate = Path(os.environ[env_name]).resolve()
        return candidate if candidate.exists() else None
    return fallback if fallback.exists() else None


def _targets(repo_root: Path, translator_version: str, bridge_hash: str):
    return [
        (repo_root / "scripts/expr_translator.py", "translator_version", TRANSLATOR_RE, translator_version),
        (repo_root / "scripts/expr_translator.py", "bridge_lemma_hash", HASH_RE, bridge_hash),
        (repo_root / "scripts/export_cert.py", "translator_version", TRANSLATOR_RE, translator_version),
        (repo_root / "scripts/export_cert.py", "bridge_lemma_hash", HASH_RE, bridge_hash),
        (repo_root / "MumeiLean/CertWriter.lean", "translator_version", CERT_TRANSLATOR_RE, translator_version),
        (repo_root / "MumeiLean/CertWriter.lean", "bridge_lemma_hash", CERT_HASH_RE, bridge_hash),
    ] + [
        (repo_root / doc, "translator_version", DOC_TRANSLATOR_RE, translator_version)
        for doc in (
            "docs/LEAN_HARNESS_CONTRACT.md",
            "docs/LEAN_TRANSLATOR_SPEC.md",
            "docs/BRIDGE_HARNESS_SPEC.md",
            "docs/INTEGRATION.md",
        )
    ] + [
        (repo_root / doc, "bridge_lemma_hash", DOC_HASH_RE, bridge_hash)
        for doc in (
            "docs/LEAN_HARNESS_CONTRACT.md",
            "docs/LEAN_TRANSLATOR_SPEC.md",
            "docs/BRIDGE_HARNESS_SPEC.md",
            "docs/INTEGRATION.md",
        )
    ] + _fixture_targets(repo_root / "tests/fixtures", translator_version, bridge_hash)


def _fixture_targets(fixtures_dir: Path, translator_version: str, bridge_hash: str):
    targets = []
    for fixture in sorted(fixtures_dir.glob("*.json")):
        text = fixture.read_text(encoding="utf-8")
        if JSON_TRANSLATOR_RE.search(text):
            targets.append((fixture, "translator_version", JSON_TRANSLATOR_RE, translator_version))
        if JSON_HASH_RE.search(text):
            targets.append((fixture, "bridge_lemma_hash", JSON_HASH_RE, bridge_hash))
    return targets


def _sibling_targets(repo: Path, translator_version: str, bridge_hash: str, agent: bool):
    if agent:
        return [
            (repo / "agent/strategies/foreign_code_strategy_helpers.py", "translator_version", AGENT_TRANSLATOR_RE, translator_version),
            (repo / "agent/strategies/foreign_code_strategy_helpers.py", "bridge_lemma_hash", AGENT_HASH_RE, bridge_hash),
        ]
    return [
        (repo / "mumei-core/src/verification/types.rs", "translator_version", RUST_TRANSLATOR_RE, translator_version),
        (repo / "mumei-core/src/verification/types.rs", "bridge_lemma_hash", RUST_HASH_RE, bridge_hash),
        (repo / "tests/fixtures/proof-cert/verified_sample.proof-cert.json", "translator_version", JSON_TRANSLATOR_RE, translator_version),
        (repo / "tests/fixtures/proof-cert/verified_sample.proof-cert.json", "bridge_lemma_hash", JSON_HASH_RE, bridge_hash),
    ]


def _replace_target(
    path: Path,
    field: str,
    pattern: Pattern[str],
    expected: str,
    write: bool,
) -> list[str]:
    if not path.exists():
        return [f"{path}: target is missing"]
    text = path.read_text(encoding="utf-8")
    matches = list(pattern.finditer(text))
    if not matches:
        return [f"{path}: {field} anchor not found"]
    violations: list[str] = []
    for match in matches:
        old = match.group(1)
        if old != expected:
            violations.append(f"{path}: {field} is {old}, expected {expected}")
    if write and violations:
        text = pattern.sub(
            lambda match: match.group(0)[: match.start(1) - match.start(0)]
            + expected
            + match.group(0)[match.end(1) - match.start(0) :],
            text,
        )
        path.write_text(text, encoding="utf-8")
        for violation in violations:
            print(f"updated {violation}")
        return []
    return violations


def sync_contract_constants(
    *,
    write: bool = False,
    catalog_path: Path = CATALOG,
    repo_root: Path = REPO_ROOT,
    mumei_repo: Path | None = None,
    mumei_agent_repo: Path | None = None,
    require_siblings: bool = False,
) -> list[str]:
    catalog = load_bridge_lemma_catalog(catalog_path)
    translator_version = catalog["translator_version"]
    bridge_hash = bridge_lemma_hash_for(catalog["obligation_classes"])
    violations: list[str] = []
    targets = _targets(repo_root, translator_version, bridge_hash)
    for target in targets:
        violations.extend(_replace_target(*target, write=write))

    siblings = [
        (mumei_repo, False, "mumei"),
        (mumei_agent_repo, True, "mumei-agent"),
    ]
    for sibling, agent, name in siblings:
        if sibling is None:
            note = f"note: {name} sibling not found; skipped"
            if require_siblings:
                violations.append(note)
            else:
                print(note)
            continue
        for target in _sibling_targets(sibling, translator_version, bridge_hash, agent):
            violations.extend(_replace_target(*target, write=write))
        mirror = sibling / "schema/bridge_lemma_catalog.json"
        if write:
            mirror.parent.mkdir(parents=True, exist_ok=True)
            if not mirror.exists() or mirror.read_bytes() != catalog_path.read_bytes():
                shutil.copyfile(catalog_path, mirror)
                print(f"updated {mirror}: catalog mirror")
        elif not mirror.exists() or mirror.read_bytes() != catalog_path.read_bytes():
            violations.append(f"{mirror}: catalog mirror differs from {catalog_path}")
    return violations


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--check", action="store_true", help="check all targets (default)")
    mode.add_argument("--write", action="store_true", help="rewrite all targets")
    parser.add_argument("--catalog", type=Path, default=CATALOG)
    parser.add_argument("--mumei-repo", type=Path)
    parser.add_argument("--mumei-agent-repo", type=Path)
    parser.add_argument("--require-siblings", action="store_true")
    parser.add_argument("--print", action="store_true", dest="print_values")
    args = parser.parse_args(argv)
    catalog = load_bridge_lemma_catalog(args.catalog)
    bridge_hash = bridge_lemma_hash_for(catalog["obligation_classes"])
    if args.print_values:
        print(f"translator_version = {catalog['translator_version']}")
        print(f"bridge_lemma_hash = {bridge_hash}")
        return 0
    mumei = _repo_arg(args.mumei_repo, "MUMEI_REPO", REPO_ROOT.parent / "mumei")
    agent = _repo_arg(args.mumei_agent_repo, "MUMEI_AGENT_REPO", REPO_ROOT.parent / "mumei-agent")
    violations = sync_contract_constants(
        write=args.write,
        catalog_path=args.catalog,
        mumei_repo=mumei,
        mumei_agent_repo=agent,
        require_siblings=args.require_siblings,
    )
    if violations:
        for violation in violations:
            print(violation)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
