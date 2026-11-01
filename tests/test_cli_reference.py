from __future__ import annotations

import ast
import re
from pathlib import Path

import pytest

from scripts.cli_reference import (
    CLI_SCRIPTS,
    ENVIRONMENT_VARIABLES,
    INTERNAL_ENV_ALLOWLIST,
    REPO_ROOT,
    capture_parsers,
    render_cli_reference,
)
from scripts.gen_cli_reference import main as generate_main


def test_committed_reference_matches_render() -> None:
    assert (REPO_ROOT / "docs/CLI_REFERENCE.md").read_text() == render_cli_reference()


def test_check_rejects_tampered_copy(tmp_path, capsys) -> None:
    copy = tmp_path / "CLI_REFERENCE.md"
    copy.write_text("tampered")
    assert generate_main(["--check"], reference_path=copy) == 1
    assert "out of date" in capsys.readouterr().err
    assert copy.read_text() == "tampered"


def test_every_argparse_script_is_referenced() -> None:
    scripts_dir = REPO_ROOT / "scripts"
    discovered = set()
    for path in scripts_dir.glob("*.py"):
        tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
        if any(
            isinstance(node, ast.Call)
            and (
                isinstance(node.func, ast.Name)
                and node.func.id == "ArgumentParser"
                or isinstance(node.func, ast.Attribute)
                and node.func.attr == "ArgumentParser"
            )
            for node in ast.walk(tree)
        ):
            discovered.add(path.relative_to(REPO_ROOT).as_posix())
    assert discovered == {script_path for script_path, _ in CLI_SCRIPTS}


def _is_os_environ(node: ast.AST) -> bool:
    return (
        isinstance(node, ast.Attribute)
        and node.attr == "environ"
        and isinstance(node.value, ast.Name)
        and node.value.id == "os"
    )


def _environment_names_read(scripts_dir: Path) -> set[str]:
    environment_names = set()
    for path in scripts_dir.glob("*.py"):
        tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
        literal_assignments = {}
        for node in ast.walk(tree):
            if not isinstance(node, (ast.Assign, ast.AnnAssign)):
                continue
            value = node.value
            targets = node.targets if isinstance(node, ast.Assign) else [node.target]
            if not isinstance(value, (ast.List, ast.Tuple, ast.Set)):
                continue
            values = {
                item.value
                for item in value.elts
                if isinstance(item, ast.Constant) and isinstance(item.value, str)
            }
            for target in targets:
                if isinstance(target, ast.Name):
                    literal_assignments[target.id] = values

        for node in ast.walk(tree):
            if isinstance(node, ast.Call):
                function = node.func
                is_get = (
                    isinstance(function, ast.Attribute)
                    and function.attr in {"get", "getenv"}
                    and (
                        _is_os_environ(function.value)
                        or isinstance(function.value, ast.Name)
                        and function.value.id == "os"
                    )
                ) or isinstance(function, ast.Name) and function.id == "getenv"
                if is_get and node.args:
                    value = node.args[0]
                    if isinstance(value, ast.Constant) and isinstance(value.value, str):
                        environment_names.add(value.value)
                    elif isinstance(value, ast.Name):
                        environment_names.update(literal_assignments.get(value.id, set()))
                if (
                    isinstance(function, ast.Name)
                    and function.id == "_repo_arg"
                    and len(node.args) > 1
                    and isinstance(node.args[1], ast.Constant)
                    and isinstance(node.args[1].value, str)
                ):
                    environment_names.add(node.args[1].value)
            elif isinstance(node, ast.Subscript) and _is_os_environ(node.value):
                index = node.slice
                if isinstance(index, ast.Constant) and isinstance(index.value, str):
                    environment_names.add(index.value)
    return environment_names


def _assert_environment_coverage(
    environment_names: set[str],
    registered: set[str],
    internal: set[str],
) -> None:
    classified = registered | internal
    assert environment_names <= classified, (
        f"Unclassified environment reads: {sorted(environment_names - classified)}"
    )
    assert classified <= environment_names, (
        f"Stale environment declarations: {sorted(classified - environment_names)}"
    )


def test_environment_reads_are_documented_or_internal() -> None:
    registered = {name for name, _, _ in ENVIRONMENT_VARIABLES}
    _assert_environment_coverage(
        _environment_names_read(REPO_ROOT / "scripts"),
        registered,
        set(INTERNAL_ENV_ALLOWLIST),
    )


def test_environment_coverage_rejects_stale_allowlist_entries() -> None:
    with pytest.raises(AssertionError, match="Stale environment declarations"):
        _assert_environment_coverage(
            {"MUMEI_REPO", "MUMEI_AGENT_REPO"},
            {"MUMEI_REPO", "MUMEI_AGENT_REPO"},
            {"FAKE_INTERNAL"},
        )


def test_parser_option_strings_match_golden_lists() -> None:
    expected = {
        "scripts/bridge.py": [
            "--cert",
            "--bundle",
            "--escalation-bundle",
            "--ingest-bundle",
            "--scan-unknown",
            "--out-dir",
            "--module-prefix",
            "--lean-cert-out",
            "--summary-json",
            "--lean-version",
            "--no-build",
            "--dual-check",
            "--ci-mode",
            "--no-export",
            "--no-tactic-search",
            "--tactic-search-history",
            "--no-tactic-search-history",
            "--record-tactic-search-history",
            "--tactic-search-timeout",
            "--failure-report",
            "--external-proofs",
            "--repo-dir",
        ],
        "scripts/check_authorization_model.py": ["--out-dir"],
        "scripts/export_cert.py": [
            "--input-cert",
            "--build-log",
            "--proved-atoms",
            "--lean-version",
            "--out",
        ],
        "scripts/ingest_cert.py": [
            "--bundle",
            "--out",
            "--module-prefix",
            "--print-summary",
            "--external-proofs",
        ],
        "scripts/lean_to_executable.py": [
            "--project-dir",
            "--module",
            "--target",
            "--out-dir",
            "--cert",
            "--binary-name",
            "--lake",
            "--run-args",
            "--run-timeout",
        ],
        "scripts/sync_contract_constants.py": [
            "--check",
            "--write",
            "--catalog",
            "--mumei-repo",
            "--mumei-agent-repo",
            "--require-siblings",
            "--print",
        ],
    }
    for script_path, parser in capture_parsers():
        option_strings = [
            option
            for action in parser._actions
            if action.option_strings and action.dest != "help"
            for option in action.option_strings
        ]
        assert option_strings == expected[script_path]
    bridge_actions = [
        action
        for action in capture_parsers()[0][1]._actions
        if action.option_strings and action.dest != "help"
    ]
    assert len(bridge_actions) == 21


def test_mutually_exclusive_groups_include_required_status() -> None:
    rendered = render_cli_reference()
    assert (
        "| `--cert`, `--bundle`, `--escalation-bundle`, "
        "`--ingest-bundle`, `--scan-unknown` | yes |"
    ) in rendered
    assert "| `--check`, `--write` | no |" in rendered


def test_reference_contains_no_absolute_checkout_paths() -> None:
    rendered = render_cli_reference()
    assert str(REPO_ROOT) not in rendered
    assert re.search(r"(?m)(?:^|\s)/(?:home|tmp|workspace|Users)/", rendered) is None
