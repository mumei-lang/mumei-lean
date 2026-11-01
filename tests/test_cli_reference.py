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

UNRESOLVED_ENV_READ_ALLOWLIST = {
    ("scripts/sync_contract_constants.py", "_repo_arg"),
}


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


def _literal_strings(node: ast.AST, bindings: dict[str, set[str]]) -> set[str]:
    if isinstance(node, ast.Constant) and isinstance(node.value, str):
        return {node.value}
    if isinstance(node, ast.Name):
        return bindings.get(node.id, set())
    if isinstance(node, (ast.List, ast.Tuple, ast.Set)):
        values = set()
        for item in node.elts:
            values.update(_literal_strings(item, bindings))
        return values
    return set()


def _scan_environment_reads(
    source: str,
    path: str,
) -> tuple[set[str], list[tuple[str, int, str]]]:
    tree = ast.parse(source, filename=path)
    literal_bindings: dict[str, set[str]] = {}
    for node in ast.walk(tree):
        if isinstance(node, (ast.Assign, ast.AnnAssign)):
            value = node.value
            targets = node.targets if isinstance(node, ast.Assign) else [node.target]
            values = _literal_strings(value, literal_bindings)
            for target in targets:
                if isinstance(target, ast.Name) and values:
                    literal_bindings[target.id] = values
        elif isinstance(node, ast.For) and isinstance(node.target, ast.Name):
            values = _literal_strings(node.iter, literal_bindings)
            if values:
                literal_bindings[node.target.id] = values

    names: set[str] = set()
    unresolved: list[tuple[str, int, str]] = []

    class ReadVisitor(ast.NodeVisitor):
        function_stack: list[str] = []

        def _function_name(self) -> str:
            return self.function_stack[-1] if self.function_stack else "<module>"

        def _record_key(self, key: ast.AST, node: ast.AST) -> None:
            values = _literal_strings(key, literal_bindings)
            if values:
                names.update(values)
            else:
                unresolved.append((path, node.lineno, self._function_name()))

        def visit_FunctionDef(self, node: ast.FunctionDef) -> None:
            self.function_stack.append(node.name)
            self.generic_visit(node)
            self.function_stack.pop()

        visit_AsyncFunctionDef = visit_FunctionDef

        def visit_Call(self, node: ast.Call) -> None:
            function = node.func
            is_environment_get = (
                isinstance(function, ast.Attribute)
                and function.attr in {"get", "getenv"}
                and (
                    _is_os_environ(function.value)
                    or isinstance(function.value, ast.Name)
                    and function.value.id == "os"
                )
            ) or isinstance(function, ast.Name) and function.id == "getenv"
            if is_environment_get:
                key = (
                    node.args[0]
                    if node.args
                    else next(
                        (keyword.value for keyword in node.keywords if keyword.arg == "key"),
                        None,
                    )
                )
                if key is not None:
                    self._record_key(key, node)
            if (
                isinstance(function, ast.Name)
                and function.id == "_repo_arg"
                and len(node.args) > 1
            ):
                self._record_key(node.args[1], node)
            self.generic_visit(node)

        def visit_Subscript(self, node: ast.Subscript) -> None:
            if _is_os_environ(node.value):
                self._record_key(node.slice, node)
            self.generic_visit(node)

    visitor = ReadVisitor()
    visitor.visit(tree)
    return names, unresolved


def _assert_no_unresolved_environment_reads(
    unresolved: list[tuple[str, int, str]],
) -> None:
    found_allowlisted = {(path, function) for path, _, function in unresolved}
    assert UNRESOLVED_ENV_READ_ALLOWLIST <= found_allowlisted, (
        "Stale unresolved environment-read allowlist entries: "
        f"{sorted(UNRESOLVED_ENV_READ_ALLOWLIST - found_allowlisted)}"
    )
    unexpected = [
        (path, line, function)
        for path, line, function in unresolved
        if (path, function) not in UNRESOLVED_ENV_READ_ALLOWLIST
    ]
    assert not unexpected, (
        "Unresolved environment reads: "
        + ", ".join(f"{path}:{line} in {function}" for path, line, function in unexpected)
    )


def _environment_names_read(scripts_dir: Path) -> set[str]:
    environment_names = set()
    unresolved = []
    for path in scripts_dir.glob("*.py"):
        names, sites = _scan_environment_reads(
            path.read_text(encoding="utf-8"),
            path.relative_to(REPO_ROOT).as_posix(),
        )
        environment_names.update(names)
        unresolved.extend(sites)
    _assert_no_unresolved_environment_reads(unresolved)
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


def test_unresolved_environment_read_is_reported() -> None:
    names, unresolved = _scan_environment_reads(
        "import os\ndef helper(key): return os.environ.get(key)\n",
        "example.py",
    )
    assert names == set()
    assert unresolved == [("example.py", 2, "helper")]
    sync_path = REPO_ROOT / "scripts/sync_contract_constants.py"
    _, allowed_sites = _scan_environment_reads(
        sync_path.read_text(encoding="utf-8"),
        "scripts/sync_contract_constants.py",
    )
    with pytest.raises(AssertionError, match=r"example\.py:2 in helper"):
        _assert_no_unresolved_environment_reads([*allowed_sites, *unresolved])


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
