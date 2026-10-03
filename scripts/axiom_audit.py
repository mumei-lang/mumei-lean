"""Audit generated Lean theorems against the kernel axiom allowlist."""
from __future__ import annotations

import re
import subprocess
import tempfile
from pathlib import Path
from typing import Literal, TypedDict

STANDARD_KERNEL_AXIOMS = frozenset(
    {"propext", "Classical.choice", "Quot.sound"}
)
DEFAULT_AXIOM_AUDIT_TIMEOUT_S = 300.0


class AuditResult(TypedDict):
    status: Literal["passed", "rejected", "error"]
    axioms: list[str]
    disallowed: list[str]


_NO_AXIOMS_RE = re.compile(
    r"^'(?P<theorem>[^']+)' does not depend on any axioms\.?$"
)
_AXIOMS_RE = re.compile(
    r"^'(?P<theorem>[^']+)' depends on axioms:\s*\[(?P<axioms>.*)$"
)


def render_audit_source(modules: list[str], theorems: list[str]) -> str:
    lines = [f"import {module}" for module in modules]
    if lines and theorems:
        lines.append("")
    lines.extend(f"#print axioms {theorem}" for theorem in theorems)
    return "\n".join(lines) + ("\n" if lines else "")


def parse_axiom_output(text: str) -> dict[str, list[str]]:
    results: dict[str, list[str]] = {}
    lines = text.splitlines()
    index = 0
    while index < len(lines):
        line = lines[index].strip()
        if line.startswith("info: "):
            line = line[len("info: ") :]
        no_axioms = _NO_AXIOMS_RE.match(line)
        if no_axioms is not None:
            results[no_axioms.group("theorem")] = []
            index += 1
            continue

        depends = _AXIOMS_RE.match(line)
        if depends is None:
            index += 1
            continue
        theorem = depends.group("theorem")
        axioms_text = depends.group("axioms")
        while "]" not in axioms_text and index + 1 < len(lines):
            index += 1
            axioms_text += " " + lines[index].strip()
        if "]" in axioms_text:
            axioms_text = axioms_text.split("]", maxsplit=1)[0]
            results[theorem] = [
                axiom.strip()
                for axiom in axioms_text.split(",")
                if axiom.strip()
            ]
        index += 1
    return results


def _error_results(theorems: list[str]) -> dict[str, AuditResult]:
    return {
        theorem: {
            "status": "error",
            "axioms": [],
            "disallowed": [],
        }
        for theorem in theorems
    }


def _write_log(log_path: Path, text: str) -> None:
    log_path.parent.mkdir(parents=True, exist_ok=True)
    log_path.write_text(text, encoding="utf-8")


def _output_text(value: str | bytes | None) -> str:
    if value is None:
        return ""
    return value.decode(errors="replace") if isinstance(value, bytes) else value


def run_axiom_audit(
    repo_dir: Path,
    modules: list[str],
    theorems: list[str],
    log_path: Path,
    timeout_s: float,
) -> dict[str, AuditResult]:
    """Run one pinned ``lake env lean`` process for the requested theorems."""
    theorems = list(dict.fromkeys(theorems))
    if not theorems:
        _write_log(log_path, "")
        return {}

    try:
        try:
            from .bridge import _lake_command_prefix
        except ImportError:  # direct ``python scripts/bridge.py`` import path
            from bridge import _lake_command_prefix  # type: ignore

        lake_prefix = _lake_command_prefix(repo_dir)
    except Exception as exc:
        _write_log(log_path, f"error: unable to select Lake toolchain: {exc}\n")
        return _error_results(theorems)

    if lake_prefix is None:
        _write_log(log_path, "error: `lake` not found on PATH\n")
        return _error_results(theorems)

    audit_path: Path | None = None
    try:
        with tempfile.NamedTemporaryFile(
            mode="w",
            encoding="utf-8",
            prefix="AxiomAudit_",
            suffix=".lean",
            dir=repo_dir,
            delete=False,
        ) as source_file:
            source_file.write(render_audit_source(modules, theorems))
            audit_path = Path(source_file.name)

        command = [*lake_prefix, "env", "lean", str(audit_path)]
        try:
            process = subprocess.run(
                command,
                cwd=repo_dir,
                capture_output=True,
                text=True,
                timeout=timeout_s,
                check=False,
            )
        except subprocess.TimeoutExpired as exc:
            output = _output_text(exc.stdout) + _output_text(exc.stderr)
            _write_log(
                log_path,
                output + f"\nerror: axiom audit timed out after {timeout_s}s\n",
            )
            return _error_results(theorems)
        except OSError as exc:
            _write_log(log_path, f"error: axiom audit could not start: {exc}\n")
            return _error_results(theorems)

        output = process.stdout + process.stderr
        _write_log(log_path, output)
        if process.returncode != 0:
            return _error_results(theorems)

        parsed = parse_axiom_output(output)
        results: dict[str, AuditResult] = {}
        for theorem in theorems:
            axioms = parsed.get(theorem)
            if axioms is None:
                results[theorem] = {
                    "status": "error",
                    "axioms": [],
                    "disallowed": [],
                }
                continue
            disallowed = [
                axiom for axiom in axioms if axiom not in STANDARD_KERNEL_AXIOMS
            ]
            results[theorem] = {
                "status": "rejected" if disallowed else "passed",
                "axioms": axioms,
                "disallowed": disallowed,
            }
        return results
    except Exception as exc:
        _write_log(log_path, f"error: unable to run axiom audit: {exc}\n")
        return _error_results(theorems)
    finally:
        if audit_path is not None:
            audit_path.unlink(missing_ok=True)
