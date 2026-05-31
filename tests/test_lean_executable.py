"""Tests for Lean executable artifact export."""
from __future__ import annotations

import os
import shutil
import subprocess
from pathlib import Path

import pytest

from lean_to_executable import (
    LeanExecutableError,
    _module_to_default_target,
    build_executable,
    main,
)

REPO_ROOT = Path(__file__).resolve().parent.parent
EXAMPLE_DIR = REPO_ROOT / "examples" / "lean_cli"


def _lake_env() -> dict[str, str]:
    env = os.environ.copy()
    elan_bin = Path.home() / ".elan" / "bin"
    env["PATH"] = f"{elan_bin}:{env.get('PATH', '')}"
    return env


def _have_lake() -> bool:
    return shutil.which("lake", path=_lake_env()["PATH"]) is not None


def test_module_name_derives_default_lake_target():
    assert _module_to_default_target("SimpleCli") == "simple-cli"
    assert _module_to_default_target("Tools.JSONPrinter") == "json-printer"
    assert _module_to_default_target("already_named") == "already-named"


def test_build_executable_copies_binary_and_certificate(tmp_path: Path, monkeypatch):
    project_dir = tmp_path / "project"
    bin_dir = project_dir / ".lake" / "build" / "bin"
    bin_dir.mkdir(parents=True)
    (project_dir / "lakefile.lean").write_text("import Lake\n")
    (project_dir / "lake-manifest.json").write_text("{}\n")
    binary = bin_dir / "simple-cli"
    binary.write_text("#!/bin/sh\n")
    cert = project_dir / ".lean-cert.json"
    cert.write_text('{"status":"verified"}\n')

    def fake_run(*_args, **_kwargs):
        return subprocess.CompletedProcess(["lake"], 0, "", "")

    monkeypatch.setattr("lean_to_executable.subprocess.run", fake_run)
    monkeypatch.setattr(
        "lean_to_executable.shutil.which",
        lambda *_args, **_kwargs: "lake",
    )

    copied_binary, copied_cert = build_executable(
        project_dir=project_dir,
        module="SimpleCli",
        out_dir=tmp_path / "out",
    )

    assert copied_binary.name == "simple-cli"
    assert copied_binary.read_text() == "#!/bin/sh\n"
    assert copied_cert.name == ".lean-cert.json"
    assert copied_cert.read_text() == '{"status":"verified"}\n'


def test_missing_lake_manifest_runs_lake_update(tmp_path: Path, monkeypatch):
    project_dir = tmp_path / "project"
    bin_dir = project_dir / ".lake" / "build" / "bin"
    bin_dir.mkdir(parents=True)
    (project_dir / "lakefile.lean").write_text("import Lake\n")
    (project_dir / ".lean-cert.json").write_text("{}\n")
    (bin_dir / "simple-cli").write_text("#!/bin/sh\n")
    calls = []

    def fake_run(args, **_kwargs):
        calls.append(args)
        return subprocess.CompletedProcess(args, 0, "", "")

    monkeypatch.setattr("lean_to_executable.subprocess.run", fake_run)
    monkeypatch.setattr(
        "lean_to_executable.shutil.which",
        lambda *_args, **_kwargs: "lake",
    )

    build_executable(
        project_dir=project_dir,
        module="SimpleCli",
        out_dir=tmp_path / "out",
    )

    assert calls[:2] == [["lake", "update"], ["lake", "build", "simple-cli"]]


def test_build_executable_can_smoke_test_copied_binary(tmp_path: Path, monkeypatch):
    project_dir = tmp_path / "project"
    bin_dir = project_dir / ".lake" / "build" / "bin"
    bin_dir.mkdir(parents=True)
    (project_dir / "lakefile.lean").write_text("import Lake\n")
    binary = bin_dir / "simple-cli"
    binary.write_text("#!/bin/sh\n")
    cert = project_dir / ".lean-cert.json"
    cert.write_text('{"status":"verified"}\n')
    calls = []

    def fake_run(args, **_kwargs):
        calls.append(args)
        return subprocess.CompletedProcess(args, 0, "ok\n", "")

    monkeypatch.setattr("lean_to_executable.subprocess.run", fake_run)
    monkeypatch.setattr(
        "lean_to_executable.shutil.which",
        lambda *_args, **_kwargs: "lake",
    )

    copied_binary, _copied_cert = build_executable(
        project_dir=project_dir,
        module="SimpleCli",
        out_dir=tmp_path / "out",
        run_args=["add", "2", "40"],
    )

    assert calls[0] == ["lake", "update"]
    assert calls[1][:3] == ["lake", "build", "simple-cli"]
    assert calls[2] == [str(copied_binary), "add", "2", "40"]


def test_build_executable_reports_smoke_test_timeout(tmp_path: Path, monkeypatch):
    project_dir = tmp_path / "project"
    bin_dir = project_dir / ".lake" / "build" / "bin"
    bin_dir.mkdir(parents=True)
    (project_dir / "lakefile.lean").write_text("import Lake\n")
    binary = bin_dir / "simple-cli"
    binary.write_text("#!/bin/sh\n")
    (project_dir / ".lean-cert.json").write_text('{"status":"verified"}\n')
    calls = []

    def fake_run(args, **_kwargs):
        calls.append(args)
        if len(calls) == 3:
            raise subprocess.TimeoutExpired(args, timeout=1)
        return subprocess.CompletedProcess(args, 0, "", "")

    monkeypatch.setattr("lean_to_executable.subprocess.run", fake_run)
    monkeypatch.setattr(
        "lean_to_executable.shutil.which",
        lambda *_args, **_kwargs: "lake",
    )

    with pytest.raises(LeanExecutableError) as exc:
        build_executable(
            project_dir=project_dir,
            module="SimpleCli",
            out_dir=tmp_path / "out",
            run_args=["sleep"],
            run_timeout=1,
        )

    assert "timed out after 1 seconds" in str(exc.value)


def test_lake_failure_reports_build_output(tmp_path: Path, monkeypatch):
    project_dir = tmp_path / "project"
    project_dir.mkdir()
    (project_dir / "lakefile.lean").write_text("import Lake\n")
    (project_dir / ".lean-cert.json").write_text("{}\n")

    def fake_run(*_args, **_kwargs):
        return subprocess.CompletedProcess(["lake"], 1, "stdout\n", "stderr\n")

    monkeypatch.setattr("lean_to_executable.subprocess.run", fake_run)
    monkeypatch.setattr(
        "lean_to_executable.shutil.which",
        lambda *_args, **_kwargs: "lake",
    )

    with pytest.raises(LeanExecutableError) as exc:
        build_executable(
            project_dir=project_dir,
            module="SimpleCli",
            out_dir=tmp_path / "out",
        )

    message = str(exc.value)
    assert "`lake update` failed with exit code 1" in message
    assert "stdout" in message
    assert "stderr" in message


def test_successful_build_requires_binary_artifact(tmp_path: Path, monkeypatch):
    project_dir = tmp_path / "project"
    project_dir.mkdir()
    (project_dir / "lakefile.lean").write_text("import Lake\n")
    (project_dir / ".lean-cert.json").write_text("{}\n")

    def fake_run(*_args, **_kwargs):
        return subprocess.CompletedProcess(["lake"], 0, "", "")

    monkeypatch.setattr("lean_to_executable.subprocess.run", fake_run)
    monkeypatch.setattr(
        "lean_to_executable.shutil.which",
        lambda *_args, **_kwargs: "lake",
    )

    with pytest.raises(LeanExecutableError) as exc:
        build_executable(
            project_dir=project_dir,
            module="SimpleCli",
            out_dir=tmp_path / "out",
        )

    assert "Lake build succeeded but no binary was found" in str(exc.value)


def test_main_returns_nonzero_when_certificate_is_missing(tmp_path: Path, capsys):
    project_dir = tmp_path / "project"
    project_dir.mkdir()
    (project_dir / "lakefile.lean").write_text("import Lake\n")

    rc = main(
        [
            "--project-dir",
            str(project_dir),
            "--module",
            "SimpleCli",
            "--out-dir",
            str(tmp_path / "out"),
        ]
    )

    assert rc == 1
    assert "Lean certificate not found" in capsys.readouterr().err


@pytest.mark.skipif(
    not _have_lake(),
    reason="lake not on PATH; skipping live Lean executable build",
)
@pytest.mark.skipif(
    os.environ.get("MUMEI_LEAN_SKIP_LIVE") == "1",
    reason="MUMEI_LEAN_SKIP_LIVE=1 set",
)
def test_example_cli_builds_and_runs(tmp_path: Path):
    rc = main(
        [
            "--project-dir",
            str(EXAMPLE_DIR),
            "--module",
            "SimpleCli",
            "--out-dir",
            str(tmp_path),
        ]
    )
    assert rc == 0
    binary = tmp_path / "simple-cli"
    cert = tmp_path / ".lean-cert.json"
    assert binary.exists()
    assert cert.exists()

    proc = subprocess.run(
        [str(binary), "add", "2", "40"],
        capture_output=True,
        text=True,
        timeout=30,
    )
    assert proc.returncode == 0
    assert proc.stdout.strip() == "42"

    for args, expected in (
        (["merkle", "7", "3", "4", "7", "1"], "merkle accepted root=7"),
        (["defi-transfer", "20", "30", "5"], "defi transfer accepted to_balance=35"),
        (["audit-commitment", "10", "20", "30", "60"], "audit commitment accepted commitment=60"),
    ):
        proc = subprocess.run(
            [str(binary), *args],
            capture_output=True,
            text=True,
            timeout=30,
        )
        assert proc.returncode == 0
        assert proc.stdout.strip() == expected
