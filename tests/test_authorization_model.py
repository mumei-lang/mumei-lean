from __future__ import annotations

import json
import os
import re
import shutil
from pathlib import Path

import pytest
import yaml

import check_authorization_model as gate

ROOT = Path(__file__).resolve().parents[1]


@pytest.mark.parametrize("module,names", gate.THEOREMS.items())
def test_every_model_and_example_theorem_is_audited(module, names):
    source = ROOT.joinpath(*module.split(".")).with_suffix(".lean").read_text()
    declarations = re.findall(r"^theorem ([A-Za-z0-9_]+)", source, re.MULTILINE)
    assert len(names) == len(set(names))
    assert set(names) == set(declarations)


def test_gate_is_required_and_preserves_diagnostics():
    workflow = yaml.safe_load((ROOT / ".github/workflows/authorization-model.yml").read_text())
    job = workflow["jobs"]["authorization-model"]
    assert job["runs-on"] == "ubuntu-24.04"
    assert not job.get("continue-on-error", False)
    assert any("check_authorization_model.py" in step.get("run", "") for step in job["steps"])
    uploads = [step for step in job["steps"] if step.get("uses", "").startswith("actions/upload-artifact@")]
    assert len(uploads) == 1
    assert uploads[0]["if"] == "always()"


@pytest.fixture
def fake_gate(monkeypatch):
    monkeypatch.setattr(gate, "THEOREMS", {"MumeiLean.AuthorizationModel": ["one", "two"]})
    monkeypatch.setattr(gate, "_rebuild_module_for_audit", lambda *args: True)

    def passed(repo, modules, theorems, log, timeout):
        return {theorem: {"status": "passed", "axioms": [], "disallowed": []} for theorem in theorems}

    monkeypatch.setattr(gate, "run_axiom_audit", passed)


def test_success_retains_existing_audit_contract(tmp_path, fake_gate):
    assert gate.check(ROOT, tmp_path)
    report = json.loads((tmp_path / "axiom_audit.json").read_text())
    assert len(report) == 2
    assert all(result == {"status": "passed", "axioms": [], "disallowed": []} for result in report.values())
    assert not list(tmp_path.glob("*.lean-cert.json"))


@pytest.mark.parametrize("failed_module", list(gate.THEOREMS))
def test_failed_build_never_audits_stale_artifacts(tmp_path, monkeypatch, failed_module):
    audited = []
    monkeypatch.setattr(gate, "_rebuild_module_for_audit", lambda repo, module, log: module != failed_module)

    def audit(repo, modules, theorems, log, timeout):
        audited.extend(modules)
        return {theorem: {"status": "passed", "axioms": [], "disallowed": []} for theorem in theorems}

    monkeypatch.setattr(gate, "run_axiom_audit", audit)
    (tmp_path / "axiom_audit.json").write_text('{"old": {"status": "passed"}}')
    assert not gate.check(ROOT, tmp_path)
    assert failed_module not in audited
    results = json.loads((tmp_path / "axiom_audit.json").read_text())
    assert "old" not in results
    assert all(results[f"{failed_module}.{name}"]["status"] == "error" for name in gate.THEOREMS[failed_module])


@pytest.mark.parametrize("status", ["rejected", "error"])
@pytest.mark.parametrize("missing", [False, True])
def test_incomplete_or_rejected_audit_fails(tmp_path, fake_gate, monkeypatch, status, missing):
    def audit(repo, modules, theorems, log, timeout):
        return {} if missing else {
            theorems[0]: {"status": status, "axioms": ["sorryAx"], "disallowed": ["sorryAx"]}
        }

    monkeypatch.setattr(gate, "run_axiom_audit", audit)
    assert not gate.check(ROOT, tmp_path)


def test_empty_registry_does_not_pass(tmp_path, monkeypatch):
    monkeypatch.setattr(gate, "THEOREMS", {})
    assert not gate.check(ROOT, tmp_path)


@pytest.mark.parametrize("passed,exit_code", [(True, 0), (False, 1)])
def test_cli_returns_failure_status(tmp_path, monkeypatch, passed, exit_code):
    monkeypatch.setattr(gate, "check", lambda repo, out: passed)
    assert gate.main(["--out-dir", str(tmp_path)]) == exit_code


@pytest.fixture
def model_repo(tmp_path, lake_available):
    if os.environ.get("MUMEI_LEAN_SKIP_LIVE") == "1":
        pytest.skip("live Lean tests disabled")
    (tmp_path / "MumeiLean").mkdir()
    for module in gate.THEOREMS:
        source = Path(*module.split(".")).with_suffix(".lean")
        shutil.copyfile(ROOT / source, tmp_path / source)
    shutil.copyfile(ROOT / "lean-toolchain", tmp_path / "lean-toolchain")
    (tmp_path / "lakefile.lean").write_text(
        'import Lake\nopen Lake DSL\npackage authorizationTest\nlean_lib MumeiLean\n'
    )
    return tmp_path


@pytest.mark.lake_available
def test_live_model_and_examples_pass(model_repo):
    assert gate.check(model_repo, model_repo / "out")


@pytest.mark.lake_available
@pytest.mark.parametrize("proof", ["sorry", "unsafeWitness"])
def test_live_forbidden_axiom_fails_even_when_build_succeeds(model_repo, proof):
    path = model_repo / "MumeiLean/AuthorizationExamples.lean"
    source = path.read_text().replace(
        "theorem owner_update_succeeds :", "axiom unsafeWitness : False\n\ntheorem owner_update_succeeds :", 1
    )
    replacement = "by sorry" if proof == "sorry" else "by exact False.elim unsafeWitness"
    path.write_text(source.replace("by decide", replacement, 1))
    assert not gate.check(model_repo, model_repo / "out")
    report = json.loads((model_repo / "out/axiom_audit.json").read_text())
    result = report["MumeiLean.AuthorizationExamples.owner_update_succeeds"]
    assert result["status"] == "rejected"
    assert result["disallowed"]


@pytest.mark.lake_available
def test_live_failed_rebuild_does_not_reuse_previous_success(model_repo):
    out = model_repo / "out"
    assert gate.check(model_repo, out)
    path = model_repo / "MumeiLean/AuthorizationExamples.lean"
    path.write_text(path.read_text().replace("by decide", "by exact invalidProof", 1))
    assert not gate.check(model_repo, out)
    report = json.loads((out / "axiom_audit.json").read_text())
    assert all(report[f"MumeiLean.AuthorizationExamples.{name}"]["status"] == "error"
               for name in gate.THEOREMS["MumeiLean.AuthorizationExamples"])
