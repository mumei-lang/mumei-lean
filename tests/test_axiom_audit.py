from __future__ import annotations

import json
import subprocess
import uuid
from pathlib import Path

import pytest

import axiom_audit
import bridge

REPO_ROOT = Path(__file__).resolve().parents[1]


def _bridge_test_atom(name: str) -> dict:
    return {
        "name": name,
        "requires": "x >= 0",
        "ensures": "result > x",
        "body_expr": "x + 1",
        "z3_check_result": "unknown",
        "status": "unknown",
        "content_hash": f"h-{name}",
        "proof_hash": f"p-{name}",
        "dependencies": [],
        "effects": [],
        "translator_version": bridge.TRANSLATOR_VERSION,
        "bridge_lemma_hash": bridge.BRIDGE_LEMMA_HASH,
    }


def _bridge_test_cert(file: str, names: list[str]) -> dict:
    return {
        "version": "1.0",
        "timestamp": "2026-05-11T00:00:00Z",
        "mumei_version": "0.6.12",
        "z3_version": "4.12.2",
        "file": file,
        "atoms": [_bridge_test_atom(name) for name in names],
        "package_name": "axiom-audit-test",
        "package_version": "0",
        "certificate_hash": "",
        "all_verified": False,
    }


def test_render_audit_source_imports_modules_and_prints_each_theorem():
    assert axiom_audit.render_audit_source(
        ["Generated.Math", "Generated.List"],
        ["Generated.Math.inc_correct", "Generated.List.length_correct"],
    ) == (
        "import Generated.Math\n"
        "import Generated.List\n"
        "\n"
        "#print axioms Generated.Math.inc_correct\n"
        "#print axioms Generated.List.length_correct\n"
    )


def test_parse_axiom_output_handles_empty_standard_and_wrapped_lists():
    output = (
        "'Generated.Math.closed' does not depend on any axioms\n"
        "'Generated.Math.classical' depends on axioms: "
        "[propext, Classical.choice, Quot.sound]\n"
        "'Generated.Math.user' depends on axioms: [\n"
        "  User.assumption,\n"
        "  Lean.ofReduceBool,\n"
        "  sorryAx]\n"
    )

    assert axiom_audit.parse_axiom_output(output) == {
        "Generated.Math.closed": [],
        "Generated.Math.classical": [
            "propext",
            "Classical.choice",
            "Quot.sound",
        ],
        "Generated.Math.user": [
            "User.assumption",
            "Lean.ofReduceBool",
            "sorryAx",
        ],
    }


def test_parse_axiom_output_ignores_missing_and_unrelated_lines():
    assert axiom_audit.parse_axiom_output(
        "warning: unrelated output\n"
        "'Generated.Math.present' depends on axioms: [propext]\n"
    ) == {"Generated.Math.present": ["propext"]}


def test_run_axiom_audit_rejects_disallowed_axioms_and_fails_missing_output(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
):
    theorem = "Generated.Math.closed"
    missing = "Generated.Math.missing"
    monkeypatch.setattr(bridge, "_lake_command_prefix", lambda _repo: ["lake"])

    def fake_run(command, **kwargs):  # noqa: ANN001
        assert command[-2:] == ["lean", command[-1]]
        assert command[-1].endswith(".lean")
        assert kwargs["cwd"] == tmp_path
        return subprocess.CompletedProcess(
            command,
            0,
            stdout=(
                f"'{theorem}' depends on axioms: [sorryAx, User.assumption]\n"
            ),
            stderr="",
        )

    monkeypatch.setattr(axiom_audit.subprocess, "run", fake_run)
    log_path = tmp_path / "logs" / "axiom_audit.log"

    results = axiom_audit.run_axiom_audit(
        tmp_path,
        ["Generated.Math"],
        [theorem, missing],
        log_path,
        1.0,
    )

    assert results == {
        theorem: {
            "status": "rejected",
            "axioms": ["sorryAx", "User.assumption"],
            "disallowed": ["sorryAx", "User.assumption"],
        },
        missing: {
            "status": "error",
            "axioms": [],
            "disallowed": [],
        },
    }
    assert "'Generated.Math.closed'" in log_path.read_text()


def test_run_axiom_audit_fails_closed_when_lake_is_missing(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
):
    monkeypatch.setattr(bridge, "_lake_command_prefix", lambda _repo: None)

    results = axiom_audit.run_axiom_audit(
        tmp_path,
        ["Generated.Math"],
        ["Generated.Math.closed"],
        tmp_path / "axiom_audit.log",
        1.0,
    )

    assert results["Generated.Math.closed"]["status"] == "error"


@pytest.mark.parametrize(
    ("returncode", "timeout"),
    [(1, False), (0, True)],
)
def test_run_axiom_audit_fails_closed_on_process_failure(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    returncode: int,
    timeout: bool,
):
    monkeypatch.setattr(bridge, "_lake_command_prefix", lambda _repo: ["lake"])

    def fake_run(command, **kwargs):  # noqa: ANN001
        if timeout:
            raise subprocess.TimeoutExpired(command, kwargs["timeout"], output="partial")
        return subprocess.CompletedProcess(
            command,
            returncode,
            stdout="'Generated.Math.closed' does not depend on any axioms\n",
            stderr="",
        )

    monkeypatch.setattr(axiom_audit.subprocess, "run", fake_run)
    theorem = "Generated.Math.closed"

    results = axiom_audit.run_axiom_audit(
        tmp_path,
        ["Generated.Math"],
        [theorem],
        tmp_path / "axiom_audit.log",
        1.0,
    )

    assert results[theorem] == {
        "status": "error",
        "axioms": [],
        "disallowed": [],
    }


@pytest.mark.parametrize(
    ("status", "axioms", "disallowed"),
    [
        ("passed", ["Classical.choice"], []),
        ("rejected", ["User.assumption"], ["User.assumption"]),
        ("error", [], []),
    ],
)
def test_bridge_axiom_audit_controls_promotion_and_metadata(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
    status: str,
    axioms: list[str],
    disallowed: list[str],
):
    fixture = REPO_ROOT / "tests" / "fixtures" / "abs_saturating.proof-cert.json"
    out_dir = tmp_path / "generated"
    repo_dir = tmp_path / "project"
    repo_dir.mkdir()
    out_cert = tmp_path / "out.lean-cert.json"
    summary_path = tmp_path / "summary.json"
    theorem = "Generated.Std.Math.Abs.abs_saturating_correct"

    def fake_build(_repo_dir: Path, log_path: Path) -> tuple[int, float]:
        log_path.parent.mkdir(parents=True, exist_ok=True)
        log_path.write_text("")
        return 0, 0.01

    def fake_audit(_repo_dir, modules, theorems, _log_path, _timeout_s):  # noqa: ANN001
        assert modules == ["Generated.Std.Math.Abs"]
        assert theorems == [theorem]
        return {
            theorem: {
                "status": status,
                "axioms": axioms,
                "disallowed": disallowed,
            }
        }

    def fake_module_build(command, **_kwargs):  # noqa: ANN001
        return subprocess.CompletedProcess(
            command,
            0,
            stdout="",
            stderr="",
        )

    monkeypatch.setattr(bridge, "_lake_command_prefix", lambda _repo: ["lake"])
    monkeypatch.setattr(
        bridge,
        "_lake_build_command",
        lambda _repo, module: ["lake", "build", module],
    )
    monkeypatch.setattr(bridge.subprocess, "run", fake_module_build)
    monkeypatch.setattr(bridge, "_run_lake_build", fake_build)
    monkeypatch.setattr(bridge, "run_axiom_audit", fake_audit)

    rc = bridge.main(
        [
            "--cert",
            str(fixture),
            "--out-dir",
            str(out_dir),
            "--repo-dir",
            str(repo_dir),
            "--lean-cert-out",
            str(out_cert),
            "--summary-json",
            str(summary_path),
            "--no-tactic-search",
        ]
    )

    assert rc == 0
    exported = json.loads(out_cert.read_text())
    atom = exported["atoms"][0]
    metadata = atom["lean_result_metadata"]
    assert metadata["axiom_audit"] == status
    assert metadata["kernel_axioms"] == axioms
    if status == "passed":
        assert atom["z3_check_result"] == "lean_verified"
    else:
        assert atom["z3_check_result"] != "lean_verified"
    audit_json = json.loads((out_dir / "axiom_audit.json").read_text())
    assert audit_json[theorem] == {
        "status": status,
        "axioms": axioms,
        "disallowed": disallowed,
    }
    counts = json.loads(summary_path.read_text())["axiom_audit"]
    assert counts == {
        "passed": int(status == "passed"),
        "rejected": int(status == "rejected"),
        "error": int(status == "error"),
    }
    if status == "rejected":
        assert "User.assumption" in capsys.readouterr().err


@pytest.mark.parametrize(
    ("status", "axioms", "disallowed"),
    [
        ("rejected", ["User.assumption"], ["User.assumption"]),
        ("error", [], []),
    ],
)
def test_failed_known_witness_audit_blocks_export_promotion(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    status: str,
    axioms: list[str],
    disallowed: list[str],
):
    fixture = REPO_ROOT / "tests" / "fixtures" / "abs_saturating.proof-cert.json"
    out_dir = tmp_path / "generated"
    repo_dir = tmp_path / "project"
    repo_dir.mkdir()
    out_cert = tmp_path / "out.lean-cert.json"
    summary_path = tmp_path / "summary.json"
    theorem = "Generated.Std.Math.Abs.abs_saturating_correct"

    def fake_build(_repo_dir: Path, log_path: Path) -> tuple[int, float]:
        log_path.parent.mkdir(parents=True, exist_ok=True)
        log_path.write_text("error: cannot resolve dependency 'mathlib'\n")
        return 1, 0.01

    def fake_audit(_repo_dir, modules, theorems, _log_path, _timeout_s):  # noqa: ANN001
        assert modules == ["Generated.Std.Math.Abs"]
        assert theorems == [theorem]
        return {
            theorem: {
                "status": status,
                "axioms": axioms,
                "disallowed": disallowed,
            }
        }

    def fake_module_build(command, **_kwargs):  # noqa: ANN001
        return subprocess.CompletedProcess(command, 0, stdout="", stderr="")

    monkeypatch.setattr(bridge, "_lake_command_prefix", lambda _repo: ["lake"])
    monkeypatch.setattr(
        bridge,
        "_lake_build_command",
        lambda _repo, module: ["lake", "build", module],
    )
    monkeypatch.setattr(bridge.subprocess, "run", fake_module_build)
    monkeypatch.setattr(bridge, "_run_lake_build", fake_build)
    monkeypatch.setattr(
        bridge,
        "_verify_known_witnesses",
        lambda *_args: [("std/math/abs", "abs_saturating")],
    )
    monkeypatch.setattr(bridge, "run_axiom_audit", fake_audit)

    rc = bridge.main(
        [
            "--cert",
            str(fixture),
            "--out-dir",
            str(out_dir),
            "--repo-dir",
            str(repo_dir),
            "--lean-cert-out",
            str(out_cert),
            "--summary-json",
            str(summary_path),
            "--no-tactic-search",
        ]
    )

    assert rc == 1
    atom = json.loads(out_cert.read_text())["atoms"][0]
    assert atom["z3_check_result"] != "lean_verified"
    assert atom["lean_metadata"]["status"] != "lean_verified"
    assert json.loads((out_dir / "axiom_audit.json").read_text())[theorem][
        "status"
    ] == status
    summary = json.loads(summary_path.read_text())
    assert summary["axiom_audit"][status] == 1
    assert summary["lean_fallback"]["known_witness_used"] == 0


def test_bridge_audits_modules_independently(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
):
    scan_root = tmp_path / "input"
    certs_dir = scan_root / "std" / "certs"
    certs_dir.mkdir(parents=True)
    (certs_dir / "module_a.proof-cert.json").write_text(
        json.dumps(_bridge_test_cert("std/audit_module_a.mm", ["audit_a"]))
    )
    (certs_dir / "module_b.proof-cert.json").write_text(
        json.dumps(_bridge_test_cert("std/audit_module_b.mm", ["audit_b"]))
    )
    out_dir = tmp_path / "generated"
    cert_out_dir = tmp_path / "lean-certs"
    repo_dir = tmp_path / "project"
    repo_dir.mkdir()
    summary_path = tmp_path / "summary.json"
    module_a = "Generated.Std.Audit_module_a"
    module_b = "Generated.Std.Audit_module_b"
    theorem_a = f"{module_a}.audit_a_correct"
    theorem_b = f"{module_b}.audit_b_correct"
    calls: list[tuple[list[str], list[str], Path]] = []

    def fake_build(_repo_dir: Path, log_path: Path) -> tuple[int, float]:
        log_path.parent.mkdir(parents=True, exist_ok=True)
        log_path.write_text("")
        return 0, 0.01

    def fake_audit(
        _repo_dir: Path,
        modules: list[str],
        theorems: list[str],
        log_path: Path,
        _timeout_s: float,
    ) -> dict[str, dict]:
        calls.append((modules, theorems, log_path))
        status = "error" if modules == [module_a] else "passed"
        return {
            theorem: {
                "status": status,
                "axioms": [],
                "disallowed": [],
            }
            for theorem in theorems
        }

    def unexpected_module_build(_repo_dir: Path, module: str) -> list[str]:
        raise AssertionError(f"build_rc=0 must not rebuild {module}")

    monkeypatch.setattr(bridge, "_lake_command_prefix", lambda _repo: ["lake"])
    monkeypatch.setattr(bridge, "_lake_build_command", unexpected_module_build)
    monkeypatch.setattr(bridge, "_run_lake_build", fake_build)
    monkeypatch.setattr(bridge, "run_axiom_audit", fake_audit)

    rc = bridge.main(
        [
            "--scan-unknown",
            str(scan_root),
            "--out-dir",
            str(out_dir),
            "--module-prefix",
            "Generated",
            "--repo-dir",
            str(repo_dir),
            "--lean-cert-out",
            str(cert_out_dir),
            "--summary-json",
            str(summary_path),
            "--no-tactic-search",
        ]
    )

    assert rc == 0
    assert calls == [
        (
            [module_a],
            [theorem_a],
            out_dir / "axiom_audit_logs" / "Generated_Std_Audit_module_a.log",
        ),
        (
            [module_b],
            [theorem_b],
            out_dir / "axiom_audit_logs" / "Generated_Std_Audit_module_b.log",
        ),
    ]
    exported_atoms = {
        atom["name"]: atom
        for path in cert_out_dir.glob("*.json")
        for atom in json.loads(path.read_text())["atoms"]
    }
    assert exported_atoms["audit_a"]["z3_check_result"] != "lean_verified"
    assert exported_atoms["audit_b"]["z3_check_result"] == "lean_verified"
    summary = json.loads(summary_path.read_text())
    assert summary["axiom_audit"] == {"passed": 1, "rejected": 0, "error": 1}
    audit_json = json.loads((out_dir / "axiom_audit.json").read_text())
    assert audit_json[theorem_a]["status"] == "error"
    assert audit_json[theorem_b]["status"] == "passed"


def test_failed_aggregate_build_rebuilds_modules_before_audit(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
):
    scan_root = tmp_path / "input"
    certs_dir = scan_root / "std" / "certs"
    certs_dir.mkdir(parents=True)
    (certs_dir / "module_a.proof-cert.json").write_text(
        json.dumps(_bridge_test_cert("std/audit_module_a.mm", ["audit_a"]))
    )
    (certs_dir / "module_b.proof-cert.json").write_text(
        json.dumps(_bridge_test_cert("std/audit_module_b.mm", ["audit_b"]))
    )
    out_dir = tmp_path / "generated"
    cert_out_dir = tmp_path / "lean-certs"
    repo_dir = tmp_path / "project"
    repo_dir.mkdir()
    summary_path = tmp_path / "summary.json"
    module_a = "Generated.Std.Audit_module_a"
    module_b = "Generated.Std.Audit_module_b"
    theorem_a = f"{module_a}.audit_a_correct"
    theorem_b = f"{module_b}.audit_b_correct"
    module_build_calls: list[str] = []
    audit_calls: list[tuple[list[str], list[str]]] = []

    def fake_build(_repo_dir: Path, log_path: Path) -> tuple[int, float]:
        log_path.parent.mkdir(parents=True, exist_ok=True)
        log_path.write_text("an unrelated generated declaration failed\n")
        return 1, 0.01

    def keep_candidates_for_module_audit(**kwargs) -> list[list[str]]:  # noqa: ANN003
        return [[] for _ in kwargs["atoms_per_payload"]]

    def fake_lake_build_command(_repo_dir: Path, module: str) -> list[str]:
        module_build_calls.append(module)
        return ["lake", "build", module]

    def fake_subprocess_run(command, **_kwargs):  # noqa: ANN001
        module = command[-1]
        if module == module_a:
            return subprocess.CompletedProcess(
                command,
                1,
                stdout="module A build failed",
                stderr="",
            )
        return subprocess.CompletedProcess(command, 0, stdout="", stderr="")

    def fake_audit(
        _repo_dir: Path,
        modules: list[str],
        theorems: list[str],
        _log_path: Path,
        _timeout_s: float,
    ) -> dict[str, dict]:
        audit_calls.append((modules, theorems))
        assert modules == [module_b]
        return {
            theorem: {"status": "passed", "axioms": [], "disallowed": []}
            for theorem in theorems
        }

    monkeypatch.setattr(bridge, "_lake_command_prefix", lambda _repo: ["lake"])
    monkeypatch.setattr(bridge, "_lake_build_command", fake_lake_build_command)
    monkeypatch.setattr(bridge, "_run_lake_build", fake_build)
    monkeypatch.setattr(bridge, "_attribute_failures", keep_candidates_for_module_audit)
    monkeypatch.setattr(bridge.subprocess, "run", fake_subprocess_run)
    monkeypatch.setattr(bridge, "run_axiom_audit", fake_audit)

    rc = bridge.main(
        [
            "--scan-unknown",
            str(scan_root),
            "--out-dir",
            str(out_dir),
            "--module-prefix",
            "Generated",
            "--repo-dir",
            str(repo_dir),
            "--lean-cert-out",
            str(cert_out_dir),
            "--summary-json",
            str(summary_path),
            "--no-tactic-search",
        ]
    )

    assert rc == 1
    assert module_build_calls == [module_a, module_b]
    assert audit_calls == [([module_b], [theorem_b])]
    exported_atoms = {
        atom["name"]: atom
        for path in cert_out_dir.glob("*.json")
        for atom in json.loads(path.read_text())["atoms"]
    }
    assert exported_atoms["audit_a"]["z3_check_result"] != "lean_verified"
    assert exported_atoms["audit_b"]["z3_check_result"] == "lean_verified"
    summary = json.loads(summary_path.read_text())
    assert summary["axiom_audit"] == {"passed": 1, "rejected": 0, "error": 1}
    audit_json = json.loads((out_dir / "axiom_audit.json").read_text())
    assert audit_json[theorem_a]["status"] == "error"
    assert audit_json[theorem_b]["status"] == "passed"
    assert (
        out_dir
        / "axiom_audit_logs"
        / "Generated_Std_Audit_module_a.build.log"
    ).read_text() == "module A build failed"


def test_unrenderable_theorem_is_reported_as_error_without_blocking_module(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
):
    scan_root = tmp_path / "input"
    certs_dir = scan_root / "std" / "certs"
    certs_dir.mkdir(parents=True)
    (certs_dir / "unrenderable.proof-cert.json").write_text(
        json.dumps(
            _bridge_test_cert("std/unrenderable_a.mm", ["unrenderable_atom"])
        )
    )
    (certs_dir / "renderable.proof-cert.json").write_text(
        json.dumps(_bridge_test_cert("std/renderable_b.mm", ["renderable_atom"]))
    )
    out_dir = tmp_path / "generated"
    cert_out_dir = tmp_path / "lean-certs"
    repo_dir = tmp_path / "project"
    repo_dir.mkdir()
    summary_path = tmp_path / "summary.json"
    module_a = "Generated.Std.Unrenderable_a"
    module_b = "Generated.Std.Renderable_b"
    theorem_a = f"{module_a}.unrenderable_atom_correct"
    theorem_b = f"{module_b}.renderable_atom_correct"
    real_render_theorem = bridge.render_theorem
    calls: list[tuple[list[str], list[str]]] = []

    def fake_build(_repo_dir: Path, log_path: Path) -> tuple[int, float]:
        log_path.parent.mkdir(parents=True, exist_ok=True)
        log_path.write_text("")
        return 0, 0.01

    def raising_render_theorem(atom) -> str:  # noqa: ANN001
        if atom.name == "unrenderable_atom":
            raise ValueError("test rendering failure")
        return real_render_theorem(atom)

    def fake_audit(
        _repo_dir: Path,
        modules: list[str],
        theorems: list[str],
        _log_path: Path,
        _timeout_s: float,
    ) -> dict[str, dict]:
        calls.append((modules, theorems))
        return {
            theorem: {"status": "passed", "axioms": [], "disallowed": []}
            for theorem in theorems
        }

    monkeypatch.setattr(bridge, "_lake_command_prefix", lambda _repo: ["lake"])
    monkeypatch.setattr(bridge, "_run_lake_build", fake_build)
    monkeypatch.setattr(bridge, "render_theorem", raising_render_theorem)
    monkeypatch.setattr(bridge, "run_axiom_audit", fake_audit)

    rc = bridge.main(
        [
            "--scan-unknown",
            str(scan_root),
            "--out-dir",
            str(out_dir),
            "--module-prefix",
            "Generated",
            "--repo-dir",
            str(repo_dir),
            "--lean-cert-out",
            str(cert_out_dir),
            "--summary-json",
            str(summary_path),
            "--no-tactic-search",
        ]
    )

    assert rc == 0
    assert calls == [([module_b], [theorem_b])]
    exported = {
        atom["name"]: atom
        for path in cert_out_dir.glob("*.json")
        for atom in json.loads(path.read_text())["atoms"]
    }
    assert exported["unrenderable_atom"]["z3_check_result"] != "lean_verified"
    assert exported["renderable_atom"]["z3_check_result"] == "lean_verified"
    audit_json = json.loads((out_dir / "axiom_audit.json").read_text())
    assert audit_json[theorem_a] == {
        "status": "error",
        "axioms": [],
        "disallowed": [],
    }
    assert audit_json[theorem_b]["status"] == "passed"
    assert json.loads(summary_path.read_text())["axiom_audit"] == {
        "passed": 1,
        "rejected": 0,
        "error": 1,
    }


def test_bridge_no_build_skips_kernel_audit_and_records_zero_counts(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
):
    fixture = REPO_ROOT / "tests" / "fixtures" / "abs_saturating.proof-cert.json"
    out_dir = tmp_path / "generated"
    out_cert = tmp_path / "out.lean-cert.json"
    summary_path = tmp_path / "summary.json"

    def unexpected_audit(*_args, **_kwargs):  # noqa: ANN002, ANN003
        raise AssertionError("no-build must skip the kernel axiom audit")

    monkeypatch.setattr(bridge, "run_axiom_audit", unexpected_audit)

    rc = bridge.main(
        [
            "--cert",
            str(fixture),
            "--out-dir",
            str(out_dir),
            "--lean-cert-out",
            str(out_cert),
            "--summary-json",
            str(summary_path),
            "--no-build",
        ]
    )

    assert rc == 0
    exported = json.loads(out_cert.read_text())
    assert exported["atoms"][0]["z3_check_result"] != "lean_verified"
    assert json.loads((out_dir / "axiom_audit.json").read_text()) == {}
    assert json.loads(summary_path.read_text())["axiom_audit"] == {
        "passed": 0,
        "rejected": 0,
        "error": 0,
    }


def test_bridge_missing_lake_skips_kernel_audit_and_does_not_promote(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
):
    fixture = REPO_ROOT / "tests" / "fixtures" / "abs_saturating.proof-cert.json"
    out_dir = tmp_path / "generated"
    repo_dir = tmp_path / "project"
    repo_dir.mkdir()
    out_cert = tmp_path / "out.lean-cert.json"
    summary_path = tmp_path / "summary.json"

    def fake_build(_repo_dir: Path, log_path: Path) -> tuple[int, None]:
        log_path.parent.mkdir(parents=True, exist_ok=True)
        log_path.write_text("error: `lake` not found on PATH\n")
        return 127, None

    def unexpected_audit(*_args, **_kwargs):  # noqa: ANN002, ANN003
        raise AssertionError("missing Lake must skip the kernel axiom audit")

    monkeypatch.setattr(bridge, "_lake_command_prefix", lambda _repo: None)
    monkeypatch.setattr(bridge, "_run_lake_build", fake_build)
    monkeypatch.setattr(bridge, "run_axiom_audit", unexpected_audit)

    rc = bridge.main(
        [
            "--cert",
            str(fixture),
            "--out-dir",
            str(out_dir),
            "--repo-dir",
            str(repo_dir),
            "--lean-cert-out",
            str(out_cert),
            "--summary-json",
            str(summary_path),
            "--no-tactic-search",
        ]
    )

    assert rc == 127
    atom = json.loads(out_cert.read_text())["atoms"][0]
    assert atom["z3_check_result"] != "lean_verified"
    assert "axiom_audit" not in atom["lean_result_metadata"]
    assert json.loads((out_dir / "axiom_audit.json").read_text()) == {}
    assert json.loads(summary_path.read_text())["axiom_audit"] == {
        "passed": 0,
        "rejected": 0,
        "error": 0,
    }


@pytest.mark.lake_available
def test_kernel_axiom_audit_lean_e2e(lake_available, tmp_path: Path):
    (tmp_path / "lean-toolchain").write_text(
        (REPO_ROOT / "lean-toolchain").read_text()
    )
    (tmp_path / "lakefile.lean").write_text(
        "import Lake\n"
        "open Lake DSL\n"
        "package axiomAuditFixture where\n"
        "lean_lib AxiomAuditFixture\n"
    )
    (tmp_path / "AxiomAuditFixture.lean").write_text(
        "namespace AxiomAuditFixture\n"
        "axiom localAuditAxiom : True\n"
        "theorem audit_decide : 2 + 2 = 4 := by decide\n"
        "theorem audit_choice {α : Type} (h : Nonempty α) : ∃ x : α, True :=\n"
        "  ⟨Classical.choice h, trivial⟩\n"
        "theorem audit_user_axiom : True := localAuditAxiom\n"
        "theorem audit_native : 1 = 1 := by native_decide\n"
        "end AxiomAuditFixture\n"
    )
    build = subprocess.run(
        ["lake", "build", "AxiomAuditFixture"],
        cwd=tmp_path,
        capture_output=True,
        text=True,
        timeout=120.0,
        check=False,
    )
    assert build.returncode == 0, build.stdout + build.stderr
    theorems = [
        "AxiomAuditFixture.audit_decide",
        "AxiomAuditFixture.audit_choice",
        "AxiomAuditFixture.audit_user_axiom",
        "AxiomAuditFixture.audit_native",
    ]

    results = axiom_audit.run_axiom_audit(
        tmp_path,
        ["AxiomAuditFixture"],
        theorems,
        tmp_path / "axiom_audit.log",
        120.0,
    )

    assert results["AxiomAuditFixture.audit_decide"]["status"] == "passed"
    assert results["AxiomAuditFixture.audit_choice"]["status"] == "passed"
    assert "Classical.choice" in results["AxiomAuditFixture.audit_choice"]["axioms"]
    assert results["AxiomAuditFixture.audit_user_axiom"]["status"] == "rejected"
    assert (
        "AxiomAuditFixture.localAuditAxiom"
        in results["AxiomAuditFixture.audit_user_axiom"]["disallowed"]
    )
    native = results["AxiomAuditFixture.audit_native"]
    assert native["status"] == "rejected"
    assert "Lean.ofReduceBool" in native["disallowed"]


@pytest.mark.lake_available
def test_failed_module_rebuild_blocks_stale_olean_audit(
    lake_available, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
):
    repo_dir = tmp_path / "lean-project"
    generated_dir = repo_dir / "generated"
    generated_root = generated_dir / "Generated"
    generated_root.mkdir(parents=True)
    (repo_dir / "lean-toolchain").write_text(
        (REPO_ROOT / "lean-toolchain").read_text()
    )
    (repo_dir / "lakefile.lean").write_text(
        "import Lake\n"
        "open Lake DSL\n"
        "package staleOleanRegression where\n"
        "lean_lib Generated where\n"
        "  srcDir := \"generated\"\n"
        "  globs := #[.andSubmodules `Generated]\n"
    )
    (generated_dir / "Generated.lean").write_text(
        "namespace Generated\nend Generated\n"
    )

    token = uuid.uuid4().hex[:8]
    module_key = f"ci_stale_olean_probe_{token}"
    atom_name = f"stale_olean_atom_{token}"
    atom = bridge.collect_unknown_atoms(
        _bridge_test_cert(f"{module_key}.mm", [atom_name])
    )[0]
    module = bridge._module_to_lean_namespace(module_key, "Generated")
    theorem_name = bridge._lean_theorem_name(atom_name)
    theorem = f"{module}.{theorem_name}"
    module_path = generated_dir / Path(*module.split(".")).with_suffix(".lean")
    module_path.parent.mkdir(parents=True, exist_ok=True)
    module_path.write_text(
        f"namespace {module}\n"
        f"theorem {theorem_name} : True := by\n"
        "  trivial\n"
        f"end {module}\n"
    )

    build_command = bridge._lake_build_command(repo_dir, module)
    assert build_command is not None
    good_build = subprocess.run(
        build_command,
        cwd=repo_dir,
        capture_output=True,
        text=True,
        timeout=60.0,
        check=False,
    )
    assert good_build.returncode == 0, good_build.stdout + good_build.stderr
    olean_path = (
        repo_dir
        / ".lake"
        / "build"
        / "lib"
        / Path(*module.split(".")).with_suffix(".olean")
    )
    assert olean_path.exists()

    axiom_name = f"local_stale_axiom_{token}"
    broken_name = f"broken_decl_{token}"
    module_path.write_text(
        f"namespace {module}\n"
        f"axiom {axiom_name} : True\n"
        f"theorem {theorem_name} : True := {axiom_name}\n"
        f"theorem {broken_name} : False := True.intro\n"
        f"end {module}\n"
    )
    failed_build = subprocess.run(
        build_command,
        cwd=repo_dir,
        capture_output=True,
        text=True,
        timeout=60.0,
        check=False,
    )
    assert failed_build.returncode != 0, failed_build.stdout + failed_build.stderr
    assert olean_path.exists()

    audit_source = tmp_path / "StaleOleanAudit.lean"
    audit_source.write_text(f"import {module}\n#print axioms {theorem}\n")
    lake_prefix = bridge._lake_command_prefix(repo_dir)
    assert lake_prefix is not None
    stale_audit = subprocess.run(
        [*lake_prefix, "env", "lean", str(audit_source)],
        cwd=repo_dir,
        capture_output=True,
        text=True,
        timeout=60.0,
        check=False,
    )
    assert stale_audit.returncode == 0, stale_audit.stdout + stale_audit.stderr
    assert f"'{theorem}' does not depend on any axioms" in stale_audit.stdout

    def unexpected_audit(*_args, **_kwargs):  # noqa: ANN002, ANN003
        raise AssertionError("a failed module rebuild must skip axiom auditing")

    monkeypatch.setattr(bridge, "run_axiom_audit", unexpected_audit)
    proved = [[atom_name]]
    failed = [[]]
    results, results_by_atom = bridge._audit_proved_atoms(
        [[atom]],
        proved,
        failed,
        1,
        repo_dir,
        tmp_path / "audit-output",
        "Generated",
    )

    assert results[theorem]["status"] == "error"
    assert results_by_atom[bridge._atom_key(atom)]["status"] == "error"
    assert failed == [[atom_name]]
    assert "type mismatch" in (
        tmp_path
        / "audit-output"
        / "axiom_audit_logs"
        / f"{module.replace('.', '_')}.build.log"
    ).read_text()
