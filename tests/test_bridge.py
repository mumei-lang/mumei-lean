"""Tests for ``scripts.bridge``."""
from __future__ import annotations

import json
import os
import shutil
import subprocess
from pathlib import Path
from types import SimpleNamespace

import pytest

import bridge
from bridge import _scan_unknown_certs, main


def _atom(name: str, z3: str = "unknown") -> dict:
    return {
        "name": name,
        "requires": "x > 0",
        "ensures": "result >= x",
        "z3_check_result": z3,
        "status": "unknown" if z3 == "unknown" else "verified",
        "content_hash": "h",
        "proof_hash": "p",
        "dependencies": [],
        "effects": [],
    }


def _lake_env() -> dict[str, str]:
    env = os.environ.copy()
    elan_bin = Path.home() / ".elan" / "bin"
    env["PATH"] = f"{elan_bin}:{env.get('PATH', '')}"
    return env


def _have_lake() -> bool:
    return shutil.which("lake", path=_lake_env()["PATH"]) is not None


def _cert(file: str, atoms: list) -> dict:
    return {
        "version": "1.0",
        "timestamp": "2026-04-28T00:00:00Z",
        "mumei_version": "0.6.12",
        "z3_version": "4.12.2",
        "file": file,
        "atoms": atoms,
        "package_name": "x",
        "package_version": "0",
        "certificate_hash": "",
        "all_verified": False,
    }


def test_scan_unknown_certs_finds_only_unknown(tmp_path: Path):
    certs_dir = tmp_path / "std" / "certs"
    certs_dir.mkdir(parents=True)
    (certs_dir / "ok.json").write_text(
        json.dumps(_cert("std/ok.mm", [_atom("a", z3="unsat")]))
    )
    (certs_dir / "status_only.json").write_text(
        json.dumps(
            _cert(
                "std/status_only.mm",
                [
                    {
                        **_atom("status_only", z3="unsat"),
                        "status": "unknown",
                        "escalation_reason": "manual_review_requested",
                    }
                ],
            )
        )
    )
    (certs_dir / "todo.json").write_text(
        json.dumps(_cert("std/todo.mm", [_atom("b", z3="unknown")]))
    )
    (certs_dir / "class_unknown.json").write_text(
        json.dumps(
            _cert(
                "std/class_unknown.mm",
                [
                    {
                        **_atom("class_unknown", z3="unsat"),
                        "z3_result_class": "unknown",
                    }
                ],
            )
        )
    )
    found = _scan_unknown_certs(certs_dir)
    assert [p.name for p, _ in found] == [
        "class_unknown.json",
        "todo.json",
    ]


def test_select_proof_strategy_uses_translator_ir_lowering_rules():
    atom = SimpleNamespace(
        translator_ir={
            "lowering_rules": [
                "finite_field_lowering",
                "crypto_primitive_lowering",
                "implication_lowering",
            ],
            "proof_trace_hints": ["try finite-field closure lemmas"],
        }
    )

    strategy = bridge.select_proof_strategy(atom)

    assert strategy["strategy"] == "finite_field+crypto+implication"
    assert strategy["imports"] == [
        "MumeiLean.Algebra",
        "MumeiLean.Crypto",
        "MumeiLean.Quantifiers",
    ]
    assert "try finite-field closure lemmas" in strategy["hints"]


def test_resolve_mathlib_imports_from_lowering_rules():
    atom = SimpleNamespace(
        translator_ir={
            "lowering_rules": [
                "finite_field_lowering",
                "group_theory_lowering",
                "crypto_primitive_lowering",
            ]
        }
    )

    imports = bridge.resolve_mathlib_imports(atom)

    assert imports == [
        "import Mathlib.Algebra.Group.Basic",
        "import Mathlib.Data.Int.ModEq",
        "import Mathlib.Data.Nat.Totient",
        "import Mathlib.Data.ZMod.Basic",
    ]


def test_main_dry_run_writes_generated_files(tmp_path: Path):
    cert_path = tmp_path / "cert.json"
    cert_path.write_text(
        json.dumps(_cert("std/math.mm", [_atom("inc", z3="unknown")]))
    )
    out_dir = tmp_path / "generated"
    rc = main(
        [
            "--cert", str(cert_path),
            "--out-dir", str(out_dir),
            "--module-prefix", "Gen",
            "--no-build",
        ]
    )
    assert rc == 0
    assert (out_dir / "Gen" / "Std" / "Math.lean").exists()


def test_main_dry_run_generates_theorems_for_unknown_only(tmp_path: Path):
    cert_path = tmp_path / "cert.json"
    cert_path.write_text(
        json.dumps(
            _cert(
                "std/math.mm",
                [
                    _atom("open_obligation", z3="unknown"),
                    _atom("closed_obligation", z3="unsat"),
                ],
            )
        )
    )
    out_dir = tmp_path / "generated"

    rc = main(
        [
            "--cert",
            str(cert_path),
            "--out-dir",
            str(out_dir),
            "--module-prefix",
            "Gen",
            "--no-build",
        ]
    )

    assert rc == 0
    text = (out_dir / "Gen" / "Std" / "Math.lean").read_text(encoding="utf-8")
    assert "open_obligation_correct" in text
    assert "closed_obligation_correct" not in text


def test_main_dry_run_with_pilot_fixture(tmp_path: Path):
    """PR 3: end-to-end pilot of forall(..) + arr[i] translation.

    The fixture under ``tests/fixtures/pilot_proof_cert.json`` carries
    two ``unknown`` atoms (``pilot_array_identity``, ``pilot_array_offset``)
    whose contracts use the new ``forall`` and ``arr[i]`` shapes. A
    dry-run bridge invocation must produce a Lean source file that
    references both translated theorems and contains no UNK / sorry
    fallbacks for the contract bodies themselves.
    """
    fixture = (
        Path(__file__).resolve().parent / "fixtures" / "pilot_proof_cert.json"
    )
    out_dir = tmp_path / "generated"
    rc = main(
        [
            "--cert", str(fixture),
            "--out-dir", str(out_dir),
            "--module-prefix", "Generated",
            "--no-build",
        ]
    )
    assert rc == 0
    pilot_lean = out_dir / "Generated" / "Std" / "Pilot.lean"
    assert pilot_lean.exists(), f"expected {pilot_lean} to be written"
    text = pilot_lean.read_text()
    # Both atoms produced theorem declarations.
    assert "pilot_array_identity_correct" in text
    assert "pilot_array_offset_correct" in text
    # Translator emitted the new forall / arr[i] shapes (Unicode ∀ + parens).
    assert "∀ i : Int" in text
    # PR 4: ``arr`` is used in ``arr[i]`` position which lowers to
    # ``arr.get! i`` (List.get! semantics), so it must be typed as a
    # ``List Int``, not a scalar ``Int``. Otherwise the generated
    # theorem fails to type-check (cannot call ``.get!`` on an Int).
    assert "(arr : List Int)" in text, text
    # And the lowered ``arr.get! i`` form must appear in the body.
    assert "arr.get!" in text, text
    # Neither atom should be flagged as a partial / unproven translation:
    # both are entirely within the v1+forall+arr[i] surface.
    assert "TODO: unproven" not in text


def test_main_dry_run_with_len_function_contract(tmp_path: Path):
    cert_path = tmp_path / "cert.json"
    cert_path.write_text(
        json.dumps(
            _cert(
                "std/functions.mm",
                [
                    {
                        **_atom("len_guard", z3="unknown"),
                        "requires": "n >= 0",
                        "ensures": "len(arr) >= n",
                    }
                ],
            )
        )
    )
    out_dir = tmp_path / "generated"
    rc = main(
        [
            "--cert", str(cert_path),
            "--out-dir", str(out_dir),
            "--module-prefix", "Generated",
            "--no-build",
        ]
    )
    assert rc == 0
    text = (out_dir / "Generated" / "Std" / "Functions.lean").read_text()
    assert "open MumeiLean" in text
    assert "mumei_len arr" in text
    assert "TODO: unproven" not in text


def test_main_dry_run_with_body_semantics_fixture(tmp_path: Path):
    fixture = Path(__file__).resolve().parent / "fixtures" / "std_math_abs.proof-cert.json"
    out_dir = tmp_path / "generated"
    rc = main(
        [
            "--cert", str(fixture),
            "--out-dir", str(out_dir),
            "--module-prefix", "Generated",
            "--no-build",
        ]
    )
    assert rc == 0
    text = (out_dir / "Generated" / "Std" / "Math" / "Abs.lean").read_text()
    assert "known_witness_used=true" not in text
    assert "h_body : result = absSaturatingResult x" in text
    assert "def absSaturatingResult (x : Int) : Int :=" in text
    assert "exact MumeiLean.StdMathAbs.abs_saturating_correct" not in text
    assert "sorry" not in text


def test_main_dry_run_with_bounded_mul_body_semantics_fixture(tmp_path: Path):
    fixture = (
        Path(__file__).resolve().parent
        / "fixtures"
        / "std_math_patterns_bounded_mul.proof-cert.json"
    )
    out_dir = tmp_path / "generated"
    rc = main(
        [
            "--cert", str(fixture),
            "--out-dir", str(out_dir),
            "--module-prefix", "Generated",
            "--no-build",
        ]
    )
    assert rc == 0
    text = (out_dir / "Generated" / "Std" / "Math" / "Patterns.lean").read_text()
    assert "known_witness_used=true" not in text
    assert "def boundedMulWithOverflowCheckResult" in text
    assert "h_body : result = boundedMulWithOverflowCheckResult a b limit" in text
    assert "mumei_arith_deep" in text
    assert "sorry" not in text


def test_main_dry_run_with_crypto_body_semantics_fixture(tmp_path: Path):
    fixture = (
        Path(__file__).resolve().parent
        / "fixtures"
        / "std_crypto_primitives_constant_time_eq.proof-cert.json"
    )
    out_dir = tmp_path / "generated"
    rc = main(
        [
            "--cert", str(fixture),
            "--out-dir", str(out_dir),
            "--module-prefix", "Generated",
            "--no-build",
        ]
    )
    assert rc == 0
    text = (out_dir / "Generated" / "Std" / "Crypto" / "Primitives.lean").read_text()
    assert "known_witness_used=true" not in text
    assert "def constantTimeEqFlagResult" in text
    assert "if left = right then 1 else 0" in text
    assert "h_body : result = constantTimeEqFlagResult left right" in text
    assert "mumei_arith_deep" in text
    assert "sorry" not in text


def test_main_dry_run_with_finite_field_body_semantics_fixture(tmp_path: Path):
    fixture = (
        Path(__file__).resolve().parent
        / "fixtures"
        / "std_algebra_finite_field_ff_zero_eq_zero.proof-cert.json"
    )
    out_dir = tmp_path / "generated"
    rc = main(
        [
            "--cert", str(fixture),
            "--out-dir", str(out_dir),
            "--module-prefix", "Generated",
            "--no-build",
        ]
    )
    assert rc == 0
    text = (
        out_dir / "Generated" / "Std" / "Algebra" / "Finite_field.lean"
    ).read_text()
    assert "known_witness_used=true" not in text
    assert "def ffZeroEqZeroResult" in text
    assert "MumeiLean.Algebra.mumei_ff_zero p" in text
    assert "h_body : result = ffZeroEqZeroResult p" in text
    assert "MumeiLean.Algebra.ff_eq_refl 0 p" in text
    assert "sorry" not in text


@pytest.mark.skipif(not _have_lake(),
                    reason="lake not on PATH; skipping live bridge E2E")
@pytest.mark.skipif(os.environ.get("MUMEI_LEAN_SKIP_LIVE") == "1",
                    reason="MUMEI_LEAN_SKIP_LIVE=1 set")
@pytest.mark.lake_available
def test_body_semantics_bridge_e2e_exports_lean_verified(tmp_path: Path):
    fixture = Path(__file__).resolve().parent / "fixtures" / "std_math_abs.proof-cert.json"
    out_cert = tmp_path / "std_math_abs.lean-cert.json"
    repo_root = Path(__file__).resolve().parents[1]
    rc = main(
        [
            "--cert", str(fixture),
            "--out-dir", str(repo_root / "generated"),
            "--repo-dir", str(repo_root),
            "--lean-cert-out", str(out_cert),
            "--module-prefix", "Generated",
        ]
    )
    assert rc == 0
    payload = json.loads(out_cert.read_text())
    atom = next(a for a in payload["atoms"] if a["name"] == "abs_saturating")
    assert atom["z3_check_result"] == "lean_verified"
    assert atom["status"] == "verified"
    assert atom["lean_metadata"]["lean_theorem_name"] == (
        "Generated.Std.Math.Abs.abs_saturating_correct"
    )
    assert atom["lean_metadata"]["known_witness_used"] is False


def test_body_semantics_export_path_marks_verified_with_clean_lake_log(
    tmp_path: Path, monkeypatch
):
    fixture = Path(__file__).resolve().parent / "fixtures" / "std_math_abs.proof-cert.json"
    out_cert = tmp_path / "std_math_abs.lean-cert.json"
    _patch_lake(monkeypatch, rc=0, log="")
    rc = main(
        [
            "--cert", str(fixture),
            "--out-dir", str(tmp_path / "generated"),
            "--lean-cert-out", str(out_cert),
            "--module-prefix", "Generated",
        ]
    )
    assert rc == 0
    payload = json.loads(out_cert.read_text())
    atom = next(a for a in payload["atoms"] if a["name"] == "abs_saturating")
    assert atom["z3_check_result"] == "lean_verified"
    assert atom["lean_metadata"]["proof_path"].endswith(
        "Generated/Std/Math/Abs.lean"
    )
    assert atom["lean_metadata"]["lean_module"] == "Generated.Std.Math.Abs"
    assert (
        atom["lean_metadata"]["lean_theorem_name"]
        == "Generated.Std.Math.Abs.abs_saturating_correct"
    )
    assert atom["lean_metadata"]["known_witness_used"] is False


def test_candidate_status_accepts_generated_theorem_names():
    atom = SimpleNamespace(
        name="abs_saturating",
        module_key="std/math/abs",
        translator_version=bridge.TRANSLATOR_VERSION,
        bridge_lemma_hash=bridge.BRIDGE_LEMMA_HASH,
        manual_lemma_reason=None,
        is_partial_translation=False,
        requires_translation=SimpleNamespace(is_partial=False),
        ensures_translation=SimpleNamespace(is_partial=False),
        body_translation=None,
    )

    status = bridge._candidate_status(
        atom,
        ["Generated.Std.Math.Abs.abs_saturating_correct"],
        [],
    )

    assert status == "lean_verified"


@pytest.mark.parametrize(
    ("field", "value"),
    [
        ("translator_version", "stale-translator-version"),
        ("bridge_lemma_hash", "stale-bridge-lemma-hash"),
    ],
)
def test_stale_source_contract_is_not_lean_verified(
    tmp_path: Path,
    field: str,
    value: str,
):
    cert_path = tmp_path / "cert.json"
    cert_path.write_text(
        json.dumps(
            _cert(
                "std/math.mm",
                [
                    {
                        **_atom("inc", z3="unknown"),
                        field: value,
                    }
                ],
            )
        )
    )
    out_cert = tmp_path / "out.lean-cert.json"

    rc = main(
        [
            "--cert", str(cert_path),
            "--out-dir", str(tmp_path / "generated"),
            "--module-prefix", "Generated",
            "--lean-cert-out", str(out_cert),
            "--no-build",
        ]
    )

    assert rc == 0
    payload = json.loads(out_cert.read_text())
    atom = payload["atoms"][0]
    assert atom["z3_check_result"] == "unknown"
    assert atom["lean_metadata"]["status"] == "stale_translator"
    assert atom["lean_result_metadata"]["status"] == "stale_translator"


def test_stale_source_contract_both_fields_is_not_lean_verified(
    tmp_path: Path,
):
    """Both translator_version and bridge_lemma_hash stale at once must still
    resolve to stale_translator (not a partial/accidental promotion)."""
    cert_path = tmp_path / "cert.json"
    cert_path.write_text(
        json.dumps(
            _cert(
                "std/math.mm",
                [
                    {
                        **_atom("inc", z3="unknown"),
                        "translator_version": "stale-translator-version",
                        "bridge_lemma_hash": "stale-bridge-lemma-hash",
                    }
                ],
            )
        )
    )
    out_cert = tmp_path / "out.lean-cert.json"

    rc = main(
        [
            "--cert", str(cert_path),
            "--out-dir", str(tmp_path / "generated"),
            "--module-prefix", "Generated",
            "--lean-cert-out", str(out_cert),
            "--no-build",
        ]
    )

    assert rc == 0
    payload = json.loads(out_cert.read_text())
    atom = payload["atoms"][0]
    assert atom["z3_check_result"] == "unknown"
    assert atom["lean_metadata"]["status"] == "stale_translator"
    assert atom["lean_result_metadata"]["status"] == "stale_translator"


def test_stale_lean_result_contract_is_not_lean_verified(
    tmp_path: Path,
    monkeypatch,
):
    cert_path = tmp_path / "cert.json"
    cert_path.write_text(
        json.dumps(_cert("std/math.mm", [_atom("inc", z3="unknown")]))
    )
    out_cert = tmp_path / "out.lean-cert.json"
    monkeypatch.setattr(bridge, "TRANSLATOR_VERSION", "stale-translator-version")

    rc = main(
        [
            "--cert", str(cert_path),
            "--out-dir", str(tmp_path / "generated"),
            "--module-prefix", "Generated",
            "--lean-cert-out", str(out_cert),
            "--no-build",
        ]
    )

    assert rc == 0
    payload = json.loads(out_cert.read_text())
    atom = payload["atoms"][0]
    assert atom["z3_check_result"] == "unknown"
    assert atom["lean_metadata"]["status"] == "stale_translator"
    assert atom["lean_metadata"]["translator_version"] == "stale-translator-version"


def test_main_scan_unknown_returns_zero_when_dir_empty(tmp_path: Path):
    rc = main(
        [
            "--scan-unknown", str(tmp_path),
            "--out-dir", str(tmp_path / "g"),
            "--no-build",
            "--no-export",
        ]
    )
    assert rc == 0


def test_main_scan_unknown_writes_summary_json(tmp_path: Path):
    """``--summary-json`` aggregates discovered unknown atoms by module."""
    certs_dir = tmp_path / "std" / "certs"
    certs_dir.mkdir(parents=True)
    (certs_dir / "list.json").write_text(
        json.dumps(
            _cert(
                "std/list.mm",
                [_atom("a", z3="unknown"), _atom("b", z3="unsat")],
            )
        )
    )
    (certs_dir / "math.json").write_text(
        json.dumps(_cert("std/math.mm", [_atom("c", z3="unknown")]))
    )
    summary = tmp_path / "summary.json"
    rc = main(
        [
            "--scan-unknown", str(tmp_path),
            "--out-dir", str(tmp_path / "g"),
            "--summary-json", str(summary),
            "--no-build",
            "--no-export",
        ]
    )
    assert rc == 0
    payload = json.loads(summary.read_text())
    assert payload["total_unknown"] == 2
    by_module = {m["module"]: m for m in payload["modules"]}
    assert set(by_module) == {"std/list", "std/math"}
    assert by_module["std/list"]["unknown_count"] == 1
    assert by_module["std/list"]["atoms"] == ["a"]
    assert by_module["std/math"]["unknown_count"] == 1
    assert by_module["std/math"]["atoms"] == ["c"]
    assert payload["harness_contract"]["policy"] == "mumei-lean-bridge-harness/v1"
    assert payload["harness_contract"]["input_kind"] == "scan_unknown"


def test_main_scan_unknown_writes_empty_summary_when_dir_empty(tmp_path: Path):
    """Empty scans still produce a summary so CI artefacts are stable."""
    summary = tmp_path / "summary.json"
    rc = main(
        [
            "--scan-unknown", str(tmp_path),
            "--out-dir", str(tmp_path / "g"),
            "--summary-json", str(summary),
            "--no-build",
            "--no-export",
        ]
    )
    assert rc == 0
    payload = json.loads(summary.read_text())
    assert payload["total_unknown"] == 0
    assert payload["modules"] == []
    assert payload["ci_mode_fallback"] is False
    assert payload["harness_contract"]["policy"] == "mumei-lean-bridge-harness/v1"


def _patch_lake(monkeypatch, rc: int, log: str) -> None:
    """Replace :func:`bridge._run_lake_build` with a deterministic stub."""

    def fake_run(repo_dir: Path, log_path: Path) -> tuple[int, float]:
        log_path.parent.mkdir(parents=True, exist_ok=True)
        log_path.write_text(log)
        return rc, 0.5

    monkeypatch.setattr(bridge, "_run_lake_build", fake_run)


def test_run_lake_build_uses_pinned_toolchain_when_elan_available(
    tmp_path: Path, monkeypatch
):
    (tmp_path / "lean-toolchain").write_text("leanprover/lean4:v4.15.0\n")
    log_path = tmp_path / "lake_build.log"
    calls: list[list[str]] = []

    def fake_which(name: str) -> str | None:
        return f"/mock/bin/{name}" if name in {"elan", "lake"} else None

    def fake_run(cmd, cwd, capture_output, text):  # noqa: ANN001
        calls.append(cmd)
        assert cwd == tmp_path
        assert capture_output is True
        assert text is True
        return subprocess.CompletedProcess(cmd, 0, stdout="ok\n", stderr="")

    monkeypatch.setattr(bridge.shutil, "which", fake_which)
    monkeypatch.setattr(bridge.subprocess, "run", fake_run)

    rc, elapsed = bridge._run_lake_build(tmp_path, log_path)
    assert rc == 0
    assert elapsed is not None and elapsed >= 0
    assert calls == [["/mock/bin/elan", "run", "leanprover/lean4:v4.15.0", "lake", "build"]]
    assert log_path.read_text() == "ok\n"


def test_run_lake_build_falls_back_to_lake_without_toolchain(
    tmp_path: Path, monkeypatch
):
    log_path = tmp_path / "lake_build.log"
    calls: list[list[str]] = []

    def fake_which(name: str) -> str | None:
        return "/mock/bin/lake" if name == "lake" else None

    def fake_run(cmd, cwd, capture_output, text):  # noqa: ANN001
        calls.append(cmd)
        return subprocess.CompletedProcess(cmd, 0, stdout="", stderr="done\n")

    monkeypatch.setattr(bridge.shutil, "which", fake_which)
    monkeypatch.setattr(bridge.subprocess, "run", fake_run)

    rc, elapsed = bridge._run_lake_build(tmp_path, log_path)
    assert rc == 0
    assert elapsed is not None and elapsed >= 0
    assert calls == [["lake", "build"]]
    assert log_path.read_text() == "done\n"


def test_run_lake_build_reports_no_timing_when_lake_missing(
    tmp_path: Path, monkeypatch
):
    log_path = tmp_path / "lake_build.log"
    monkeypatch.setattr(bridge.shutil, "which", lambda name: None)

    rc, elapsed = bridge._run_lake_build(tmp_path, log_path)

    assert rc == 127
    assert elapsed is None


def test_escalation_timing_propagates_to_metadata_and_summary(
    tmp_path: Path, monkeypatch
):
    """The measured `lake build` time reaches mumei's benchmark surface."""
    bundle_path = tmp_path / "vstd_settlement.escalation-bundle.json"
    bundle_path.write_text(
        json.dumps(
            {
                "version": "1.0",
                "file": "std/settlement.mm",
                "summary": {},
                "candidates": [
                    {
                        **_atom("balance_conservation", z3="unknown"),
                        "requires": "amount > 0 && from_balance >= amount",
                        "ensures": "from_balance - amount >= 0",
                        "z3_result_class": "unknown",
                        "escalation_reason": "z3_unknown",
                        "logic_fragment_tags": ["linear_arithmetic"],
                    }
                ],
            }
        )
    )
    out_cert = tmp_path / "out.lean-cert.json"
    summary = tmp_path / "summary.json"
    _patch_lake(monkeypatch, rc=0, log="")

    rc = main(
        [
            "--escalation-bundle", str(bundle_path),
            "--out-dir", str(tmp_path / "generated"),
            "--module-prefix", "Generated",
            "--lean-cert-out", str(out_cert),
            "--summary-json", str(summary),
        ]
    )

    assert rc == 0
    candidate = json.loads(out_cert.read_text())["candidates"][0]
    assert candidate["lean_result_metadata"]["lean_solver_time_s"] == 0.5
    assert json.loads(summary.read_text())["lean_fallback"][
        "lean_solver_time_s"
    ] == 0.5


def test_escalation_timing_is_none_on_dry_run(tmp_path: Path):
    bundle_path = tmp_path / "vstd_settlement.escalation-bundle.json"
    bundle_path.write_text(
        json.dumps(
            {
                "version": "1.0",
                "file": "std/settlement.mm",
                "summary": {},
                "candidates": [
                    {
                        **_atom("balance_conservation", z3="unknown"),
                        "requires": "amount > 0",
                        "ensures": "amount >= 0",
                        "z3_result_class": "unknown",
                        "escalation_reason": "z3_unknown",
                    }
                ],
            }
        )
    )
    summary = tmp_path / "summary.json"

    rc = main(
        [
            "--escalation-bundle", str(bundle_path),
            "--out-dir", str(tmp_path / "generated"),
            "--module-prefix", "Generated",
            "--summary-json", str(summary),
            "--no-build",
            "--no-export",
        ]
    )

    assert rc == 0
    payload = json.loads(summary.read_text())
    assert payload["lean_fallback"]["lean_solver_time_s"] is None


def test_verify_known_witnesses_requires_canonical_module(
    tmp_path: Path, monkeypatch
):
    source = tmp_path / "MumeiLean" / "StdMathAbs.lean"
    source.parent.mkdir(parents=True)
    source.write_text(
        "theorem abs_saturating_correct : True := by trivial\n"
        "theorem list_length_correct : True := by trivial\n"
    )
    calls: list[list[str]] = []

    def fake_which(name: str) -> str | None:
        return "/mock/bin/lake" if name == "lake" else None

    def fake_run(cmd, cwd, capture_output, text):  # noqa: ANN001
        calls.append(cmd)
        assert cwd == tmp_path
        return subprocess.CompletedProcess(cmd, 0, stdout="", stderr="")

    monkeypatch.setattr(bridge.shutil, "which", fake_which)
    monkeypatch.setattr(bridge.subprocess, "run", fake_run)

    proved = bridge._verify_known_witnesses(
        [
            SimpleNamespace(name="abs_saturating", module_key="custom/math"),
            SimpleNamespace(name="list_length", module_key="std/list"),
        ],
        tmp_path,
        tmp_path / "logs",
    )

    assert proved == [("std/list", "list_length")]
    assert calls == [["lake", "build", "MumeiLean.StdMathAbs"]]


def test_verify_known_witnesses_builds_domain_witness_modules(
    tmp_path: Path, monkeypatch
):
    witnesses = [
        ("balance_conservation", "std/finance/settlement", "MumeiLean.Settlement"),
        (
            "trace_balance_conservation",
            "std/finance/settlement",
            "MumeiLean.Settlement",
        ),
        (
            "no_settlement_without_validate",
            "std/finance/settlement",
            "MumeiLean.Settlement",
        ),
        (
            "no_reentrancy_after_withdraw",
            "std/contract/vault",
            "MumeiLean.SmartContract",
        ),
        (
            "withdraw_preserves_other_balance",
            "std/contract/vault",
            "MumeiLean.SmartContract",
        ),
        (
            "withdraw_amount_nonnegative_bound",
            "std/contract/vault",
            "MumeiLean.SmartContract",
        ),
        (
            "nlae_vault_withdraw_amount_nonnegative_bound",
            "examples/nlae_integration_demo",
            "MumeiLean.SmartContract",
        ),
        (
            "nlae_vault_no_negative_withdraw",
            "examples/nlae_integration_demo",
            "MumeiLean.SmartContract",
        ),
        ("add_bounded", "std/math/patterns", "MumeiLean.Patterns"),
        ("transfer_preserves_sum", "std/math/patterns", "MumeiLean.Patterns"),
    ]
    for module in {module for _, _, module in witnesses}:
        source = tmp_path / Path(*module.split(".")).with_suffix(".lean")
        source.parent.mkdir(parents=True, exist_ok=True)
        theorem_lines = [
            f"theorem {name} : True := by trivial\n"
            for name, _, witness_module in witnesses
            if witness_module == module
        ]
        source.write_text("".join(theorem_lines))
    calls: list[list[str]] = []

    def fake_which(name: str) -> str | None:
        return "/mock/bin/lake" if name == "lake" else None

    def fake_run(cmd, cwd, capture_output, text):  # noqa: ANN001
        calls.append(cmd)
        assert cwd == tmp_path
        assert capture_output is True
        assert text is True
        return subprocess.CompletedProcess(cmd, 0, stdout="", stderr="")

    monkeypatch.setattr(bridge.shutil, "which", fake_which)
    monkeypatch.setattr(bridge.subprocess, "run", fake_run)

    proved = bridge._verify_known_witnesses(
        [
            SimpleNamespace(name=name, module_key=module_key)
            for name, module_key, _ in witnesses
        ],
        tmp_path,
        tmp_path / "logs",
    )

    assert set(proved) == {(module_key, name) for name, module_key, _ in witnesses}
    assert calls == [
        ["lake", "build", "MumeiLean.Patterns"],
        ["lake", "build", "MumeiLean.Settlement"],
        ["lake", "build", "MumeiLean.SmartContract"],
    ]


def test_known_witness_adds_partial_atom_to_proved_payload(
    tmp_path: Path, monkeypatch
):
    cert_path = tmp_path / "cert.json"
    atom = {
        **_atom("list_length", z3="unknown"),
        "requires": "foo(x)",
        "ensures": "result >= 0",
    }
    cert_path.write_text(json.dumps(_cert("std/list.mm", [atom])))
    out_cert = tmp_path / "out.lean-cert.json"
    _patch_lake(monkeypatch, rc=1, log="error: cannot resolve dependency 'mathlib'\n")
    monkeypatch.setattr(
        bridge,
        "_verify_known_witnesses",
        lambda atoms, repo_dir, log_dir: [("std/list", "list_length")],
    )

    rc = main(
        [
            "--cert", str(cert_path),
            "--out-dir", str(tmp_path / "generated"),
            "--module-prefix", "Generated",
            "--lean-cert-out", str(out_cert),
        ]
    )

    assert rc == 0
    upgraded = json.loads(out_cert.read_text())
    list_length = next(a for a in upgraded["atoms"] if a["name"] == "list_length")
    assert list_length["z3_check_result"] == "lean_verified"
    assert list_length["lean_metadata"]["status"] == "lean_verified"


def test_main_escalation_bundle_exports_metrics_and_metadata(
    tmp_path: Path, monkeypatch
):
    bundle_path = tmp_path / "math.escalation-bundle.json"
    bundle_path.write_text(
        json.dumps(
            {
                "version": "1.0",
                "file": "std/math.mm",
                "summary": {},
                "candidates": [
                    {
                        **_atom("inc", z3="unknown"),
                        "z3_result_class": "unknown",
                        "escalation_reason": "z3_unknown",
                        "logic_fragment_tag": "quantified_formula",
                        "logic_fragment_tags": ["quantifier_alternation"],
                    }
                ],
            }
        )
    )
    out_cert = tmp_path / "out.lean-cert.json"
    summary = tmp_path / "summary.json"
    _patch_lake(monkeypatch, rc=0, log="")

    rc = main(
        [
            "--ingest-bundle", str(bundle_path),
            "--out-dir", str(tmp_path / "generated"),
            "--module-prefix", "Generated",
            "--lean-cert-out", str(out_cert),
            "--summary-json", str(summary),
        ]
    )

    assert rc == 0
    upgraded = json.loads(out_cert.read_text())
    candidate = upgraded["candidates"][0]
    assert candidate["z3_check_result"] == "lean_verified"
    assert candidate["lean_metadata"]["status"] == "lean_verified"
    assert candidate["lean_metadata"]["z3_result_class"] == "unknown"
    assert candidate["lean_metadata"]["escalation_reason"] == "z3_unknown"
    assert candidate["lean_metadata"]["logic_fragment_tag"] == "quantified_formula"
    assert candidate["lean_metadata"]["logic_fragment_tags"] == ["quantifier_alternation"]
    assert candidate["lean_result_metadata"]["status"] == "lean_verified"
    assert "escalation_reason=z3_unknown" in candidate["lean_metadata"]["diagnostics"]
    assert upgraded["harness_contract"]["policy"] == "mumei-lean-bridge-harness/v1"
    assert candidate["lean_metadata"]["harness"]["failure_taxonomy"] == "proved"
    metrics = json.loads(summary.read_text())["metrics"]
    assert metrics["escalation_attempts"] == 1
    assert metrics["lean_successes"] == 1
    assert metrics["by_logic_fragment"]["quantifier_alternation"]["success_rate"] == 1.0
    assert metrics["by_z3_result_class"]["unknown"]["success_rate"] == 1.0


def test_main_escalation_bundle_defaults_lean_cert_out(
    tmp_path: Path, monkeypatch
):
    bundle_path = tmp_path / "vstd_settlement.escalation-bundle.json"
    bundle_path.write_text(
        json.dumps(
            {
                "version": "1.0",
                "file": "std/settlement.mm",
                "summary": {},
                "candidates": [
                    {
                        **_atom("balance_conservation", z3="unknown"),
                        "requires": "amount > 0 && from_balance >= amount",
                        "ensures": "(from_balance - amount) + (to_balance + amount) == from_balance + to_balance",
                        "z3_result_class": "unknown",
                        "escalation_reason": "z3_unknown_global_balance_conservation",
                        "logic_fragment_tags": ["linear_arithmetic", "settlement"],
                    }
                ],
            }
        )
    )
    _patch_lake(monkeypatch, rc=0, log="")
    monkeypatch.chdir(tmp_path)

    rc = main(["--escalation-bundle", str(bundle_path)])

    assert rc == 0
    out_cert = tmp_path / "out" / "vstd_settlement.lean-cert.json"
    candidate = json.loads(out_cert.read_text())["candidates"][0]
    assert candidate["z3_check_result"] == "lean_verified"


def test_main_escalation_bundle_includes_solver_heatmap_metadata(
    tmp_path: Path, monkeypatch
):
    bundle_path = tmp_path / "math.escalation-bundle.json"
    bundle_path.write_text(
        json.dumps(
            {
                "version": "1.0",
                "file": "std/math.mm",
                "summary": {},
                "candidates": [
                    {
                        **_atom("mul_loop", z3="unknown"),
                        "escalation_reason": "z3_unknown",
                    }
                ],
            }
        )
    )
    out_dir = tmp_path / "generated"
    (tmp_path / "mul_loop_heatmap.json").write_text(
        json.dumps(
            {
                "atom_name": "mul_loop",
                "total_time_ms": 50,
                "total_rlimit": 100,
                "timeout_reason": "z3_unknown",
                "constraints": [
                    {"constraint_id": "cheap", "rlimit_consumed": 5, "time_ms": 1},
                    {"constraint_id": "expensive", "rlimit_consumed": 95, "time_ms": 49},
                ],
            }
        )
    )
    out_cert = tmp_path / "out.lean-cert.json"
    _patch_lake(monkeypatch, rc=0, log="")

    rc = main(
        [
            "--escalation-bundle", str(bundle_path),
            "--out-dir", str(out_dir),
            "--module-prefix", "Generated",
            "--lean-cert-out", str(out_cert),
        ]
    )

    assert rc == 0
    metadata = json.loads(out_cert.read_text())["candidates"][0]["lean_metadata"]
    assert metadata["solver_heatmap"]["total_rlimit"] == 100
    assert "solver_heatmap_available=true" in metadata["diagnostics"]
    assert "top_constraints=expensive(95),cheap(5)" in metadata["diagnostics"]


def test_main_marks_all_failed_when_lake_returns_nonzero_with_unrecognised_log(
    tmp_path: Path, monkeypatch
):
    """rc != 0 + no recognised diagnostic must NOT yield ``lean_verified``.

    Regression for the bug at scripts/bridge.py:228 where a non-zero
    ``lake build`` exit accompanied by an infrastructure-level error
    that does not match ``_ERROR_RE`` (e.g. ``error: cannot resolve
    dependency 'mathlib'`` — no leading ``file:line:col:``) silently
    fell through and marked every atom as ``lean_verified``.
    """
    cert_path = tmp_path / "cert.json"
    cert_path.write_text(
        json.dumps(_cert("std/math.mm", [_atom("inc", z3="unknown")]))
    )
    out_cert = tmp_path / "out.lean-cert.json"
    _patch_lake(monkeypatch, rc=1, log="error: cannot resolve dependency 'mathlib'\n")

    rc = main(
        [
            "--cert", str(cert_path),
            "--out-dir", str(tmp_path / "generated"),
            "--module-prefix", "Generated",
            "--lean-cert-out", str(out_cert),
        ]
    )
    assert rc != 0
    upgraded = json.loads(out_cert.read_text())
    inc = next(a for a in upgraded["atoms"] if a["name"] == "inc")
    assert inc["z3_check_result"] == "unknown"
    assert inc["status"] != "verified"


def test_main_does_not_falsely_mark_when_lake_missing(
    tmp_path: Path, monkeypatch
):
    """rc==127 must mark all lifted atoms as failed, not ``lean_verified``."""
    cert_path = tmp_path / "cert.json"
    cert_path.write_text(
        json.dumps(_cert("std/math.mm", [_atom("inc", z3="unknown")]))
    )
    out_cert = tmp_path / "out.lean-cert.json"
    _patch_lake(monkeypatch, rc=127, log="")

    rc = main(
        [
            "--cert", str(cert_path),
            "--out-dir", str(tmp_path / "generated"),
            "--module-prefix", "Generated",
            "--lean-cert-out", str(out_cert),
        ]
    )
    assert rc == 127
    upgraded = json.loads(out_cert.read_text())
    inc = next(a for a in upgraded["atoms"] if a["name"] == "inc")
    assert inc["z3_check_result"] == "unknown"


def test_main_lake_missing_no_export_returns_zero(
    tmp_path: Path, monkeypatch
):
    cert_path = tmp_path / "cert.json"
    cert_path.write_text(
        json.dumps(_cert("std/math.mm", [_atom("inc", z3="unknown")]))
    )
    out_dir = tmp_path / "generated"
    _patch_lake(monkeypatch, rc=127, log="")

    rc = main(
        [
            "--cert", str(cert_path),
            "--out-dir", str(out_dir),
            "--module-prefix", "Generated",
            "--no-export",
        ]
    )

    assert rc == 0
    assert (out_dir / "Generated" / "Std" / "Math.lean").exists()


def test_main_ci_mode_falls_back_on_lake_failure(
    tmp_path: Path, monkeypatch
):
    cert_path = tmp_path / "cert.json"
    cert_path.write_text(
        json.dumps(_cert("std/math.mm", [_atom("inc", z3="unknown")]))
    )
    summary = tmp_path / "summary.json"
    out_dir = tmp_path / "generated"
    _patch_lake(monkeypatch, rc=1, log="error: cannot resolve dependency 'mathlib'\n")

    rc = main(
        [
            "--cert", str(cert_path),
            "--out-dir", str(out_dir),
            "--module-prefix", "Generated",
            "--lean-cert-out", str(tmp_path / "out.lean-cert.json"),
            "--summary-json", str(summary),
            "--ci-mode",
        ]
    )

    assert rc == 0
    assert (out_dir / "Generated" / "Std" / "Math.lean").exists()
    assert not (tmp_path / "out.lean-cert.json").exists()
    payload = json.loads(summary.read_text())
    assert payload["ci_mode_fallback"] is True
    assert payload["total_unknown"] == 1


def test_main_attributes_failures_per_payload_in_multi_cert_mode(
    tmp_path: Path, monkeypatch
):
    """Same-named atoms across payloads must not cross-contaminate.

    Two scanned certificates each define an atom called ``inc``. Only
    payload A's ``inc_correct`` (in ``Generated/Std/Math.lean``) emits a
    ``sorry`` warning; payload B's ``inc_correct`` (in
    ``Generated/Std/List.lean``) compiles cleanly. The output cert for
    A must keep ``inc`` as ``unknown`` and B must upgrade ``inc`` to
    ``lean_verified``.
    """
    certs_dir = tmp_path / "std" / "certs"
    certs_dir.mkdir(parents=True)
    (certs_dir / "math.json").write_text(
        json.dumps(_cert("std/math.mm", [_atom("inc", z3="unknown")]))
    )
    (certs_dir / "list.json").write_text(
        json.dumps(_cert("std/list.mm", [_atom("inc", z3="unknown")]))
    )
    log = (
        "Generated/Std/Math.lean:1:0: theorem inc_correct\n"
        "Generated/Std/Math.lean:1:0: warning: declaration uses 'sorry'\n"
    )
    _patch_lake(monkeypatch, rc=0, log=log)

    out_dir = tmp_path / "out"
    rc = main(
        [
            "--scan-unknown", str(tmp_path),
            "--out-dir", str(tmp_path / "generated"),
            "--module-prefix", "Generated",
            "--lean-cert-out", str(out_dir),
        ]
    )
    assert rc == 0

    math_out = json.loads((out_dir / "math.json").read_text())
    list_out = json.loads((out_dir / "list.json").read_text())
    assert {a["name"]: a["z3_check_result"] for a in math_out["atoms"]} == {
        "inc": "unknown"
    }
    assert {a["name"]: a["z3_check_result"] for a in list_out["atoms"]} == {
        "inc": "lean_verified"
    }


def test_main_unattributed_failure_applies_to_every_payload(
    tmp_path: Path, monkeypatch
):
    """A failure with no recoverable file path must fail across all payloads.

    Defensive complement to per-file attribution: when the build log
    surfaces a failure we cannot pin to a specific generated file, we
    must apply it to every payload that owns an atom by that name
    rather than silently dropping it (which would falsely upgrade the
    atom to ``lean_verified``).
    """
    certs_dir = tmp_path / "std" / "certs"
    certs_dir.mkdir(parents=True)
    (certs_dir / "math.json").write_text(
        json.dumps(_cert("std/math.mm", [_atom("inc", z3="unknown")]))
    )
    (certs_dir / "list.json").write_text(
        json.dumps(_cert("std/list.mm", [_atom("inc", z3="unknown")]))
    )
    # No ``file:line:col:`` prefix → file path is ``None`` and the
    # failure has to be applied conservatively.
    log = "theorem inc_correct\nwarning: declaration uses 'sorry'\n"
    _patch_lake(monkeypatch, rc=0, log=log)

    out_dir = tmp_path / "out"
    rc = main(
        [
            "--scan-unknown", str(tmp_path),
            "--out-dir", str(tmp_path / "generated"),
            "--module-prefix", "Generated",
            "--lean-cert-out", str(out_dir),
        ]
    )
    assert rc == 0
    for name in ("math.json", "list.json"):
        cert_out = json.loads((out_dir / name).read_text())
        assert all(
            a["z3_check_result"] == "unknown" for a in cert_out["atoms"]
        ), name


def test_sort_ascending_ingest_generates_bridge_theorem(tmp_path: Path):
    """Sort ascending atom (spurious_candidate) is ingested and rendered
    via MumeiLean.Sort.insertion_sort_ascending_bridge."""
    fixture = (
        Path(__file__).resolve().parent
        / "fixtures"
        / "std_list_sort_ascending.proof-cert.json"
    )
    out_dir = tmp_path / "generated"
    rc = main(
        [
            "--cert", str(fixture),
            "--out-dir", str(out_dir),
            "--module-prefix", "Generated",
            "--no-build",
        ]
    )
    assert rc == 0
    lean_file = out_dir / "Generated" / "Std" / "List.lean"
    assert lean_file.exists()
    text = lean_file.read_text()
    assert "theorem verified_insertion_sort_ascending_correct" in text
    assert "MumeiLean.Sort.insertion_sort_ascending_bridge" in text
    assert "List.insertionSort" in text
    assert "known_witness_used=true" not in text
    assert "sorry" not in text
