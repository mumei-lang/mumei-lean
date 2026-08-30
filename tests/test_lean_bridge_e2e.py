"""Live subprocess E2E coverage for ``scripts/bridge.py`` Lean exports."""
from __future__ import annotations

import json
import os
import shutil
import subprocess
import sys
from pathlib import Path

import pytest


REPO_ROOT = Path(__file__).resolve().parents[1]
FIXTURES = Path(__file__).resolve().parent / "fixtures"
BRIDGE = REPO_ROOT / "scripts" / "bridge.py"
GENERATED_ABS = REPO_ROOT / "generated" / "Generated" / "Std" / "Math" / "Abs.lean"
GENERATED_PATTERNS = (
    REPO_ROOT / "generated" / "Generated" / "Std" / "Math" / "Patterns.lean"
)
GENERATED_CRYPTO_PRIMITIVES = (
    REPO_ROOT / "generated" / "Generated" / "Std" / "Crypto" / "Primitives.lean"
)
GENERATED_SETTLEMENT = (
    REPO_ROOT / "generated" / "Generated" / "Std" / "Settlement.lean"
)
GENERATED_FINITE_FIELD = (
    REPO_ROOT / "generated" / "Generated" / "Std" / "Algebra" / "Finite_field.lean"
)
GENERATED_GUARD_TRACE = (
    REPO_ROOT / "generated" / "Generated" / "Std" / "Contract" / "Guard_trace.lean"
)
GENERATED_ACCESS_CONTROL = (
    REPO_ROOT / "generated" / "Generated" / "Std" / "Contract" / "Access_control.lean"
)
GENERATED_CEI = (
    REPO_ROOT / "generated" / "Generated" / "Std" / "Contract" / "Cei.lean"
)
GENERATED_SORT_LIST = (
    REPO_ROOT / "generated" / "Generated" / "Std" / "List.lean"
)
GENERATED_CORE_PREDICATES = (
    REPO_ROOT / "generated" / "Generated" / "Std" / "Core_predicates.lean"
)


def _bridge_env() -> dict[str, str]:
    env = os.environ.copy()
    elan_bin = Path.home() / ".elan" / "bin"
    env["PATH"] = f"{elan_bin}:{env.get('PATH', '')}"
    return env


def _without_lake_env() -> dict[str, str]:
    env = os.environ.copy()
    paths = [
        path
        for path in env.get("PATH", "").split(os.pathsep)
        if path and shutil.which("lake", path=path) is None
    ]
    env["PATH"] = os.pathsep.join(paths) or "/usr/bin:/bin"
    return env


def _run_bridge(
    *args: str,
    env: dict[str, str] | None = None,
) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(BRIDGE), *args],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        env=env or _bridge_env(),
        check=False,
    )


def _assert_bridge_ok(proc: subprocess.CompletedProcess[str]) -> None:
    assert proc.returncode == 0, (
        f"bridge exited {proc.returncode}\n"
        f"stdout:\n{proc.stdout}\n"
        f"stderr:\n{proc.stderr}"
    )


def _cleanup_generated_file(path: Path) -> None:
    path.unlink(missing_ok=True)
    current = path.parent
    generated_root = REPO_ROOT / "generated" / "Generated"
    while current != generated_root and current.exists():
        try:
            current.rmdir()
        except OSError:
            break
        current = current.parent


def _cleanup_generated_abs() -> None:
    _cleanup_generated_file(GENERATED_ABS)


def _cleanup_generated_patterns() -> None:
    _cleanup_generated_file(GENERATED_PATTERNS)


def _cleanup_generated_crypto_primitives() -> None:
    _cleanup_generated_file(GENERATED_CRYPTO_PRIMITIVES)


def _cleanup_generated_settlement() -> None:
    _cleanup_generated_file(GENERATED_SETTLEMENT)


def _cleanup_generated_finite_field() -> None:
    _cleanup_generated_file(GENERATED_FINITE_FIELD)


def _cleanup_generated_core_predicates() -> None:
    _cleanup_generated_file(GENERATED_CORE_PREDICATES)


def _cleanup_generated_guard_trace() -> None:
    _cleanup_generated_file(GENERATED_GUARD_TRACE)


def _cleanup_generated_access_control() -> None:
    _cleanup_generated_file(GENERATED_ACCESS_CONTROL)


def _cleanup_generated_cei() -> None:
    _cleanup_generated_file(GENERATED_CEI)


@pytest.mark.lake_available
def test_lean_fallback_upgrades_unknown_to_lean_verified(lake_available, tmp_path: Path):
    src = (REPO_ROOT / "MumeiLean" / "StdMathAbs.lean").read_text()
    assert "theorem abs_saturating_correct" in src

    out_cert = tmp_path / "abs_saturating.lean-cert.json"
    out_dir = REPO_ROOT / "generated"
    summary = tmp_path / "summary.json"
    _cleanup_generated_abs()
    try:
        proc = _run_bridge(
            "--cert",
            str(FIXTURES / "abs_saturating.proof-cert.json"),
            "--out-dir",
            str(out_dir),
            "--lean-cert-out",
            str(out_cert),
            "--summary-json",
            str(summary),
        )

        _assert_bridge_ok(proc)
        assert GENERATED_ABS.exists()
        generated_src = GENERATED_ABS.read_text()
        assert "namespace Generated.Std.Math.Abs" in generated_src
        assert "theorem abs_saturating_correct" in generated_src
        payload = json.loads(out_cert.read_text())
        assert payload["atoms"][0]["z3_check_result"] == "lean_verified"
        assert payload["atoms"][0]["lean_metadata"]["proof_path"].endswith(
            "generated/Generated/Std/Math/Abs.lean"
        )
        assert payload["atoms"][0]["lean_metadata"]["known_witness_used"] is False
        assert payload["atoms"][0]["lean_metadata"]["lean_module"] == "Generated.Std.Math.Abs"
        assert (
            payload["atoms"][0]["lean_metadata"]["lean_theorem_name"]
            == "Generated.Std.Math.Abs.abs_saturating_correct"
        )
        assert payload["all_verified"] is True
        summary_payload = json.loads(summary.read_text())
        assert summary_payload["lean_fallback"]["proved"] >= 1
        assert summary_payload["details"][0]["lean_fallback"]["proved"] >= 1
        assert summary_payload["metrics"]["lean_successes"] > 0
        assert (
            summary_payload["metrics"]["by_atom"]["abs_saturating"]["status"]
            == "lean_verified"
        )
        assert (
            summary_payload["metrics"]["by_atom"]["abs_saturating"]["known_witness_used"]
            is False
        )
    finally:
        _cleanup_generated_abs()


@pytest.mark.lake_available
def test_guard_trace_fixture_upgrades_unknown_to_lean_verified(
    lake_available, tmp_path: Path
):
    out_cert = tmp_path / "guard_trace.lean-cert.json"
    out_dir = tmp_path / "generated"
    _cleanup_generated_guard_trace()
    try:
        proc = _run_bridge(
            "--cert",
            str(FIXTURES / "guard_trace_demo.proof-cert.json"),
            "--out-dir",
            str(out_dir),
            "--lean-cert-out",
            str(out_cert),
        )

        _assert_bridge_ok(proc)
        assert GENERATED_GUARD_TRACE.exists()
        generated_src = GENERATED_GUARD_TRACE.read_text()
        assert "import MumeiLean.SmartContract" in generated_src
        assert "open MumeiLean.SmartContract" in generated_src
        assert (
            "theorem guarded_reentrancy_trace_correct :\n"
            "    runGuard GuardState.Unlocked [GuardOp.lock, GuardOp.externalCall, "
            "GuardOp.unlock] = some GuardState.Unlocked := by\n"
            "  decide"
        ) in generated_src
        assert (
            "theorem unguarded_reentrancy_trace_correct :\n"
            "    runGuard GuardState.Unlocked [GuardOp.externalCall] = none := by\n"
            "  decide"
        ) in generated_src
        payload = json.loads(out_cert.read_text())
        guarded = next(
            atom for atom in payload["atoms"] if atom["name"] == "guarded_reentrancy_trace"
        )
        unguarded = next(
            atom for atom in payload["atoms"] if atom["name"] == "unguarded_reentrancy_trace"
        )
        assert guarded["z3_check_result"] == "lean_verified"
        assert guarded["status"] == "verified"
        assert unguarded["z3_check_result"] == "lean_verified"
        assert unguarded["status"] == "verified"
        assert payload["all_verified"] is True
    finally:
        _cleanup_generated_guard_trace()


@pytest.mark.lake_available
def test_access_control_fixture_upgrades_unknown_to_lean_verified(
    lake_available, tmp_path: Path
):
    out_cert = tmp_path / "access_control.lean-cert.json"
    out_dir = tmp_path / "generated"
    _cleanup_generated_access_control()
    try:
        proc = _run_bridge(
            "--cert",
            str(FIXTURES / "access_control_demo.proof-cert.json"),
            "--out-dir",
            str(out_dir),
            "--lean-cert-out",
            str(out_cert),
        )

        _assert_bridge_ok(proc)
        assert GENERATED_ACCESS_CONTROL.exists()
        generated_src = GENERATED_ACCESS_CONTROL.read_text()
        assert "import MumeiLean.SmartContract" in generated_src
        assert "open MumeiLean.SmartContract" in generated_src
        assert (
            "theorem guarded_access_control_trace_correct :\n"
            "    runAccess AccessState.Unchecked [AccessOp.authCheck, "
            "AccessOp.stateWrite] = some AccessState.Checked := by\n"
            "  decide"
        ) in generated_src
        assert (
            "theorem unguarded_access_control_trace_correct :\n"
            "    runAccess AccessState.Unchecked [AccessOp.stateWrite] = none := by\n"
            "  decide"
        ) in generated_src
        payload = json.loads(out_cert.read_text())
        guarded = next(
            atom
            for atom in payload["atoms"]
            if atom["name"] == "guarded_access_control_trace"
        )
        unguarded = next(
            atom
            for atom in payload["atoms"]
            if atom["name"] == "unguarded_access_control_trace"
        )
        assert guarded["z3_check_result"] == "lean_verified"
        assert guarded["status"] == "verified"
        assert unguarded["z3_check_result"] == "lean_verified"
        assert unguarded["status"] == "verified"
        assert payload["all_verified"] is True
    finally:
        _cleanup_generated_access_control()


@pytest.mark.lake_available
def test_cei_fixture_upgrades_unknown_to_lean_verified(
    lake_available, tmp_path: Path
):
    out_cert = tmp_path / "cei.lean-cert.json"
    out_dir = tmp_path / "generated"
    _cleanup_generated_cei()
    try:
        proc = _run_bridge(
            "--cert",
            str(FIXTURES / "cei_demo.proof-cert.json"),
            "--out-dir",
            str(out_dir),
            "--lean-cert-out",
            str(out_cert),
        )

        _assert_bridge_ok(proc)
        assert GENERATED_CEI.exists()
        generated_src = GENERATED_CEI.read_text()
        assert "import MumeiLean.SmartContract" in generated_src
        assert "open MumeiLean.SmartContract" in generated_src
        assert (
            "theorem ordered_cei_trace_correct :\n"
            "    runCei CeiState.Effects [CeiOp.effect, CeiOp.interaction] "
            "= some CeiState.Interacted := by\n"
            "  decide"
        ) in generated_src
        assert (
            "theorem violating_cei_trace_correct :\n"
            "    runCei CeiState.Effects [CeiOp.interaction, CeiOp.effect] = none := by\n"
            "  decide"
        ) in generated_src
        payload = json.loads(out_cert.read_text())
        ordered = next(
            atom
            for atom in payload["atoms"]
            if atom["name"] == "ordered_cei_trace"
        )
        violating = next(
            atom
            for atom in payload["atoms"]
            if atom["name"] == "violating_cei_trace"
        )
        assert ordered["z3_check_result"] == "lean_verified"
        assert ordered["status"] == "verified"
        assert violating["z3_check_result"] == "lean_verified"
        assert violating["status"] == "verified"
        assert payload["all_verified"] is True
    finally:
        _cleanup_generated_cei()


@pytest.mark.lake_available
def test_bounded_mul_body_semantics_upgrades_unknown_to_lean_verified(
    lake_available, tmp_path: Path
):
    out_cert = tmp_path / "std_math_patterns.lean-cert.json"
    out_dir = REPO_ROOT / "generated"
    _cleanup_generated_patterns()
    try:
        proc = _run_bridge(
            "--cert",
            str(FIXTURES / "std_math_patterns_bounded_mul.proof-cert.json"),
            "--out-dir",
            str(out_dir),
            "--lean-cert-out",
            str(out_cert),
        )

        _assert_bridge_ok(proc)
        assert GENERATED_PATTERNS.exists()
        payload = json.loads(out_cert.read_text())
        atom = next(
            a for a in payload["atoms"]
            if a["name"] == "bounded_mul_with_overflow_check"
        )
        assert atom["z3_check_result"] == "lean_verified"
        assert atom["status"] == "verified"
        assert atom["lean_metadata"]["known_witness_used"] is False
        assert atom["lean_metadata"]["lean_theorem_name"] == (
            "Generated.Std.Math.Patterns."
            "bounded_mul_with_overflow_check_correct"
        )
    finally:
        _cleanup_generated_patterns()


@pytest.mark.lake_available
def test_crypto_constant_time_eq_upgrades_unknown_to_lean_verified(
    lake_available, tmp_path: Path
):
    out_cert = tmp_path / "std_crypto_primitives.lean-cert.json"
    out_dir = REPO_ROOT / "generated"
    _cleanup_generated_crypto_primitives()
    try:
        proc = _run_bridge(
            "--cert",
            str(FIXTURES / "std_crypto_primitives_constant_time_eq.proof-cert.json"),
            "--out-dir",
            str(out_dir),
            "--lean-cert-out",
            str(out_cert),
        )

        _assert_bridge_ok(proc)
        assert GENERATED_CRYPTO_PRIMITIVES.exists()
        payload = json.loads(out_cert.read_text())
        atom = next(a for a in payload["atoms"] if a["name"] == "constant_time_eq_flag")
        assert atom["z3_check_result"] == "lean_verified"
        assert atom["status"] == "verified"
        assert atom["lean_metadata"]["known_witness_used"] is False
        assert atom["lean_metadata"]["lean_theorem_name"] == (
            "Generated.Std.Crypto.Primitives.constant_time_eq_flag_correct"
        )
    finally:
        _cleanup_generated_crypto_primitives()


@pytest.mark.lake_available
def test_finite_field_zero_eq_upgrades_unknown_to_lean_verified(
    lake_available, tmp_path: Path
):
    out_cert = tmp_path / "std_algebra_finite_field.lean-cert.json"
    out_dir = REPO_ROOT / "generated"
    _cleanup_generated_finite_field()
    try:
        proc = _run_bridge(
            "--cert",
            str(
                FIXTURES
                / "std_algebra_finite_field_ff_zero_eq_zero.proof-cert.json"
            ),
            "--out-dir",
            str(out_dir),
            "--lean-cert-out",
            str(out_cert),
        )

        _assert_bridge_ok(proc)
        assert GENERATED_FINITE_FIELD.exists()
        payload = json.loads(out_cert.read_text())
        atom = next(
            a for a in payload["atoms"] if a["name"] == "ff_zero_eq_zero"
        )
        assert atom["z3_check_result"] == "lean_verified"
        assert atom["status"] == "verified"
        assert atom["lean_metadata"]["known_witness_used"] is False
        assert atom["lean_metadata"]["lean_theorem_name"] == (
            "Generated.Std.Algebra.Finite_field.ff_zero_eq_zero_correct"
        )
    finally:
        _cleanup_generated_finite_field()


@pytest.mark.lake_available
def test_finite_field_commutativity_upgrades_unknown_to_lean_verified(
    lake_available, tmp_path: Path
):
    out_cert = tmp_path / "std_algebra_finite_field_comm.lean-cert.json"
    out_dir = REPO_ROOT / "generated"
    _cleanup_generated_finite_field()
    try:
        proc = _run_bridge(
            "--cert",
            str(
                FIXTURES
                / "std_algebra_finite_field_ff_mul_commutative.proof-cert.json"
            ),
            "--out-dir",
            str(out_dir),
            "--lean-cert-out",
            str(out_cert),
        )

        _assert_bridge_ok(proc)
        assert GENERATED_FINITE_FIELD.exists()
        generated = GENERATED_FINITE_FIELD.read_text()
        assert "MumeiLean.Algebra.ff_mul_comm_eq" in generated
        payload = json.loads(out_cert.read_text())
        atom = next(
            a for a in payload["atoms"] if a["name"] == "ff_mul_commutative"
        )
        assert atom["z3_check_result"] == "lean_verified"
        assert atom["status"] == "verified"
        assert atom["lean_metadata"]["known_witness_used"] is False
        assert atom["lean_metadata"]["lean_theorem_name"] == (
            "Generated.Std.Algebra.Finite_field.ff_mul_commutative_correct"
        )
        assert atom["z3_result_class"] == "unknown"
        assert atom["escalation_reason"] == "z3_unknown"
        assert atom["logic_fragment_tags"] == ["finite_field", "nonlinear_arithmetic"]
    finally:
        _cleanup_generated_finite_field()


@pytest.mark.lake_available
def test_finite_field_associativity_upgrades_unknown_to_lean_verified(
    lake_available, tmp_path: Path
):
    out_cert = tmp_path / "std_algebra_finite_field_assoc.lean-cert.json"
    out_dir = REPO_ROOT / "generated"
    _cleanup_generated_finite_field()
    try:
        proc = _run_bridge(
            "--cert",
            str(
                FIXTURES
                / "std_algebra_finite_field_ff_mul_associative.proof-cert.json"
            ),
            "--out-dir",
            str(out_dir),
            "--lean-cert-out",
            str(out_cert),
        )

        _assert_bridge_ok(proc)
        assert GENERATED_FINITE_FIELD.exists()
        generated = GENERATED_FINITE_FIELD.read_text()
        assert "MumeiLean.Algebra.ff_mul_assoc_mod" in generated
        payload = json.loads(out_cert.read_text())
        atom = next(
            a for a in payload["atoms"] if a["name"] == "ff_mul_associative"
        )
        assert atom["z3_check_result"] == "lean_verified"
        assert atom["status"] == "verified"
        assert atom["lean_metadata"]["known_witness_used"] is False
        assert atom["lean_metadata"]["lean_theorem_name"] == (
            "Generated.Std.Algebra.Finite_field.ff_mul_associative_correct"
        )
        assert atom["z3_result_class"] == "unknown"
        assert atom["escalation_reason"] == "z3_unknown"
        assert atom["logic_fragment_tags"] == ["finite_field", "nonlinear_arithmetic"]
    finally:
        _cleanup_generated_finite_field()


@pytest.mark.lake_available
def test_finite_field_distributivity_discharged_by_tactic_search(
    lake_available, tmp_path: Path
):
    """Twelfth live path: `lean_verified` via automatic tactic search (spec §12).

    No bridge lemma template covers modular distributivity, so the generic
    fallback proof fails to build and the `build_failure` search stage adopts
    `mumei_ff_mod`.
    """
    out_cert = tmp_path / "std_algebra_finite_field_distrib.lean-cert.json"
    out_dir = REPO_ROOT / "generated"
    _cleanup_generated_finite_field()
    try:
        proc = _run_bridge(
            "--cert",
            str(
                FIXTURES
                / "std_algebra_finite_field_ff_mul_add_distributive.proof-cert.json"
            ),
            "--out-dir",
            str(out_dir),
            "--lean-cert-out",
            str(out_cert),
        )

        _assert_bridge_ok(proc)
        assert GENERATED_FINITE_FIELD.exists()
        assert "mumei_ff_mod" in GENERATED_FINITE_FIELD.read_text()
        payload = json.loads(out_cert.read_text())
        atom = next(
            a for a in payload["atoms"] if a["name"] == "ff_mul_add_distributive"
        )
        assert atom["z3_check_result"] == "lean_verified"
        assert atom["status"] == "verified"
        metadata = atom["lean_metadata"]
        assert metadata["status"] == "lean_verified"
        assert metadata["known_witness_used"] is False
        assert metadata["lean_theorem_name"] == (
            "Generated.Std.Algebra.Finite_field.ff_mul_add_distributive_correct"
        )
        assert metadata["manual_lemma_reason"] is None
        search = metadata["tactic_search"]
        assert search["stage"] == "build_failure"
        assert search["adopted_tactic"] == "mumei_ff_mod"
        assert search["exhausted"] is False
        assert search["timed_out"] is False
        assert search["search_time_s"] > 0
        # Search time is folded into the single `lean_solver_time_s` channel.
        assert metadata["lean_solver_time_s"] > search["search_time_s"]
    finally:
        _cleanup_generated_finite_field()


@pytest.mark.lake_available
def test_predicate_guard_collapse_discharged_by_widened_ladder(
    lake_available, tmp_path: Path
):
    """Thirteenth live path: `lean_verified` via the widened ladder (spec §12.2).

    The obligation is a classically-valid, Peirce-shaped guard collapse over
    predicate-parametric contracts: no bridge lemma template covers it, the
    generic fallback proof fails to build, and none of the twelve arithmetic /
    modular / field candidates close it — `tauto` does.
    """
    out_cert = tmp_path / "std_core_predicates_guard_collapse.lean-cert.json"
    out_dir = REPO_ROOT / "generated"
    _cleanup_generated_core_predicates()
    try:
        proc = _run_bridge(
            "--cert",
            str(FIXTURES / "std_core_predicates_guard_collapse.proof-cert.json"),
            "--out-dir",
            str(out_dir),
            "--lean-cert-out",
            str(out_cert),
        )

        _assert_bridge_ok(proc)
        assert GENERATED_CORE_PREDICATES.exists()
        assert "tauto" in GENERATED_CORE_PREDICATES.read_text()
        payload = json.loads(out_cert.read_text())
        atom = next(
            a for a in payload["atoms"] if a["name"] == "predicate_guard_collapse"
        )
        assert atom["z3_check_result"] == "lean_verified"
        assert atom["status"] == "verified"
        metadata = atom["lean_metadata"]
        assert metadata["status"] == "lean_verified"
        assert metadata["known_witness_used"] is False
        assert metadata["lean_theorem_name"] == (
            "Generated.Std.Core_predicates.predicate_guard_collapse_correct"
        )
        assert metadata["manual_lemma_reason"] is None
        search = metadata["tactic_search"]
        assert search["stage"] == "build_failure"
        assert search["adopted_tactic"] == "tauto"
        assert search["exhausted"] is False
        assert search["timed_out"] is False
        assert search["search_time_s"] > 0
        # The pinned history (spec §12.5) records `tauto` for this class, so the
        # ladder is probed in learned order and the adopted tactic is unchanged.
        assert search["history_ranked"] is True
        assert search["candidates_tried"] == ["tauto"]
        # Search time is folded into the single `lean_solver_time_s` channel.
        assert metadata["lean_solver_time_s"] > search["search_time_s"]
    finally:
        _cleanup_generated_core_predicates()


@pytest.mark.lake_available
def test_finite_field_pow_expansion_discharged_by_tactic_search(
    lake_available, tmp_path: Path
):
    """Fourteenth live path: `lean_verified` via the `mumei_ff_pow` stage (§12.2).

    The obligation expands a modular square into repeated modular
    multiplication. No bridge lemma template covers it, and `mumei_ff_mod` does
    not reach under the exponent (`Int.toNat` literal, reduction below `^`), so
    the ladder tail entry `mumei_ff_pow` is what closes it.
    """
    out_cert = tmp_path / "std_algebra_finite_field_pow.lean-cert.json"
    out_dir = REPO_ROOT / "generated"
    _cleanup_generated_finite_field()
    try:
        proc = _run_bridge(
            "--cert",
            str(
                FIXTURES
                / "std_algebra_finite_field_ff_pow_square_expands.proof-cert.json"
            ),
            "--out-dir",
            str(out_dir),
            "--lean-cert-out",
            str(out_cert),
        )

        _assert_bridge_ok(proc)
        assert GENERATED_FINITE_FIELD.exists()
        assert "mumei_ff_pow" in GENERATED_FINITE_FIELD.read_text()
        payload = json.loads(out_cert.read_text())
        atom = next(
            a for a in payload["atoms"] if a["name"] == "ff_pow_square_expands"
        )
        assert atom["z3_check_result"] == "lean_verified"
        assert atom["status"] == "verified"
        metadata = atom["lean_metadata"]
        assert metadata["status"] == "lean_verified"
        assert metadata["known_witness_used"] is False
        assert metadata["lean_theorem_name"] == (
            "Generated.Std.Algebra.Finite_field.ff_pow_square_expands_correct"
        )
        assert metadata["manual_lemma_reason"] is None
        search = metadata["tactic_search"]
        assert search["stage"] == "build_failure"
        assert search["adopted_tactic"] == "mumei_ff_pow"
        assert search["exhausted"] is False
        assert search["timed_out"] is False
        assert search["search_time_s"] > 0
        # Search time is folded into the single `lean_solver_time_s` channel.
        assert metadata["lean_solver_time_s"] > search["search_time_s"]
    finally:
        _cleanup_generated_finite_field()


@pytest.mark.lake_available
def test_widened_ladder_goal_shapes_compile(lake_available):
    """The new ladder entries close the goal shapes the spec claims (§12.2)."""
    proc = subprocess.run(
        ["lake", "env", "lean", str(FIXTURES / "tactic_ladder_driver.lean")],
        cwd=str(REPO_ROOT),
        env=_bridge_env(),
        capture_output=True,
        text=True,
        timeout=900,
    )
    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "error" not in proc.stdout


@pytest.mark.lake_available
def test_tactic_search_can_be_disabled(lake_available, tmp_path: Path):
    """`--no-tactic-search` keeps the pre-§12 conservative behaviour."""
    out_cert = tmp_path / "std_algebra_finite_field_distrib_off.lean-cert.json"
    out_dir = REPO_ROOT / "generated"
    _cleanup_generated_finite_field()
    try:
        proc = _run_bridge(
            "--cert",
            str(
                FIXTURES
                / "std_algebra_finite_field_ff_mul_add_distributive.proof-cert.json"
            ),
            "--out-dir",
            str(out_dir),
            "--lean-cert-out",
            str(out_cert),
            "--no-tactic-search",
        )

        payload = json.loads(out_cert.read_text())
        atom = next(
            a for a in payload["atoms"] if a["name"] == "ff_mul_add_distributive"
        )
        assert atom["z3_check_result"] == "unknown"
        assert atom["status"] != "verified"
        metadata = atom["lean_metadata"]
        assert metadata["status"] != "lean_verified"
        assert "tactic_search" not in metadata
        assert proc.returncode != 0
    finally:
        _cleanup_generated_finite_field()


def test_bridge_no_build_dry_run(tmp_path: Path):
    out_cert = tmp_path / "abs_saturating.no-build.lean-cert.json"
    proc = _run_bridge(
        "--cert",
        str(FIXTURES / "abs_saturating.proof-cert.json"),
        "--out-dir",
        str(tmp_path / "generated"),
        "--lean-cert-out",
        str(out_cert),
        "--no-build",
        env=_without_lake_env(),
    )

    _assert_bridge_ok(proc)
    payload = json.loads(out_cert.read_text())
    atom = payload["atoms"][0]
    metadata = atom["lean_result_metadata"]
    assert atom["z3_check_result"] != "lean_verified"
    assert metadata["status"] == "manual_lemma_required"
    assert metadata["z3_result_class"] == "unknown"
    assert metadata["translator_ir"]["sort"] == "contract_obligation"
    assert metadata["logic_fragment_tags"] == []
    assert metadata["manual_lemma_reason"] is None
    assert metadata["translator_version"] == "mumei-lean-translator-ir-v2"
    assert (
        metadata["bridge_lemma_hash"]
        == "ee8cd3ba96c3318b3f07445f4755619744d4e1f9a662af94f3cbce6d41ed4347"
    )
    assert payload["all_verified"] is False


def test_bridge_scan_unknown(tmp_path: Path):
    scan_root = tmp_path / "fixtures"
    certs_dir = scan_root / "std" / "certs"
    certs_dir.mkdir(parents=True)
    (certs_dir / "math.json").write_text(
        (FIXTURES / "abs_saturating.proof-cert.json").read_text()
    )
    summary = tmp_path / "summary.json"

    proc = _run_bridge(
        "--scan-unknown",
        str(scan_root),
        "--out-dir",
        str(tmp_path / "generated"),
        "--summary-json",
        str(summary),
        "--no-build",
        "--no-export",
        env=_without_lake_env(),
    )

    _assert_bridge_ok(proc)
    payload = json.loads(summary.read_text())
    assert payload["total_unknown"] >= 1


def _cleanup_generated_sort_list() -> None:
    _cleanup_generated_file(GENERATED_SORT_LIST)


@pytest.mark.lake_available
def test_sort_ascending_upgrades_spurious_to_lean_verified(
    lake_available, tmp_path: Path
):
    """5th live generated theorem path: insertion sort ascending preservation.

    The sort atom produces ``z3_check_result == "spurious_candidate"``
    (Z3 Array + forall quantifier), which the bridge now accepts as an
    escalation candidate. The bridge delegates to
    ``MumeiLean.Sort.insertion_sort_ascending_bridge`` and ``lake build``
    discharges the proof, upgrading the atom to ``lean_verified``.
    """
    out_cert = tmp_path / "std_list_sort_ascending.lean-cert.json"
    out_dir = REPO_ROOT / "generated"
    _cleanup_generated_sort_list()
    try:
        proc = _run_bridge(
            "--cert",
            str(FIXTURES / "std_list_sort_ascending.proof-cert.json"),
            "--out-dir",
            str(out_dir),
            "--lean-cert-out",
            str(out_cert),
        )

        _assert_bridge_ok(proc)
        assert GENERATED_SORT_LIST.exists()
        payload = json.loads(out_cert.read_text())
        atom = next(
            a for a in payload["atoms"]
            if a["name"] == "verified_insertion_sort_ascending"
        )
        assert atom["z3_check_result"] == "lean_verified"
        assert atom["status"] == "verified"
        assert atom["lean_metadata"]["known_witness_used"] is False
        assert atom["lean_metadata"]["lean_theorem_name"] == (
            "Generated.Std.List."
            "verified_insertion_sort_ascending_correct"
        )
    finally:
        _cleanup_generated_sort_list()


@pytest.mark.lake_available
def test_poly_bound_monotone_upgrades_unknown_to_lean_verified(
    lake_available, tmp_path: Path
):
    """6th live generated theorem path: single non-conjunction nonlinear
    predicate. Z3 returns ``unknown`` on the nonlinear obligation; the bridge
    lowers the body through ``mumei_arith_deep`` (nlinarith/positivity) and
    ``lake build`` upgrades the atom to ``lean_verified``."""
    out_cert = tmp_path / "std_math_patterns_poly.lean-cert.json"
    out_dir = REPO_ROOT / "generated"
    _cleanup_generated_patterns()
    try:
        proc = _run_bridge(
            "--cert",
            str(FIXTURES / "std_math_patterns_poly_bound.proof-cert.json"),
            "--out-dir",
            str(out_dir),
            "--lean-cert-out",
            str(out_cert),
        )

        _assert_bridge_ok(proc)
        assert GENERATED_PATTERNS.exists()
        payload = json.loads(out_cert.read_text())
        atom = next(
            a for a in payload["atoms"] if a["name"] == "poly_bound_monotone"
        )
        assert atom["z3_check_result"] == "lean_verified"
        assert atom["status"] == "verified"
        assert atom["lean_metadata"]["known_witness_used"] is False
        assert atom["lean_metadata"]["lean_theorem_name"] == (
            "Generated.Std.Math.Patterns.poly_bound_monotone_correct"
        )
    finally:
        _cleanup_generated_patterns()


@pytest.mark.lake_available
def test_exists_pivot_partition_upgrades_spurious_to_lean_verified(
    lake_available, tmp_path: Path
):
    """7th live generated theorem path: forall/exists quantifier alternation.

    Z3 reports ``spurious_candidate`` because the ∀∃ alternation is trigger
    sensitive. The bridge delegates to
    ``MumeiLean.Quantifiers.forall_exists_swap_of_finite`` with an explicit
    identity choice witness and ``lake build`` upgrades to ``lean_verified``."""
    out_cert = tmp_path / "std_list_exists_pivot.lean-cert.json"
    out_dir = REPO_ROOT / "generated"
    _cleanup_generated_sort_list()
    try:
        proc = _run_bridge(
            "--cert",
            str(FIXTURES / "std_list_exists_pivot_partition.proof-cert.json"),
            "--out-dir",
            str(out_dir),
            "--lean-cert-out",
            str(out_cert),
        )

        _assert_bridge_ok(proc)
        assert GENERATED_SORT_LIST.exists()
        payload = json.loads(out_cert.read_text())
        atom = next(
            a for a in payload["atoms"] if a["name"] == "exists_pivot_partition"
        )
        assert atom["z3_check_result"] == "lean_verified"
        assert atom["status"] == "verified"
        assert atom["lean_metadata"]["known_witness_used"] is False
        assert atom["lean_metadata"]["lean_theorem_name"] == (
            "Generated.Std.List.exists_pivot_partition_correct"
        )
    finally:
        _cleanup_generated_sort_list()


@pytest.mark.lake_available
def test_sum_nonneg_inductive_upgrades_unknown_to_lean_verified(
    lake_available, tmp_path: Path
):
    """8th live generated theorem path: natural-number induction.

    Z3 leaves the recursive nonnegativity obligation ``unknown``. The bridge
    delegates to ``MumeiLean.AdvancedPatterns.int_nonnegative_induction_pattern``
    and ``lake build`` upgrades the atom to ``lean_verified``."""
    out_cert = tmp_path / "std_math_patterns_sum.lean-cert.json"
    out_dir = REPO_ROOT / "generated"
    _cleanup_generated_patterns()
    try:
        proc = _run_bridge(
            "--cert",
            str(FIXTURES / "std_math_patterns_sum_nonneg.proof-cert.json"),
            "--out-dir",
            str(out_dir),
            "--lean-cert-out",
            str(out_cert),
        )

        _assert_bridge_ok(proc)
        assert GENERATED_PATTERNS.exists()
        payload = json.loads(out_cert.read_text())
        atom = next(
            a for a in payload["atoms"] if a["name"] == "sum_nonneg_inductive"
        )
        assert atom["z3_check_result"] == "lean_verified"
        assert atom["status"] == "verified"
        assert atom["lean_metadata"]["known_witness_used"] is False
        assert atom["lean_metadata"]["lean_theorem_name"] == (
            "Generated.Std.Math.Patterns.sum_nonneg_inductive_correct"
        )
    finally:
        _cleanup_generated_patterns()


@pytest.mark.lake_available
def test_rtgs_transfer_conservation_upgrades_unknown_to_lean_verified(
    lake_available, tmp_path: Path
):
    """9th live generated theorem path: RTGS balance conservation.

    The obligation classifies as ``rtgs_obligation`` and is discharged by
    ``mumei_arith`` against the conservation surface in
    ``MumeiLean.Algebra`` / ``MumeiLean.AdvancedPatterns``. The exported atom
    must also carry the measured escalation cost in
    ``lean_result_metadata.lean_solver_time_s``, which mumei's benchmark
    runner reads as ``details.lean_solver_time_s``.
    """
    out_cert = tmp_path / "std_settlement_rtgs.lean-cert.json"
    out_dir = REPO_ROOT / "generated"
    _cleanup_generated_settlement()
    try:
        proc = _run_bridge(
            "--cert",
            str(FIXTURES / "std_settlement_rtgs_conservation.proof-cert.json"),
            "--out-dir",
            str(out_dir),
            "--lean-cert-out",
            str(out_cert),
        )

        _assert_bridge_ok(proc)
        assert GENERATED_SETTLEMENT.exists()
        payload = json.loads(out_cert.read_text())
        atom = next(
            a
            for a in payload["atoms"]
            if a["name"] == "rtgs_transfer_conservation"
        )
        assert atom["z3_check_result"] == "lean_verified"
        assert atom["status"] == "verified"
        assert atom["lean_metadata"]["known_witness_used"] is False
        assert atom["lean_metadata"]["lean_theorem_name"] == (
            "Generated.Std.Settlement.rtgs_transfer_conservation_correct"
        )
        assert atom["lean_result_metadata"]["lean_solver_time_s"] > 0
    finally:
        _cleanup_generated_settlement()


@pytest.mark.lake_available
def test_bridge_escalation_bundle(lake_available, tmp_path: Path):
    out_cert = tmp_path / "abs_saturating.escalation.lean-cert.json"
    _cleanup_generated_abs()
    try:
        proc = _run_bridge(
            "--escalation-bundle",
            str(FIXTURES / "abs_saturating.escalation-bundle.json"),
            "--lean-cert-out",
            str(out_cert),
        )

        _assert_bridge_ok(proc)
        payload = json.loads(out_cert.read_text())
        candidate = payload["candidates"][0]
        assert candidate["name"] == "abs_saturating"
        assert candidate["z3_check_result"] == "lean_verified"
        assert candidate["lean_metadata"]["known_witness_used"] is False
    finally:
        _cleanup_generated_abs()
