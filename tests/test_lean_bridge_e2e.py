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
        == "5716cfdd945d68b4a0d75d75c5ade1934cbd76e0dfe16734a8f3dd723cfdd8e9"
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


GENERATED_STACK = REPO_ROOT / "generated" / "Generated" / "Std" / "Stack.lean"


@pytest.mark.lake_available
def test_builtin_name_binder_and_block_body_upgrade_unknown_to_lean_verified(
    lake_available, tmp_path: Path
):
    """Spec §4.1/§4.2: bare `max` binds as Int and `{ top + 1 }` unwraps.

    Both atoms in the fixture were partial (helper-name clash / brace
    passthrough) before the lowering; they must now build without a
    known witness and without touching the bridge lemma catalog.
    """
    out_cert = tmp_path / "stack.lean-cert.json"
    out_dir = tmp_path / "generated"
    _cleanup_generated_file(GENERATED_STACK)
    try:
        proc = _run_bridge(
            "--cert",
            str(FIXTURES / "std_stack_builtin_name_binder.proof-cert.json"),
            "--out-dir",
            str(out_dir),
            "--lean-cert-out",
            str(out_cert),
        )
        _assert_bridge_ok(proc)
        assert "0 partial translation" in proc.stdout
        generated_src = GENERATED_STACK.read_text()
        assert "def stackPushResult (top max : Int) : Int :=\n  top + 1\n" in generated_src
        assert (
            "theorem stack_push_correct (top max : Int) (result : Int) "
            "(h_body : result = stackPushResult top max) :\n"
            "    (top ≥ 0 ∧ max > 0 ∧ top < max) → (result ≥ 0 ∧ result ≤ max)"
        ) in generated_src
        assert "if top = max then 1 else 0" in generated_src
        assert "{ top" not in generated_src
        payload = json.loads(out_cert.read_text())
        for name in ("stack_push", "stack_is_full"):
            atom = next(a for a in payload["atoms"] if a["name"] == name)
            assert atom["z3_check_result"] == "lean_verified"
            assert atom["status"] == "verified"
            meta = atom["lean_metadata"]
            assert meta["known_witness_used"] is False
            assert meta["translator_version"] == "mumei-lean-translator-ir-v2"
            assert meta["bridge_lemma_hash"] == (
                "5716cfdd945d68b4a0d75d75c5ade1934cbd76e0dfe16734a8f3dd723cfdd8e9"
            )
        push = next(a for a in payload["atoms"] if a["name"] == "stack_push")
        rules = push["lean_metadata"]["translator_ir"]["lowering_rules"]
        assert "builtin_name_binder_lowering" in rules
        assert payload["all_verified"] is True
    finally:
        _cleanup_generated_file(GENERATED_STACK)


GENERATED_DEFI = REPO_ROOT / "generated" / "Generated" / "Defi" / "Invariants.lean"


@pytest.mark.lake_available
def test_perform_sequence_body_semantics_upgrade_unknown_to_lean_verified(
    lake_available, tmp_path: Path
):
    """Spec §4.3: `{ perform …; e }` body blocks lower to their value tail.

    Both fixture atoms were partial (`unknown_token` on `;`) before the
    lowering; they must now build via body semantics without a known
    witness and without touching the bridge lemma catalog.
    """
    out_cert = tmp_path / "defi_invariants.lean-cert.json"
    out_dir = tmp_path / "generated"
    _cleanup_generated_file(GENERATED_DEFI)
    try:
        proc = _run_bridge(
            "--cert",
            str(FIXTURES / "defi_invariants_perform_sequence.proof-cert.json"),
            "--out-dir",
            str(out_dir),
            "--lean-cert-out",
            str(out_cert),
        )
        _assert_bridge_ok(proc)
        assert "0 partial translation" in proc.stdout
        generated_src = GENERATED_DEFI.read_text()
        assert (
            "def ceiCompliantWithdrawResult (balance amount : Int) : Int :=\n"
            "  balance - amount\n"
        ) in generated_src
        assert "perform" not in generated_src
        payload = json.loads(out_cert.read_text())
        for name in ("cei_compliant_withdraw", "guarded_state_update"):
            atom = next(a for a in payload["atoms"] if a["name"] == name)
            assert atom["z3_check_result"] == "lean_verified"
            assert atom["status"] == "verified"
            meta = atom["lean_metadata"]
            assert meta["known_witness_used"] is False
            assert meta["translator_version"] == "mumei-lean-translator-ir-v2"
            assert meta["bridge_lemma_hash"] == (
                "5716cfdd945d68b4a0d75d75c5ade1934cbd76e0dfe16734a8f3dd723cfdd8e9"
            )
            rules = meta["translator_ir"]["lowering_rules"]
            assert "perform_statement_lowering" in rules
        assert payload["all_verified"] is True
    finally:
        _cleanup_generated_file(GENERATED_DEFI)


GENERATED_LINEAR_OWNERSHIP = (
    REPO_ROOT / "generated" / "Generated" / "Concurrency" / "Linear_ownership.lean"
)


@pytest.mark.lake_available
def test_let_sequence_body_semantics_upgrade_unknown_to_lean_verified(
    lake_available, tmp_path: Path
):
    """Spec §4.4: `{ let x = e; …; tail }` blocks lower to the substituted tail.

    Both fixture atoms were partial (`unknown_token` on `;`) before the
    lowering; they must now build via body semantics without a known
    witness and without touching the bridge lemma catalog.
    """
    out_cert = tmp_path / "linear_ownership.lean-cert.json"
    out_dir = tmp_path / "generated"
    _cleanup_generated_file(GENERATED_LINEAR_OWNERSHIP)
    try:
        proc = _run_bridge(
            "--cert",
            str(
                FIXTURES / "concurrency_linear_ownership_let_sequence.proof-cert.json"
            ),
            "--out-dir",
            str(out_dir),
            "--lean-cert-out",
            str(out_cert),
        )
        _assert_bridge_ok(proc)
        assert "0 partial translation" in proc.stdout
        generated_src = GENERATED_LINEAR_OWNERSHIP.read_text()
        assert "def moveOnceResult (buf : Int) : Int :=" in generated_src
        assert "def readBeforeMoveResult (buf : Int) : Int :=" in generated_src
        assert "let owned" not in generated_src
        payload = json.loads(out_cert.read_text())
        for name in ("move_once", "read_before_move"):
            atom = next(a for a in payload["atoms"] if a["name"] == name)
            assert atom["z3_check_result"] == "lean_verified"
            assert atom["status"] == "verified"
            meta = atom["lean_metadata"]
            assert meta["known_witness_used"] is False
            assert meta["translator_version"] == "mumei-lean-translator-ir-v2"
            assert meta["bridge_lemma_hash"] == (
                "5716cfdd945d68b4a0d75d75c5ade1934cbd76e0dfe16734a8f3dd723cfdd8e9"
            )
            rules = meta["translator_ir"]["lowering_rules"]
            assert "let_statement_lowering" in rules
        assert payload["all_verified"] is True
    finally:
        _cleanup_generated_file(GENERATED_LINEAR_OWNERSHIP)


GENERATED_SATURATING = (
    REPO_ROOT / "generated" / "Generated" / "Arithmetic" / "Saturating.lean"
)


@pytest.mark.lake_available
def test_nested_if_body_semantics_upgrade_unknown_to_lean_verified(
    lake_available, tmp_path: Path
):
    """Spec §4.5: `if c { a } else { b }` branches may nest conditionals.

    The fixture atom was partial (`unsupported_syntax`) before the nested
    lowering; it must now build via body semantics without a known
    witness and without touching the bridge lemma catalog.
    """
    out_cert = tmp_path / "saturating.lean-cert.json"
    out_dir = tmp_path / "generated"
    _cleanup_generated_file(GENERATED_SATURATING)
    try:
        proc = _run_bridge(
            "--cert",
            str(FIXTURES / "arithmetic_saturating_nested_if.proof-cert.json"),
            "--out-dir",
            str(out_dir),
            "--lean-cert-out",
            str(out_cert),
        )
        _assert_bridge_ok(proc)
        assert "0 partial translation" in proc.stdout
        generated_src = GENERATED_SATURATING.read_text()
        assert (
            "if x < lo then lo else if x > hi then hi else x" in generated_src
        )
        payload = json.loads(out_cert.read_text())
        atom = next(a for a in payload["atoms"] if a["name"] == "clamp_to_range")
        assert atom["z3_check_result"] == "lean_verified"
        assert atom["status"] == "verified"
        meta = atom["lean_metadata"]
        assert meta["known_witness_used"] is False
        assert meta["translator_version"] == "mumei-lean-translator-ir-v2"
        assert meta["bridge_lemma_hash"] == (
            "5716cfdd945d68b4a0d75d75c5ade1934cbd76e0dfe16734a8f3dd723cfdd8e9"
        )
        rules = meta["translator_ir"]["lowering_rules"]
        assert "nested_if_lowering" in rules
        assert payload["all_verified"] is True
    finally:
        _cleanup_generated_file(GENERATED_SATURATING)


GENERATED_TASK_STRUCT = (
    REPO_ROOT
    / "generated"
    / "Generated"
    / "Concurrency"
    / "Task_struct_capture_double_move_fail.lean"
)


@pytest.mark.lake_available
def test_struct_projection_body_semantics_upgrade_unknown_to_lean_verified(
    lake_available, tmp_path: Path
):
    """Spec §4.6: `p.x` lowers to the scalar binder `p_x`.

    The fixture atom was partial (`unknown_token` on `.`) before the
    projection lowering; it must now build via body semantics without a
    known witness and without touching the bridge lemma catalog.
    """
    out_cert = tmp_path / "task_struct.lean-cert.json"
    out_dir = tmp_path / "generated"
    _cleanup_generated_file(GENERATED_TASK_STRUCT)
    try:
        proc = _run_bridge(
            "--cert",
            str(FIXTURES / "concurrency_task_struct_projection.proof-cert.json"),
            "--out-dir",
            str(out_dir),
            "--lean-cert-out",
            str(out_cert),
        )
        _assert_bridge_ok(proc)
        assert "0 partial translation" in proc.stdout
        generated_src = GENERATED_TASK_STRUCT.read_text()
        assert "def takePointResult (p_x : Int) : Int :=" in generated_src
        assert "(p_x ≥ 0) → (result ≥ 0)" in generated_src
        payload = json.loads(out_cert.read_text())
        atom = next(a for a in payload["atoms"] if a["name"] == "take_point")
        assert atom["z3_check_result"] == "lean_verified"
        assert atom["status"] == "verified"
        meta = atom["lean_metadata"]
        assert meta["known_witness_used"] is False
        assert meta["translator_version"] == "mumei-lean-translator-ir-v2"
        assert meta["bridge_lemma_hash"] == (
            "5716cfdd945d68b4a0d75d75c5ade1934cbd76e0dfe16734a8f3dd723cfdd8e9"
        )
        rules = meta["translator_ir"]["lowering_rules"]
        assert "struct_projection_lowering" in rules
        assert payload["all_verified"] is True
    finally:
        _cleanup_generated_file(GENERATED_TASK_STRUCT)


GENERATED_TASK_GROUP = (
    REPO_ROOT / "generated" / "Generated" / "Concurrency" / "Task_group_all.lean"
)
GENERATED_TASK_GROUP_ANY = (
    REPO_ROOT / "generated" / "Generated" / "Concurrency" / "Task_group_any_winner.lean"
)


@pytest.mark.lake_available
def test_task_group_all_body_semantics_upgrade_unknown_to_lean_verified(
    lake_available, tmp_path: Path
):
    """Spec §4.7: `task_group:all` yields its last task's value.

    The fixture atom was partial (`unknown_token` on `task`/`:`/`;`)
    before the task-group lowering; it must now build via body
    semantics without a known witness.
    """
    out_cert = tmp_path / "task_group.lean-cert.json"
    out_dir = tmp_path / "generated"
    _cleanup_generated_file(GENERATED_TASK_GROUP)
    try:
        proc = _run_bridge(
            "--cert",
            str(FIXTURES / "concurrency_task_group_all.proof-cert.json"),
            "--out-dir",
            str(out_dir),
            "--lean-cert-out",
            str(out_cert),
        )
        _assert_bridge_ok(proc)
        assert "0 partial translation" in proc.stdout
        generated_src = GENERATED_TASK_GROUP.read_text()
        assert "def joinAllLastResultResult (a b : Int) : Int :=" in generated_src
        assert "(a ≥ 0 ∧ b ≥ 0) → (result = b)" in generated_src
        payload = json.loads(out_cert.read_text())
        atom = next(a for a in payload["atoms"] if a["name"] == "join_all_last_result")
        assert atom["z3_check_result"] == "lean_verified"
        assert atom["status"] == "verified"
        meta = atom["lean_metadata"]
        assert meta["known_witness_used"] is False
        assert meta["translator_version"] == "mumei-lean-translator-ir-v2"
        assert meta["bridge_lemma_hash"] == (
            "5716cfdd945d68b4a0d75d75c5ade1934cbd76e0dfe16734a8f3dd723cfdd8e9"
        )
        rules = meta["translator_ir"]["lowering_rules"]
        assert "task_group_all_lowering" in rules
        assert meta["translator_ir"]["obligation_class"] == "concurrency_obligation"
        assert payload["all_verified"] is True
    finally:
        _cleanup_generated_file(GENERATED_TASK_GROUP)


@pytest.mark.lake_available
def test_task_group_any_body_semantics_upgrade_unknown_to_lean_verified(
    lake_available, tmp_path: Path
):
    """Spec §4.7: `task_group:any` — `result` is whichever task wins.

    The def yields the ``List Int`` of candidate values and the theorem
    hypothesises ``result ∈ <def>``; ``fin_cases`` splits the membership
    into one goal per task value, each closed by the arithmetic cascade
    under ``requires``.
    """
    out_cert = tmp_path / "task_group_any.lean-cert.json"
    out_dir = tmp_path / "generated"
    _cleanup_generated_file(GENERATED_TASK_GROUP_ANY)
    try:
        proc = _run_bridge(
            "--cert",
            str(FIXTURES / "concurrency_task_group_any.proof-cert.json"),
            "--out-dir",
            str(out_dir),
            "--lean-cert-out",
            str(out_cert),
        )
        _assert_bridge_ok(proc)
        assert "0 partial translation" in proc.stdout
        generated_src = GENERATED_TASK_GROUP_ANY.read_text()
        assert "def raceTwoReplicasResult (a b : Int) : List Int :=" in generated_src
        assert "(h_body : result ∈ raceTwoReplicasResult a b)" in generated_src
        assert "fin_cases h_body" in generated_src
        payload = json.loads(out_cert.read_text())
        atom = next(a for a in payload["atoms"] if a["name"] == "race_two_replicas")
        assert atom["z3_check_result"] == "lean_verified"
        assert atom["status"] == "verified"
        meta = atom["lean_metadata"]
        assert meta["known_witness_used"] is False
        assert meta["translator_version"] == "mumei-lean-translator-ir-v2"
        assert meta["bridge_lemma_hash"] == (
            "5716cfdd945d68b4a0d75d75c5ade1934cbd76e0dfe16734a8f3dd723cfdd8e9"
        )
        rules = meta["translator_ir"]["lowering_rules"]
        assert "task_group_any_lowering" in rules
        assert meta["translator_ir"]["obligation_class"] == "concurrency_obligation"
        assert payload["all_verified"] is True
    finally:
        _cleanup_generated_file(GENERATED_TASK_GROUP_ANY)


GENERATED_LOOP_INVARIANT = (
    REPO_ROOT
    / "generated"
    / "Generated"
    / "Benchmarks"
    / "Svcomp_style"
    / "Loop_invariant.lean"
)

LOOP_VC_PROOF_SCRIPT = """intro h
obtain ⟨hn, -, hall⟩ := h
refine ⟨?_, ?_, ?_, ?_⟩
· refine ⟨by omega, by omega, by omega⟩
· intro sum i hi
  obtain ⟨h1, h2, h3, h4⟩ := hi
  have harr := hall i h1 h4
  refine ⟨by omega, by omega, by omega⟩
· intro sum i hi
  obtain ⟨h1, -, -, h4⟩ := hi
  omega
· intro sum i hi result hr
  obtain ⟨-, -, h3, -⟩ := hi
  omega"""


@pytest.mark.lake_available
def test_while_loop_invariant_emits_vc_theorem_shape(
    lake_available, tmp_path: Path
):
    """Spec §4.8: a while+invariant body emits the loop's verification
    conditions as the theorem goal — no ``def``/``h_body`` — and the
    generic ``mumei_arith_deep`` ladder cannot close it, so the atom
    stays ``unknown`` and remains a B-4 external-proof input.
    """
    out_cert = tmp_path / "loop_invariant.lean-cert.json"
    out_dir = tmp_path / "generated"
    _cleanup_generated_file(GENERATED_LOOP_INVARIANT)
    try:
        proc = _run_bridge(
            "--cert",
            str(FIXTURES / "svcomp_style_loop_invariant.proof-cert.json"),
            "--out-dir",
            str(out_dir),
            "--lean-cert-out",
            str(out_cert),
        )
        assert proc.returncode == 1, proc.stdout + proc.stderr
        assert "0 partial translation" in proc.stdout
        generated_src = GENERATED_LOOP_INVARIANT.read_text()
        assert "theorem sum_array_correct (n : Int) (arr : List Int)" in generated_src
        assert "def " not in generated_src
        assert "h_body" not in generated_src
        # VC conjuncts: invariant base, step, decreases, exit→ensures.
        assert "0 ≥ 0 ∧ 0 ≤ n ∧ 0 ≥ 0" in generated_src
        assert "∀ sum i : Int" in generated_src
        assert "¬ (i < n)" in generated_src
        assert "result = (sum) → (result ≥ 0)" in generated_src
        assert "sorry" not in generated_src
        payload = json.loads(out_cert.read_text())
        atom = next(a for a in payload["atoms"] if a["name"] == "sum_array")
        assert atom["z3_check_result"] == "unknown"
        meta = atom["lean_metadata"]
        assert meta["status"] == "manual_lemma_required"
        assert meta["known_witness_used"] is False
        assert meta.get("ai_proof_used") is not True
        rules = meta["translator_ir"]["lowering_rules"]
        assert "while_loop_invariant_lowering" in rules
    finally:
        _cleanup_generated_file(GENERATED_LOOP_INVARIANT)


@pytest.mark.lake_available
def test_while_loop_invariant_vc_provable_via_external_proof(
    lake_available, tmp_path: Path
):
    """Spec §4.8/B-4: the emitted VC theorem is provable — a supplied
    external proof script (invariant intro + per-conjunct discharge)
    lifts the atom to ``lean_verified``.
    """
    proofs = tmp_path / "proofs.json"
    proofs.write_text(
        json.dumps(
            {
                "proofs": [
                    {
                        "atom": "sum_array",
                        "attempts": 1,
                        "tactic_script": LOOP_VC_PROOF_SCRIPT,
                    }
                ]
            }
        )
    )
    out_cert = tmp_path / "loop_invariant.lean-cert.json"
    out_dir = tmp_path / "generated"
    _cleanup_generated_file(GENERATED_LOOP_INVARIANT)
    try:
        proc = _run_bridge(
            "--cert",
            str(FIXTURES / "svcomp_style_loop_invariant.proof-cert.json"),
            "--out-dir",
            str(out_dir),
            "--lean-cert-out",
            str(out_cert),
            "--no-tactic-search",
            "--external-proofs",
            str(proofs),
        )
        _assert_bridge_ok(proc)
        generated_src = GENERATED_LOOP_INVARIANT.read_text()
        assert "sorry" not in generated_src
        payload = json.loads(out_cert.read_text())
        atom = next(a for a in payload["atoms"] if a["name"] == "sum_array")
        assert atom["z3_check_result"] == "lean_verified"
        assert atom["status"] == "verified"
        meta = atom["lean_metadata"]
        assert meta["status"] == "lean_verified"
        assert meta["ai_proof_used"] is True
        assert meta["ai_proof_attempts"] == 1
        assert meta["external_proof"]["source"] == "ai_generated_proof"
        assert meta["known_witness_used"] is False
        assert meta["bridge_lemma_hash"] == (
            "5716cfdd945d68b4a0d75d75c5ade1934cbd76e0dfe16734a8f3dd723cfdd8e9"
        )
        assert payload["all_verified"] is True
    finally:
        _cleanup_generated_file(GENERATED_LOOP_INVARIANT)


GENERATED_REGTECH_LOOP = (
    REPO_ROOT
    / "generated"
    / "Generated"
    / "Benchmarks"
    / "Domain_compliance"
    / "Regtech_exhaustiveness.lean"
)

# ``all_transactions_within_limit``'s requires renders the spec-level
# ``forall`` as ``true`` (the emitted certificate drops it), so its loop
# VC needs no elementwise hypothesis and ``omega`` discharges every
# conjunct once the quantified carry is introduced.
REGTECH_LOOP_PROOF_SCRIPT = """intro h
obtain ⟨hn, -, -, -⟩ := h
refine ⟨?_, ?_, ?_, ?_⟩
· refine ⟨by omega, by omega, by omega⟩
· intro count i hi
  obtain ⟨h1, h2, h3, h4⟩ := hi
  refine ⟨by omega, by omega, by omega⟩
· intro count i hi
  obtain ⟨h1, h2, -, h4⟩ := hi
  omega
· intro count i hi result hr
  obtain ⟨-, -, h3, -⟩ := hi
  omega"""


@pytest.mark.lake_available
def test_loop_vc_declared_array_types_provable_via_external_proof(
    lake_available, tmp_path: Path
):
    """Real-cert shape: a ``[i64]`` parameter that is never indexed still
    binds ``List Int`` (declared ``translator_ir`` types are authoritative)
    and its loop VC is closable by a supplied external proof."""
    proofs = tmp_path / "proofs.json"
    proofs.write_text(
        json.dumps(
            {
                "proofs": [
                    {
                        "atom": "all_transactions_within_limit",
                        "attempts": 1,
                        "tactic_script": REGTECH_LOOP_PROOF_SCRIPT,
                    }
                ]
            }
        )
    )
    out_cert = tmp_path / "regtech_loop.lean-cert.json"
    out_dir = tmp_path / "generated"
    _cleanup_generated_file(GENERATED_REGTECH_LOOP)
    try:
        proc = _run_bridge(
            "--cert",
            str(FIXTURES / "domain_compliance_regtech_loop.proof-cert.json"),
            "--out-dir",
            str(out_dir),
            "--lean-cert-out",
            str(out_cert),
            "--no-tactic-search",
            "--external-proofs",
            str(proofs),
        )
        _assert_bridge_ok(proc)
        generated_src = GENERATED_REGTECH_LOOP.read_text()
        assert "(amounts : List Int)" in generated_src
        assert "mumei_len" not in generated_src
        payload = json.loads(out_cert.read_text())
        atom = next(
            a
            for a in payload["atoms"]
            if a["name"] == "all_transactions_within_limit"
        )
        assert atom["z3_check_result"] == "lean_verified"
        meta = atom["lean_metadata"]
        assert meta["ai_proof_used"] is True
        assert meta["known_witness_used"] is False
    finally:
        _cleanup_generated_file(GENERATED_REGTECH_LOOP)


GENERATED_LIST_RETURNING_LOOP = (
    REPO_ROOT
    / "generated"
    / "Generated"
    / "Benchmarks"
    / "Svcomp_style"
    / "List_returning_loop.lean"
)

# Spec §4.8: ``copy_prefix`` returns ``[i64]``, so its post conjunct binds
# ``result : List Int`` (declared ``translator_ir`` result type) and
# ``result.length`` ensures forms elaborate; the VC closes once ``result``
# is substituted for the tail expression.
LIST_RETURNING_LOOP_PROOF_SCRIPT = """intro h
obtain ⟨hn, harr⟩ := h
refine ⟨?_, ?_, ?_, ?_⟩
· refine ⟨by omega, by omega⟩
· intro i hi
  obtain ⟨h1, h2, h3⟩ := hi
  refine ⟨by omega, by omega⟩
· intro i hi
  obtain ⟨h1, h2, h3⟩ := hi
  omega
· intro i hi result hr
  subst hr
  omega"""


@pytest.mark.lake_available
def test_loop_vc_list_result_provable_via_external_proof(
    lake_available, tmp_path: Path
):
    """A ``-> [i64]`` while-loop VC quantifies ``result : List Int`` in
    its post conjunct, so ``len(result)`` ensures elaborate and the
    supplied external proof lifts the atom to ``lean_verified``."""
    proofs = tmp_path / "proofs.json"
    proofs.write_text(
        json.dumps(
            {
                "proofs": [
                    {
                        "atom": "copy_prefix",
                        "attempts": 1,
                        "tactic_script": LIST_RETURNING_LOOP_PROOF_SCRIPT,
                    }
                ]
            }
        )
    )
    out_cert = tmp_path / "list_returning_loop.lean-cert.json"
    out_dir = REPO_ROOT / "generated"
    _cleanup_generated_file(GENERATED_LIST_RETURNING_LOOP)
    try:
        proc = _run_bridge(
            "--cert",
            str(FIXTURES / "svcomp_style_list_returning_loop.proof-cert.json"),
            "--out-dir",
            str(out_dir),
            "--lean-cert-out",
            str(out_cert),
            "--no-tactic-search",
            "--external-proofs",
            str(proofs),
        )
        _assert_bridge_ok(proc)
        generated_src = GENERATED_LIST_RETURNING_LOOP.read_text()
        assert "∀ (result : List Int)" in generated_src
        assert "(result : Int)" not in generated_src
        payload = json.loads(out_cert.read_text())
        atom = next(a for a in payload["atoms"] if a["name"] == "copy_prefix")
        assert atom["z3_check_result"] == "lean_verified"
        assert atom["status"] == "verified"
        meta = atom["lean_metadata"]
        assert meta["status"] == "lean_verified"
        assert meta["ai_proof_used"] is True
        assert meta["known_witness_used"] is False
        assert meta["bridge_lemma_hash"] == (
            "5716cfdd945d68b4a0d75d75c5ade1934cbd76e0dfe16734a8f3dd723cfdd8e9"
        )
        assert payload["all_verified"] is True
    finally:
        _cleanup_generated_file(GENERATED_LIST_RETURNING_LOOP)


GENERATED_LOOP_FORALL = (
    REPO_ROOT
    / "generated"
    / "Generated"
    / "Benchmarks"
    / "Svcomp_style"
    / "Loop_invariant.lean"
)

GENERATED_RTGS_LOOP = (
    REPO_ROOT
    / "generated"
    / "Generated"
    / "Benchmarks"
    / "Domain_compliance"
    / "Rtgs_balance_conservation.lean"
)

# Real-cert shape: ``requires`` renders the ``forall`` conjunct as ``true``
# and ``forall_constraints`` carries it structurally; ingest restores it as
# ``∀ i, 0 ≤ i → i < n → arr[i] ≥ 0``, which the step conjunct needs.
SUM_ARRAY_FORALL_PROOF_SCRIPT = """intro h
obtain ⟨hn, -, -, hall⟩ := h
refine ⟨?_, ?_, ?_, ?_⟩
· refine ⟨by omega, by omega, by omega⟩
· intro sum i hi
  obtain ⟨h1, h2, h3, h4⟩ := hi
  have harr := hall i h1 h4
  refine ⟨by omega, by omega, by omega⟩
· intro sum i hi
  obtain ⟨h1, -, -, h4⟩ := hi
  omega
· intro sum i hi result hr
  obtain ⟨-, -, h3, -⟩ := hi
  omega"""

RTGS_LOOP_PROOF_SCRIPT = """intro h
obtain ⟨hn, -, -, hall⟩ := h
refine ⟨?_, ?_, ?_, ?_⟩
· refine ⟨by omega, by omega, by omega⟩
· intro total i hi
  obtain ⟨h1, h2, h3, h4⟩ := hi
  have hb := hall i h1 h4
  refine ⟨by omega, by omega, by omega⟩
· intro total i hi
  obtain ⟨h1, -, -, h4⟩ := hi
  omega
· intro total i hi result hr
  obtain ⟨-, -, h3, -⟩ := hi
  omega"""


@pytest.mark.lake_available
@pytest.mark.parametrize(
    "fixture,generated,atom,script",
    [
        (
            "svcomp_style_loop_invariant_forall.proof-cert.json",
            GENERATED_LOOP_FORALL,
            "sum_array",
            SUM_ARRAY_FORALL_PROOF_SCRIPT,
        ),
        (
            "domain_compliance_rtgs_loop_forall.proof-cert.json",
            GENERATED_RTGS_LOOP,
            "queue_total_is_nonnegative",
            RTGS_LOOP_PROOF_SCRIPT,
        ),
    ],
    ids=["sum_array", "queue_total_is_nonnegative"],
)
def test_loop_vc_forall_constraints_provable_via_external_proof(
    lake_available, tmp_path: Path, fixture, generated, atom, script
):
    """Real-cert loop VCs with elementwise ``forall`` hypotheses restored
    from ``forall_constraints`` verify via the B-4 external-proof route
    (群 3: ``sum_array`` and ``queue_total_is_nonnegative``)."""
    proofs = tmp_path / "proofs.json"
    proofs.write_text(
        json.dumps(
            {"proofs": [{"atom": atom, "attempts": 1, "tactic_script": script}]}
        )
    )
    out_cert = tmp_path / "loop.lean-cert.json"
    out_dir = tmp_path / "generated"
    _cleanup_generated_file(generated)
    try:
        proc = _run_bridge(
            "--cert",
            str(FIXTURES / fixture),
            "--out-dir",
            str(out_dir),
            "--lean-cert-out",
            str(out_cert),
            "--no-tactic-search",
            "--external-proofs",
            str(proofs),
        )
        _assert_bridge_ok(proc)
        generated_src = generated.read_text()
        assert "∀ i : Int, 0 ≤ i" in generated_src
        payload = json.loads(out_cert.read_text())
        found = next(a for a in payload["atoms"] if a["name"] == atom)
        assert found["z3_check_result"] == "lean_verified"
        meta = found["lean_metadata"]
        assert meta["ai_proof_used"] is True
        assert meta["known_witness_used"] is False
    finally:
        _cleanup_generated_file(generated)


GENERATED_QUINTIC = REPO_ROOT / "generated" / "Generated" / "Std" / "Quintic.lean"
QUINTIC_GOOD_SCRIPT = (
    "intro hx\nsubst h_body\nunfold quinticPosResult\n"
    "have h2 : 0 < x * x := mul_pos hx hx\n"
    "exact mul_pos (mul_pos (mul_pos h2 hx) hx) hx"
)


@pytest.mark.lake_available
@pytest.mark.parametrize(
    ("label", "entry", "expect_verified", "expect_rejected", "expect_failure_kind"),
    [
        ("valid_script", {"tactic_script": QUINTIC_GOOD_SCRIPT}, True, None, None),
        (
            "sorry",
            {"tactic_script": "intro hx\nsorry"},
            False,
            "forbidden_token:sorry",
            None,
        ),
        (
            "unsolved_goals",
            {"tactic_script": "intro hx\nsubst h_body\nunfold quinticPosResult"},
            False,
            None,
            "unsolved_goals",
        ),
        (
            "type_mismatch",
            {"tactic_script": "intro hx\nexact hx"},
            False,
            None,
            "type_mismatch",
        ),
        (
            "missing_witness",
            {"witness_lemma": "Std.Quintic.no_such_lemma", "source": "handwritten_witness"},
            False,
            None,
            "unknown_identifier",
        ),
    ],
)
def test_external_proof_matrix_never_promotes_unproved_atoms(
    lake_available,
    tmp_path: Path,
    label,
    entry,
    expect_verified,
    expect_rejected,
    expect_failure_kind,
):
    """Spec §13.4: only a script that really builds yields ``lean_verified``.

    The fixture (``x > 0 → x⁵ > 0``) is out of reach for the generic
    ``mumei_arith_deep`` ladder, so promotion can only come from the
    supplied proof — and the failing rows prove it never does falsely.
    Rows that reach Lake must also leave an atom-attributed entry of the
    expected ``kind`` in the B-3 failure report, because that entry is what
    mumei-agent feeds back to the model for the next attempt.
    """
    proofs = tmp_path / "proofs.json"
    proofs.write_text(
        json.dumps({"proofs": [{"atom": "quintic_pos", "attempts": 3, **entry}]})
    )
    out_cert = tmp_path / "quintic.lean-cert.json"
    out_dir = tmp_path / "generated"
    _cleanup_generated_file(GENERATED_QUINTIC)
    try:
        proc = _run_bridge(
            "--cert",
            str(FIXTURES / "std_quintic_external_proof.proof-cert.json"),
            "--out-dir",
            str(out_dir),
            "--lean-cert-out",
            str(out_cert),
            "--no-tactic-search",
            "--external-proofs",
            str(proofs),
        )
        if expect_verified:
            _assert_bridge_ok(proc)
        else:
            assert proc.returncode == 1, proc.stdout + proc.stderr
        generated_src = GENERATED_QUINTIC.read_text()
        assert "sorry" not in generated_src
        assert "theorem quintic_pos_correct (x : Int) (result : Int)" in generated_src
        payload = json.loads(out_cert.read_text())
        [atom] = payload["atoms"]
        meta = atom["lean_metadata"]
        assert meta["translator_version"] == "mumei-lean-translator-ir-v2"
        assert meta["bridge_lemma_hash"] == (
            "5716cfdd945d68b4a0d75d75c5ade1934cbd76e0dfe16734a8f3dd723cfdd8e9"
        )
        if expect_rejected is not None:
            assert f"rejected: {expect_rejected}" in proc.stderr
            assert meta["external_proof"] == {"rejected": expect_rejected}
            assert "external_proof:" not in generated_src
        else:
            assert meta["external_proof"]["source"] == entry.get(
                "source", "ai_generated_proof"
            )
            assert meta["ai_proof_attempts"] == 3
        if expect_verified:
            assert atom["z3_check_result"] == "lean_verified"
            assert meta["status"] == "lean_verified"
            assert meta["ai_proof_used"] is True
            assert payload["all_verified"] is True
        else:
            assert atom["z3_check_result"] == "unknown"
            assert meta["status"] == "manual_lemma_required"
            assert meta["ai_proof_used"] is False
            assert payload["all_verified"] is False
        report_path = out_dir / "lake_build_failures.json"
        if expect_failure_kind is not None:
            report = json.loads(report_path.read_text())
            assert report["schema"] == "mumei-lean-build-failures-v1"
            attributed = [f for f in report["failures"] if f["atom"] == "quintic_pos"]
            assert attributed, report
            assert expect_failure_kind in {f["kind"] for f in attributed}, report
            assert all(isinstance(f["line"], int) for f in attributed), report
        elif expect_verified and report_path.exists():
            report = json.loads(report_path.read_text())
            assert not [f for f in report["failures"] if f["atom"] == "quintic_pos"], report
    finally:
        _cleanup_generated_file(GENERATED_QUINTIC)
