"""Tests for ``scripts.bridge``."""
from __future__ import annotations

import json
from pathlib import Path

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


def _cert(file: str, atoms: list) -> dict:
    return {
        "version": "1.0",
        "timestamp": "2026-04-28T00:00:00Z",
        "mumei_version": "0.5.6",
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
    (certs_dir / "todo.json").write_text(
        json.dumps(_cert("std/todo.mm", [_atom("b", z3="unknown")]))
    )
    found = _scan_unknown_certs(certs_dir)
    assert [p.name for p, _ in found] == ["todo.json"]


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
    assert payload == {"total_unknown": 0, "modules": []}


def _patch_lake(monkeypatch, rc: int, log: str) -> None:
    """Replace :func:`bridge._run_lake_build` with a deterministic stub."""

    def fake_run(repo_dir: Path, log_path: Path) -> int:
        log_path.parent.mkdir(parents=True, exist_ok=True)
        log_path.write_text(log)
        return rc

    monkeypatch.setattr(bridge, "_run_lake_build", fake_run)


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
