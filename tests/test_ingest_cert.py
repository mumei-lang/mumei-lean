"""Tests for ``scripts.ingest_cert``."""
from __future__ import annotations

import json
from pathlib import Path

import pytest

from ingest_cert import (
    _classify_input,
    _module_to_lean_namespace,
    collect_unknown_atoms,
    render_module,
    render_theorem,
    write_modules,
)


def _make_atom(
    name: str,
    requires: str = "",
    ensures: str = "",
    z3: str = "unknown",
    status: str = "unknown",
    body_expr: str = "",
    body_summary: str = "",
) -> dict:
    atom = {
        "name": name,
        "requires": requires,
        "ensures": ensures,
        "z3_check_result": z3,
        "status": status,
        "content_hash": "",
        "proof_hash": "",
        "dependencies": [],
        "effects": [],
    }
    if body_expr:
        atom["body_expr"] = body_expr
    if body_summary:
        atom["body_summary"] = body_summary
    return atom


def _make_certificate(file: str, atoms: list) -> dict:
    return {
        "version": "1.0",
        "timestamp": "2026-04-28T00:00:00Z",
        "mumei_version": "0.5.6",
        "z3_version": "4.12.2",
        "file": file,
        "atoms": atoms,
        "package_name": "test",
        "package_version": "0.0.0",
        "certificate_hash": "",
        "all_verified": False,
    }


def test_classify_input_recognises_certificate_and_bundle():
    cert = _make_certificate("a.mm", [_make_atom("a")])
    assert _classify_input(cert) == "certificate"

    bundle = {
        "bundle_version": "1.0",
        "modules": {"std/core": cert},
        "summary": {},
    }
    assert _classify_input(bundle) == "bundle"

    with pytest.raises(ValueError):
        _classify_input({"unrelated": True})


def test_collect_unknown_atoms_filters_by_z3_check_result():
    cert = _make_certificate(
        "math.mm",
        [
            _make_atom("a", z3="unknown"),
            _make_atom("b", z3="unsat"),
            _make_atom("c", z3="unknown"),
        ],
    )
    atoms = collect_unknown_atoms(cert)
    assert [a.name for a in atoms] == ["a", "c"]


def test_collect_unknown_atoms_handles_bundle():
    cert_a = _make_certificate("std/core.mm", [_make_atom("ax", z3="unknown")])
    cert_b = _make_certificate(
        "std/list.mm",
        [_make_atom("bx", z3="unsat"), _make_atom("cx", z3="unknown")],
    )
    bundle = {
        "bundle_version": "1.0",
        "modules": {"std/core": cert_a, "std/list": cert_b},
        "summary": {},
    }
    atoms = collect_unknown_atoms(bundle)
    names = sorted(a.name for a in atoms)
    assert names == ["ax", "cx"]
    keys = {a.module_key for a in atoms}
    assert keys == {"std/core", "std/list"}


def test_module_to_lean_namespace_capitalises_and_sanitises():
    assert _module_to_lean_namespace("std/core", "Generated") == "Generated.Std.Core"
    assert _module_to_lean_namespace("std/sub-mod/0name", "G") == "G.Std.Sub_mod.M0name"


def test_render_theorem_includes_atom_name_and_mumei_arith_body():
    # PR 4: render_theorem now defaults to ``mumei_arith <;> sorry``
    # (mathlib4-backed automation with a ``sorry`` fallback) instead
    # of a bare ``sorry``. The ``sorry`` substring is still present so
    # ``scripts/export_cert.py``'s warning detection keeps working.
    cert = _make_certificate(
        "m.mm",
        [_make_atom("inc", requires="x > 0", ensures="result >= x")],
    )
    [atom] = collect_unknown_atoms(cert)
    rendered = render_theorem(atom)
    assert "theorem inc_correct" in rendered
    assert "mumei_arith <;> sorry" in rendered
    # both x and result should appear in the params declaration
    assert "x" in rendered
    assert "result" in rendered


def test_render_theorem_injects_body_semantics_for_simple_body():
    cert = _make_certificate(
        "std/math/abs.mm",
        [
            _make_atom(
                "abs_auto",
                requires="true",
                ensures="result >= 0",
                body_expr="if x >= 0 then x else -x",
                body_summary="absolute value",
            )
        ],
    )
    [atom] = collect_unknown_atoms(cert)
    assert atom.body_expr == "if x >= 0 then x else -x"
    rendered = render_theorem(atom)
    assert "def absAutoResult (x : Int) : Int :=" in rendered
    assert "if x ≥ 0 then x else - x" in rendered
    assert "(h_body : result = absAutoResult x)" in rendered
    assert "rw [h_body]" in rendered
    assert "unfold absAutoResult" in rendered
    assert "mumei_arith_deep <;> sorry" in rendered


def test_render_theorem_falls_back_for_complex_body():
    cert = _make_certificate(
        "m.mm",
        [
            _make_atom(
                "custom",
                requires="true",
                ensures="result >= 0",
                body_expr="custom_fn(x)",
            )
        ],
    )
    [atom] = collect_unknown_atoms(cert)
    rendered = render_theorem(atom)
    assert "def customResult" not in rendered
    assert "body semantics unsupported" in rendered
    assert "mumei_arith <;> sorry" in rendered


def test_render_theorem_falls_back_when_body_references_result():
    cert = _make_certificate(
        "m.mm",
        [
            _make_atom(
                "self_ref",
                requires="true",
                ensures="result >= 0",
                body_expr="result + 1",
            )
        ],
    )
    [atom] = collect_unknown_atoms(cert)
    rendered = render_theorem(atom)
    assert "def selfRefResult" not in rendered
    assert "body semantics unsupported" in rendered
    assert "mumei_arith <;> sorry" in rendered


def test_render_theorem_does_not_add_result_param_for_substring_matches():
    # Identifier ``results`` must not trigger a spurious ``result : Int``
    # parameter in the emitted theorem signature.
    import re

    cert = _make_certificate(
        "m.mm",
        [_make_atom("count_pos", requires="results > 0", ensures="results >= 0")],
    )
    [atom] = collect_unknown_atoms(cert)
    rendered = render_theorem(atom)
    assert "theorem count_pos_correct" in rendered
    # ``results`` is the free identifier; ``result`` (whole word) must
    # NOT appear in the parameter list.
    assert "results" in rendered
    # Match the parameter list ``(... : Int)`` and check that ``result``
    # is not one of the bound identifiers.
    params_match = re.search(r"\(([^)]*) : Int\)", rendered)
    assert params_match is not None
    bound_idents = params_match.group(1).split()
    assert "result" not in bound_idents
    assert "results" in bound_idents

    cert2 = _make_certificate(
        "m.mm",
        [_make_atom("nr", requires="no_result > 0", ensures="no_result == 1")],
    )
    [atom2] = collect_unknown_atoms(cert2)
    rendered2 = render_theorem(atom2)
    params_match2 = re.search(r"\(([^)]*) : Int\)", rendered2)
    assert params_match2 is not None
    bound_idents2 = params_match2.group(1).split()
    assert "result" not in bound_idents2
    assert "no_result" in bound_idents2


def test_render_theorem_adds_result_param_when_token_is_operator_adjacent():
    # ``result>=x`` (no whitespace) used to slip past the ``.split()``
    # check; ensure the tokenised path still picks it up.
    cert = _make_certificate(
        "m.mm",
        [_make_atom("inc", requires="x > 0", ensures="result>=x")],
    )
    [atom] = collect_unknown_atoms(cert)
    rendered = render_theorem(atom)
    assert "theorem inc_correct" in rendered
    assert "result" in rendered


def test_render_module_emits_namespace_header_and_imports():
    cert = _make_certificate(
        "math.mm",
        [_make_atom("inc", requires="x > 0", ensures="result >= x")],
    )
    atoms = collect_unknown_atoms(cert)
    src = render_module("std/math", "Generated", atoms)
    assert "namespace Generated.Std.Math" in src
    assert "import MumeiLean" in src
    assert "end Generated.Std.Math" in src.strip().split("\n")[-1]


def test_write_modules_groups_by_module_key(tmp_path: Path):
    cert_a = _make_certificate("std/core.mm", [_make_atom("ax", z3="unknown")])
    cert_b = _make_certificate("std/list.mm", [_make_atom("bx", z3="unknown")])
    bundle = {
        "bundle_version": "1.0",
        "modules": {"std/core": cert_a, "std/list": cert_b},
        "summary": {},
    }
    atoms = collect_unknown_atoms(bundle)
    out_dir = tmp_path / "generated"
    written = write_modules(atoms, out_dir, "Generated")
    rels = sorted(p.relative_to(out_dir).as_posix() for p in written)
    assert rels == ["Generated/Std/Core.lean", "Generated/Std/List.lean"]
    for path in written:
        assert path.exists()
        assert "namespace Generated.Std." in path.read_text()


def test_render_theorem_forall_contract_uses_lean_quantifier_and_list_typing():
    # Integration check that ``forall`` / ``arr[i]`` lower into the
    # PR 4 surface end-to-end via render_theorem (not just the
    # translator in isolation).
    cert = _make_certificate(
        "math.mm",
        [
            _make_atom(
                "forall_atom",
                requires="n >= 0 && forall(i, 0, n, arr[i] >= 0)",
                ensures="forall(i, 0, n, arr[i] >= 0)",
            )
        ],
    )
    [atom] = collect_unknown_atoms(cert)
    rendered = render_theorem(atom)
    # Lean ``∀`` quantifier in the theorem body.
    assert "∀ i : Int" in rendered
    # ``arr`` is reported as a list, not a scalar Int.
    assert "(arr : List Int)" in rendered
    assert "(arr : Int)" not in rendered
    # ``arr.get! i.toNat`` lowering appears in the rendered body.
    # (List.get! takes ``Nat``; ``i`` is bound at ``Int`` by ``forall``.)
    assert "arr.get! i.toNat" in rendered
    # Default body now uses the mumei_arith automation.
    assert "mumei_arith <;> sorry" in rendered
    # No unproven marker — this contract is fully within the v2 surface.
    assert "TODO: unproven" not in rendered


def test_render_theorem_types_string_predicate_identifiers_as_string():
    cert = _make_certificate(
        "http.mm",
        [
            _make_atom(
                "secure_get",
                requires='starts_with(url, "https://")',
                ensures="result >= 0",
            )
        ],
    )
    [atom] = collect_unknown_atoms(cert)
    rendered = render_theorem(atom)
    assert '(mumei_starts_with url "https://")' in rendered
    assert "(url : String)" in rendered
    assert "(url : Int)" not in rendered
    assert "TODO: unproven" not in rendered


def test_main_writes_files(tmp_path: Path):
    from ingest_cert import main

    cert = _make_certificate(
        "math.mm",
        [_make_atom("inc", requires="x > 0", ensures="result >= x")],
    )
    cert_path = tmp_path / "cert.json"
    cert_path.write_text(json.dumps(cert))
    out_dir = tmp_path / "out"
    rc = main([str(cert_path), "--out", str(out_dir), "--module-prefix", "Gen"])
    assert rc == 0
    expected = out_dir / "Gen" / "Math.lean"
    assert expected.exists()
    text = expected.read_text()
    assert "theorem inc_correct" in text
