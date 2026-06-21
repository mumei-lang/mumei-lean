"""Tests for ``scripts.ingest_cert``."""
from __future__ import annotations

import json
from pathlib import Path

import pytest

from ingest_cert import (
    _classify_input,
    _module_to_lean_namespace,
    _translate_expr,
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
        "mumei_version": "0.6.0",
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


def test_collect_unknown_atoms_accepts_unknown_status_class():
    cert = _make_certificate(
        "math.mm",
        [
            {
                **_make_atom("class_unknown", z3="timeout", status="pending"),
                "z3_result_class": "unknown",
            },
            _make_atom("status_unknown", z3="timeout", status="unknown"),
            _make_atom("sat", z3="sat", status="failed"),
        ],
    )
    atoms = collect_unknown_atoms(cert)
    assert [a.name for a in atoms] == ["class_unknown", "status_unknown"]


def test_collect_unknown_atoms_handles_escalation_bundle():
    bundle = {
        "version": "1.0",
        "file": "std/math.mm",
        "summary": {},
        "candidates": [
            {
                **_make_atom("nla", z3="timeout"),
                "z3_result_class": "timeout",
                "escalation_reason": "z3_timeout_or_resource_limit",
                "logic_fragment_tag": "nonlinear_arithmetic",
                "logic_fragment_tags": ["nonlinear_arithmetic"],
            }
        ],
    }
    assert _classify_input(bundle) == "escalation_bundle"
    [atom] = collect_unknown_atoms(bundle)
    assert atom.name == "nla"
    assert atom.module_key == "std/math"
    assert atom.z3_result_class == "timeout"
    assert atom.escalation_reason == "z3_timeout_or_resource_limit"
    assert atom.logic_fragment_tag == "nonlinear_arithmetic"
    assert atom.logic_fragment_tags == ["nonlinear_arithmetic"]


def test_translate_expr_forall_pattern():
    result = _translate_expr("forall(i, 0, n, arr[i] >= 0)")

    assert "∀ i : Int" in result.lean_expr
    assert "0 ≤ i" in result.lean_expr
    assert "i < n" in result.lean_expr
    assert "arr.get! i.toNat ≥ 0" in result.lean_expr
    assert "i" not in result.identifiers
    assert result.is_partial is False


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
    # Generated obligations use automation directly; remaining subgoals
    # are reported as Lean build failures rather than masked by ``sorry``.
    cert = _make_certificate(
        "m.mm",
        [_make_atom("inc", requires="x > 0", ensures="result >= x")],
    )
    [atom] = collect_unknown_atoms(cert)
    rendered = render_theorem(atom)
    assert "theorem inc_correct" in rendered
    assert "mumei_arith" in rendered
    assert "sorry" not in rendered
    # both x and result should appear in the params declaration
    assert "x" in rendered
    assert "result" in rendered


def test_render_theorem_includes_escalation_traceability_comments():
    cert = _make_certificate(
        "m.mm",
        [
            {
                **_make_atom("nla", requires="x > 0", ensures="result >= x", z3="timeout"),
                "z3_result_class": "timeout",
                "escalation_reason": "z3_timeout_complex_fragment",
                "logic_fragment_tags": ["nonlinear_arithmetic"],
            }
        ],
    )
    [atom] = collect_unknown_atoms(cert)
    rendered = render_theorem(atom)
    assert "-- mumei_escalation_reason: z3_timeout_complex_fragment" in rendered
    assert "-- mumei_logic_fragment_tags: nonlinear_arithmetic" in rendered
    assert "-- mumei_z3_result_class: timeout" in rendered


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
    assert "mumei_arith_deep" in rendered
    assert "sorry" not in rendered


def test_render_theorem_delegates_known_abs_witness():
    cert = _make_certificate(
        "std/math/abs.mm",
        [
            _make_atom(
                "abs_saturating",
                requires="true",
                ensures="result >= 0",
                body_expr="if x >= 0 then x else -x",
            )
        ],
    )
    [atom] = collect_unknown_atoms(cert)
    rendered = render_theorem(atom)
    assert "known_witness_used=true" in rendered
    assert "MumeiLean.StdMathAbs.absSaturatingResult" in rendered
    assert "exact MumeiLean.StdMathAbs.abs_saturating_correct" in rendered
    assert "mumei_arith" not in rendered
    assert "sorry" not in rendered


def test_render_theorem_applies_translator_ir_binder_names_to_goal():
    cert = _make_certificate(
        "m.mm",
        [
            _make_atom(
                "reserved_binder",
                requires="theorem > 0",
                ensures="result >= theorem",
            )
        ],
    )
    [atom] = collect_unknown_atoms(cert)
    rendered = render_theorem(atom)
    assert "(theorem_binder result : Int)" in rendered
    assert "(theorem_binder > 0)" in rendered
    assert "(result ≥ theorem_binder)" in rendered


def test_render_theorem_applies_binder_mapping_to_body_semantics():
    raw_atom = _make_atom(
        "mapped_body",
        requires="true",
        ensures="result >= x",
        body_expr="x + 1",
    )
    raw_atom["binder_mapping"] = {"x": "x_lean"}
    cert = _make_certificate("m.mm", [raw_atom])
    [atom] = collect_unknown_atoms(cert)
    rendered = render_theorem(atom)
    assert "def mappedBodyResult (x_lean : Int) : Int :=" in rendered
    assert "x_lean + 1" in rendered
    assert "(result : Int)" in rendered
    assert "(h_body : result = mappedBodyResult x_lean)" in rendered
    assert "(result ≥ x_lean)" in rendered


def test_render_theorem_injects_list_body_semantics():
    cert = _make_certificate(
        "m.mm",
        [
            _make_atom(
                "list_body",
                requires="true",
                ensures="result[0] == x",
                body_expr="[x, y]",
            )
        ],
    )
    [atom] = collect_unknown_atoms(cert)
    rendered = render_theorem(atom)
    assert "def listBodyResult (x y : Int) : List Int :=" in rendered
    assert "[x, y]" in rendered
    assert "(result : List Int)" in rendered
    assert "(h_body : result = listBodyResult x y)" in rendered
    assert "body semantics unsupported" not in rendered


def test_render_theorem_injects_string_body_semantics():
    cert = _make_certificate(
        "m.mm",
        [
            _make_atom(
                "string_body",
                requires='starts_with(result, "M")',
                ensures='starts_with(result, "M")',
                body_expr='"Mumei"',
            )
        ],
    )
    [atom] = collect_unknown_atoms(cert)
    rendered = render_theorem(atom)
    assert "def stringBodyResult : String :=" in rendered
    assert '"Mumei"' in rendered
    assert "(result : String)" in rendered
    assert "(h_body : result = stringBodyResult)" in rendered
    assert "body semantics unsupported" not in rendered


def test_render_theorem_injects_quantified_body_semantics():
    cert = _make_certificate(
        "m.mm",
        [
            _make_atom(
                "quant_body",
                requires="true",
                ensures="result == true",
                body_expr="forall(i, 0, n, arr[i] >= 0)",
            )
        ],
    )
    [atom] = collect_unknown_atoms(cert)
    rendered = render_theorem(atom)
    assert "def quantBodyResult (n : Int) (arr : List Int) : Prop :=" in rendered
    assert "∀ i : Int" in rendered
    assert "arr.get! i.toNat ≥ 0" in rendered
    assert "(h_body : result = quantBodyResult n arr)" in rendered
    assert "body semantics unsupported" not in rendered


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
    assert "mumei_arith" in rendered
    assert "sorry" not in rendered


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
    assert "mumei_arith" in rendered
    assert "sorry" not in rendered


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
    assert "mumei_arith" in rendered
    assert "sorry" not in rendered
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


def test_render_theorem_lowers_unknown_obligation_as_manual():
    cert = _make_certificate(
        "math.mm",
        [
            _make_atom(
                "unknown_guard",
                requires="unknown_obligation(x)",
                ensures="result >= 0",
            )
        ],
    )
    [atom] = collect_unknown_atoms(cert)
    rendered = render_theorem(atom)

    assert "MumeiLean.AdvancedPatterns.mumei_unknown_obligation x" in rendered
    assert "manual_lemma_reason=unknown_obligation_requires_manual_lemma" in rendered
    assert "unknown_obligation_lowering" in str(atom.translator_ir)


def test_collect_unknown_atoms_prioritizes_sc_and_rtgs_domains():
    cert = _make_certificate(
        "settlement.mm",
        [
            _make_atom(
                "withdraw_preserves_other_balance",
                requires="balance >= amount",
                ensures="result >= 0",
            ),
            _make_atom(
                "trace_balance_conservation",
                requires="rtgs_validated(state)",
                ensures="rtgs_settled(next_state)",
            ),
        ],
    )
    atoms = collect_unknown_atoms(cert)

    assert atoms[0].unknown_obligation_domain == "smart_contract"
    assert atoms[0].escalation_reason == "sc"
    assert "smart_contract_lowering" in atoms[0].translator_ir["lowering_rules"]
    assert atoms[1].unknown_obligation_domain == "rtgs"
    assert atoms[1].escalation_reason == "rtgs"
    assert "rtgs_settlement_lowering" in atoms[1].translator_ir["lowering_rules"]


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
