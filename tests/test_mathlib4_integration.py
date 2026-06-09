"""Focused tests for the mathlib4 integration prototype."""
from __future__ import annotations

from expr_translator import (
    translate_bounded_quantifier_to_finset,
    translate_contract,
    translate_finite_field,
    translate_group_theory,
)


def test_finset_bounded_forall_prototype_records_bridge_metadata():
    result = translate_bounded_quantifier_to_finset(
        "forall",
        "i",
        "0",
        "n",
        "arr[i] >= 0",
    )

    assert result is not None
    assert result.lean_expr == (
        "(∀ iNat ∈ Finset.Ico (0 : Int).toNat n.toNat, "
        "let i : Int := Int.ofNat iNat; arr.get! i.toNat ≥ 0)"
    )
    assert result.identifiers == ["n", "arr"]
    assert result.array_identifiers == ["arr"]
    assert result.translator_ir is not None
    assert "mathlib4_bridge" in result.translator_ir.lowering_rules
    assert "finset_bounded_quantifier_lowering" in result.translator_ir.lowering_rules
    assert result.translator_ir.requires_bridge_lemmas == [
        "mumei_finset_bounded_quantifier_bridge"
    ]


def test_finset_bounded_exists_prototype_preserves_body_translation():
    result = translate_bounded_quantifier_to_finset(
        "exists",
        "j",
        "lo",
        "hi",
        "ff_in_field(ff_mul(j, x, p), p)",
    )

    assert result is not None
    assert result.lean_expr.startswith("(∃ jNat ∈ Finset.Ico lo.toNat hi.toNat")
    assert "let j : Int := Int.ofNat jNat" in result.lean_expr
    assert "(MumeiLean.Algebra.mumei_ff_mul j x p)" in result.lean_expr
    assert result.identifiers == ["lo", "hi", "x", "p"]


def test_finite_field_add_mul_prototype_uses_algebra_bridge():
    assert translate_finite_field("ff_add", ["a", "b", "p"]) == "((a + b) % p)"
    assert translate_finite_field("ff_mul", ["a", "b", "p"]) == (
        "(MumeiLean.Algebra.mumei_ff_mul a b p)"
    )

    result = translate_contract("ff_eq(ff_add(a, b, p), ff_mul(c, d, p), p)")
    assert "((a + b) % p)" in result.lean_expr
    assert "(MumeiLean.Algebra.mumei_ff_mul c d p)" in result.lean_expr
    assert result.translator_ir is not None
    assert "finite_field_lowering" in result.translator_ir.lowering_rules
    assert "mathlib4_bridge" in result.translator_ir.lowering_rules


def test_group_identity_inverse_prototype_uses_algebra_bridge():
    assert translate_group_theory("group_identity", []) == (
        "(MumeiLean.Algebra.mumei_group_identity)"
    )
    assert translate_group_theory("group_inv", ["g"]) == (
        "(MumeiLean.Algebra.mumei_group_inv g)"
    )

    result = translate_contract(
        "group_mul(group_inv(g), g) == group_identity()"
    )
    assert "(MumeiLean.Algebra.mumei_group_inv g)" in result.lean_expr
    assert "(MumeiLean.Algebra.mumei_group_identity)" in result.lean_expr
    assert result.translator_ir is not None
    assert "group_theory_lowering" in result.translator_ir.lowering_rules
    assert "mathlib4_bridge" in result.translator_ir.lowering_rules
