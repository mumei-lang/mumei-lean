"""Unit tests for ``scripts.expr_translator``."""
from __future__ import annotations

from expr_translator import contains_identifier, translate_contract


def test_trivial_contract_is_true():
    result = translate_contract("")
    assert result.lean_expr == "True"
    assert result.is_trivial is True
    assert result.is_partial is False
    assert result.identifiers == []

    result_true = translate_contract("true")
    assert result_true.lean_expr == "True"
    assert result_true.is_trivial is True


def test_simple_arithmetic_comparison():
    result = translate_contract("x > 0")
    assert result.lean_expr == "x > 0"
    assert result.identifiers == ["x"]
    assert result.is_partial is False


def test_logical_and_and_or_translate_to_unicode():
    result = translate_contract("x > 0 && y < 10")
    assert "∧" in result.lean_expr
    assert result.identifiers == ["x", "y"]

    result_or = translate_contract("x == 0 || y != 0")
    assert "∨" in result_or.lean_expr
    assert "=" in result_or.lean_expr
    assert "≠" in result_or.lean_expr


def test_result_is_reserved_and_not_listed_as_free_identifier():
    result = translate_contract("result >= x")
    assert "result" not in result.identifiers
    assert "x" in result.identifiers


def test_unknown_token_marks_partial():
    # Square brackets are outside the v1 surface and trigger UNK tokens.
    result = translate_contract("arr[0] > 0")
    assert result.is_partial is True


def test_geq_and_leq_become_unicode():
    result_geq = translate_contract("x >= 0")
    assert "≥" in result_geq.lean_expr
    result_leq = translate_contract("x <= 10")
    assert "≤" in result_leq.lean_expr


def test_negation_is_translated():
    result = translate_contract("!flag")
    assert result.lean_expr.startswith("¬")
    assert result.identifiers == ["flag"]


def test_contains_identifier_respects_token_boundaries():
    # Exact match — both whitespace-delimited and operator-adjacent.
    assert contains_identifier("result >= x", "result") is True
    assert contains_identifier("result>=x", "result") is True
    assert contains_identifier("x + result", "result") is True

    # Substring matches must NOT trigger.
    assert contains_identifier("results >= 0", "result") is False
    assert contains_identifier("no_result > 0", "result") is False
    assert contains_identifier("result_count == 1", "result") is False

    # Empty / missing input.
    assert contains_identifier("", "result") is False
    assert contains_identifier("x > 0", "") is False
