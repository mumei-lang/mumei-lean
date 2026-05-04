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
    # ``@`` is outside the v1 surface and triggers an UNK token.
    result = translate_contract("x @ 0")
    assert result.is_partial is True


def test_array_access():
    # PR 4: arr[i] becomes ``arr.get! i.toNat`` (List.get! takes Nat;
    # ``i`` is bound as Int by the surrounding contract).
    result = translate_contract("arr[i] >= 0")
    assert "arr.get! i.toNat ≥ 0" in result.lean_expr, result.lean_expr
    # Both `arr` and `i` are free identifiers at this level.
    assert "arr" in result.identifiers
    assert "i" in result.identifiers
    # ``arr`` appears in array-access position, so it must be reported
    # separately so the renderer can type it ``List Int``.
    assert result.array_identifiers == ["arr"]
    assert result.is_partial is False


def test_result_array_access_marks_partial():
    # ``result`` is reserved (bound separately as the return value) and
    # cannot be re-typed as ``List Int``. If it appears in ``arr[i]``
    # position, we must flag the contract as partial rather than emit
    # ``result.get! i`` with a scalar ``result : Int`` binding.
    result = translate_contract("forall(i, 0, n, result[i] >= 0)")
    assert result.is_partial is True
    assert "result" not in result.array_identifiers


def test_forall_bound_name_reused_as_free_marks_partial():
    # Sharing a name between a forall binder and a free occurrence
    # outside the forall scope is ambiguous — flag as partial rather
    # than silently drop the free use (which would produce Lean that
    # references an undeclared identifier).
    result = translate_contract("i > 0 && forall(i, 0, n, arr[i] >= 0)")
    assert result.is_partial is True


def test_bare_comma_outside_forall_marks_partial():
    # The tokenizer accepts ``,`` for forall's sake, but a stray comma
    # outside any ``forall(..)`` / ``arr[..]`` is still outside the v1
    # surface and must be flagged so the generated theorem carries the
    # ``-- TODO: unproven`` marker.
    result = translate_contract("f(a, b)")
    assert result.is_partial is True


def test_array_access_with_arithmetic_index():
    # arr[i + 1] must produce ``arr.get! (i + 1).toNat`` — NOT
    # ``arr.get! i + 1``. ``List.get!`` takes ``Nat``, so the
    # compound expression needs both the outer parens (to bind the
    # whole sum) and a ``.toNat`` conversion at the end.
    result = translate_contract("arr[i + 1] > 0")
    assert "arr.get! (i + 1).toNat" in result.lean_expr, result.lean_expr
    # Defensive: the un-parenthesised / un-coerced forms are known
    # footguns and must not slip through.
    assert "arr.get! i + 1" not in result.lean_expr, result.lean_expr
    assert "arr.get! (i + 1) " not in result.lean_expr, result.lean_expr
    assert result.is_partial is False


def test_forall_basic():
    # PR 4: forall(i, 0, n, arr[i] >= 0) →
    #   (∀ i : Int, 0 ≤ i → i < n → arr.get! i.toNat ≥ 0)
    result = translate_contract("forall(i, 0, n, arr[i] >= 0)")
    assert "∀ i : Int" in result.lean_expr
    assert "0 ≤ i" in result.lean_expr
    assert "i < n" in result.lean_expr
    assert "arr.get! i.toNat ≥ 0" in result.lean_expr, result.lean_expr
    # The bound variable `i` must NOT appear as a free identifier.
    assert "i" not in result.identifiers
    # The non-bound names should still be free.
    assert "arr" in result.identifiers
    assert "n" in result.identifiers
    assert result.is_partial is False


def test_forall_with_logical_connective():
    # forall composed under && should still translate cleanly.
    result = translate_contract("n >= 0 && forall(i, 0, n, arr[i] >= 0)")
    assert "∧" in result.lean_expr
    assert "∀ i : Int" in result.lean_expr
    assert "n" in result.identifiers
    assert "arr" in result.identifiers
    assert "i" not in result.identifiers
    assert result.is_partial is False


def test_forall_arity_mismatch_marks_partial():
    # `forall` with the wrong number of args is partial, not a crash.
    result = translate_contract("forall(i, n)")
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


def test_len_translation():
    # v3: len(arr) >= n → (mumei_len arr) ≥ n. ``len`` is not bound as a
    # free identifier, and ``arr`` remains scalar so mumei certificates can
    # pass an explicit length parameter.
    result = translate_contract("len(arr) >= n")
    assert "(mumei_len arr)" in result.lean_expr, result.lean_expr
    assert "len" not in result.identifiers
    assert "arr" in result.identifiers
    assert "n" in result.identifiers
    assert result.array_identifiers == []
    assert result.is_partial is False


def test_len_function_call():
    result = translate_contract("len(arr) >= n")
    assert "(mumei_len arr)" in result.lean_expr or "mumei_len" in result.lean_expr
    assert result.is_partial is False


def test_abs_function_call():
    result = translate_contract("abs(x) >= 0")
    assert "mumei_abs" in result.lean_expr
    assert result.is_partial is False


def test_min_max_function_call():
    result = translate_contract("min(a, b) <= a")
    assert "(min a b)" in result.lean_expr
    assert result.is_partial is False

    result_max = translate_contract("max(a, b) >= a")
    assert "(max a b)" in result_max.lean_expr
    assert result_max.is_partial is False


def test_old_function_call_lowers_to_old_identifier():
    result = translate_contract("old(balance) >= balance")
    assert "old_balance ≥ balance" in result.lean_expr, result.lean_expr
    assert "old_balance" in result.identifiers
    assert "balance" in result.identifiers
    assert result.is_partial is False


def test_starts_with_function_call():
    result = translate_contract('starts_with(url, "https://")')
    assert result.lean_expr == '(mumei_starts_with url "https://")'
    assert result.identifiers == ["url"]
    assert result.string_identifiers == ["url"]
    assert result.is_partial is False


def test_ends_with_function_call():
    result = translate_contract('ends_with(path, ".json")')
    assert result.lean_expr == '(mumei_ends_with path ".json")'
    assert result.identifiers == ["path"]
    assert result.string_identifiers == ["path"]
    assert result.is_partial is False


def test_if_then_else_expression():
    result = translate_contract("if x > 0 then x else 0")
    assert result.lean_expr == "if x > 0 then x else 0"
    assert result.identifiers == ["x"]
    assert result.is_partial is False


def test_new_constructs_compose_without_partial_marker():
    result = translate_contract(
        'old(balance) >= amount && starts_with(url, "https://")'
    )
    assert 'old_balance ≥ amount' in result.lean_expr, result.lean_expr
    assert '∧' in result.lean_expr
    assert '(mumei_starts_with url "https://")' in result.lean_expr
    assert result.identifiers == ["old_balance", "amount", "url"]
    assert result.string_identifiers == ["url"]
    assert result.is_partial is False


def test_unknown_function_remains_partial():
    result = translate_contract("custom_fn(x, y) > 0")
    assert result.is_partial is True


def test_result_equals_expr():
    result = translate_contract("result == x + 1")
    assert "result = x + 1" in result.lean_expr
    assert result.is_partial is False


def test_nested_forall():
    # forall inside forall over a 2-D array: every inner ``forall``
    # body still translates cleanly, the inner bound variable does not
    # leak as a free identifier, and ``arr`` remains a single array
    # identifier (not duplicated).
    src = "forall(i, 0, n, forall(j, 0, n, arr[i] >= 0))"
    result = translate_contract(src)
    # Two ``∀`` quantifiers, both bound to ``Int``.
    assert result.lean_expr.count("∀ ") == 2
    assert "∀ i : Int" in result.lean_expr
    assert "∀ j : Int" in result.lean_expr
    assert "arr.get! i.toNat ≥ 0" in result.lean_expr
    # Bound variables are not free.
    assert "i" not in result.identifiers
    assert "j" not in result.identifiers
    assert "arr" in result.identifiers
    assert "n" in result.identifiers
    assert result.array_identifiers == ["arr"]
    assert result.is_partial is False


def test_unknown_function_call_is_partial():
    # Generic function calls are emitted verbatim but must mark the
    # contract as partial so the generated theorem carries a
    # ``-- TODO: unproven`` triage marker.
    result = translate_contract("custom_fn(x)")
    assert result.is_partial is True
    assert "custom_fn" in result.lean_expr


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
