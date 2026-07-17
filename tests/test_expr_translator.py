"""Unit tests for ``scripts.expr_translator``."""
from __future__ import annotations

import expr_translator
from expr_translator import (
    OBLIGATION_CLASS_ARITHMETIC,
    OBLIGATION_CLASS_CRYPTO,
    OBLIGATION_CLASS_FINITE_FIELD,
    OBLIGATION_CLASS_GROUP_THEORY,
    OBLIGATION_CLASS_QUANTIFIER,
    OBLIGATION_CLASS_RTGS,
    OBLIGATION_CLASS_SMART_CONTRACT,
    OBLIGATION_CLASS_SMART_CONTRACT_GUARD_TRACE,
    OBLIGATION_CLASS_UNKNOWN,
    TranslatorIR,
    TranslatorIRBinder,
    classify_obligation,
    contains_identifier,
    guard_trace_expected_to_lean,
    obligation_bridge_lemmas,
    normalize_guard_trace_translator_ir,
    render_guard_trace_theorem,
    translate_body,
    translate_contract,
    translate_finite_field,
    translate_group_theory,
    translate_quantifier,
    validate_translator_ir_compliance,
)


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


def test_unbounded_forall_colon_form():
    result = translate_contract("forall x: x >= 0")
    assert result.lean_expr == "(∀ x : Int, x ≥ 0)"
    assert result.identifiers == []
    assert result.is_partial is False


def test_unbounded_exists_colon_form():
    result = translate_contract("exists x: x == 0")
    assert result.lean_expr == "(∃ x : Int, x = 0)"
    assert result.identifiers == []
    assert result.is_partial is False


def test_quantifier_accepts_explicit_string_type():
    result = translate_contract('forall name : String: starts_with(name, "A")')
    assert result.lean_expr == '(∀ name : String, (mumei_starts_with name "A"))'
    assert result.identifiers == []
    assert result.string_identifiers == []
    assert result.is_partial is False


def test_nested_unbounded_quantifiers():
    result = translate_contract("forall i: forall j: i < j")
    assert result.lean_expr == "(∀ i : Int, (∀ j : Int, i < j))"
    assert result.identifiers == []
    assert result.is_partial is False


def test_nested_unbounded_quantifiers_comma_form():
    result = translate_contract("forall x, exists y, P(x, y)")
    assert result.lean_expr == "(∀ x : Int, (∃ y : Int, (P x y)))"
    assert result.identifiers == ["P"]
    assert result.predicate_identifiers == ["P"]
    assert result.predicate_arities == {"P": 2}
    assert result.is_partial is False


def test_nested_unbounded_quantifiers_typed_comma_form():
    result = translate_contract("forall x : T, forall y : T, P(x, y)")
    assert result.lean_expr == "(∀ x : Int, (∀ y : Int, (P x y)))"
    assert result.identifiers == ["P"]
    assert result.is_partial is False


def test_translate_quantifier_public_entrypoint_handles_nested_exists():
    result = translate_quantifier("forall i: exists(j, 0, n, j >= i)")
    assert result.lean_expr == "(∀ i : Int, (∃ j : Int, 0 ≤ j ∧ j < n ∧ j ≥ i))"
    assert result.identifiers == ["n"]
    assert result.is_partial is False


def test_unbounded_quantifier_with_logical_connective():
    result = translate_contract("forall x: x >= 0 && x < n")
    assert result.lean_expr == "(∀ x : Int, x ≥ 0 ∧ x < n)"
    assert result.identifiers == ["n"]
    assert result.is_partial is False


def test_stray_colon_marks_partial():
    result = translate_contract("x : 5")
    assert result.is_partial is True


def test_unbounded_quantifier_requires_immediate_colon():
    result = translate_contract("forall x exists y: y > x")
    assert result.is_partial is True
    assert result.lean_expr != "(∀ x : Int, y > x)"

    malformed = translate_contract("forall x + y: y > 0")
    assert malformed.is_partial is True
    assert "y" in malformed.identifiers


def test_exists_call_form():
    result = translate_contract("exists(x, x == 0)")
    assert result.lean_expr == "(∃ x : Int, x = 0)"
    assert result.identifiers == []
    assert result.is_partial is False


def test_exists_call_form_with_type_annotation():
    result = translate_contract('exists(name: String, starts_with(name, "M"))')
    assert result.lean_expr == '(∃ name : String, (mumei_starts_with name "M"))'
    assert result.identifiers == []
    assert result.string_identifiers == []
    assert result.is_partial is False


def test_bounded_forall_in_range_form():
    result = translate_contract("forall(x in 0..n, P(x))")
    assert result.lean_expr == "(∀ x : Int, 0 ≤ x → x < n → (P x))"
    assert result.identifiers == ["n", "P"]
    assert result.predicate_identifiers == ["P"]
    assert result.predicate_arities == {"P": 1}
    assert result.is_partial is False


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


def test_old_does_not_trigger_scalar_type_conflicts():
    result = translate_contract("old(arr) >= 0 && arr[0] >= 0")
    assert "old_arr ≥ 0" in result.lean_expr, result.lean_expr
    assert "arr.get! 0" in result.lean_expr
    assert result.array_identifiers == ["arr"]
    assert result.is_partial is False

    string_result = translate_contract('old(name) >= 0 && starts_with(name, "Mr")')
    assert "old_name ≥ 0" in string_result.lean_expr, string_result.lean_expr
    assert '(mumei_starts_with name "Mr")' in string_result.lean_expr
    assert string_result.string_identifiers == ["name"]
    assert string_result.is_partial is False


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


def test_contains_function_call():
    result = translate_contract('contains(s, "hello")')
    assert result.lean_expr == '(mumei_contains s "hello")'
    assert result.identifiers == ["s"]
    assert result.string_identifiers == ["s"]
    assert result.is_partial is False


def test_not_contains_function_call():
    result = translate_contract('not_contains(path, "..")')
    assert result.lean_expr == '(mumei_not_contains path "..")'
    assert result.is_partial is False


def test_not_contains_string_identifiers():
    result = translate_contract('not_contains(path, "..")')
    assert "path" in result.string_identifiers


def test_sum_function_call():
    result = translate_contract("sum(arr, n)")
    assert result.lean_expr == "(mumei_sum arr n)"
    assert result.identifiers == ["arr", "n"]
    # ``arr`` is the ``List Int`` first argument of ``mumei_sum`` and
    # must be reported as an array identifier so the renderer types it
    # as ``List Int`` rather than the scalar-``Int`` default.
    assert result.array_identifiers == ["arr"]
    assert result.is_partial is False


def test_count_function_call():
    result = translate_contract("count(arr, 0)")
    assert result.lean_expr == "(mumei_count arr 0)"
    assert result.identifiers == ["arr"]
    assert result.array_identifiers == ["arr"]
    assert result.is_partial is False


def test_crypto_function_calls():
    result = translate_contract("mod(pow(signature, public_key), n) == message")
    assert (
        "(MumeiLean.CryptoHelpers.mumei_mod "
        "(MumeiLean.CryptoHelpers.mumei_pow signature public_key) n)"
        in result.lean_expr
    )
    assert "message" in result.identifiers
    assert result.is_partial is False

    phi_result = translate_contract("phi(n) > 0")
    assert phi_result.lean_expr == "(MumeiLean.CryptoHelpers.mumei_phi n) > 0"
    assert phi_result.identifiers == ["n"]
    assert phi_result.is_partial is False


def test_algebra_function_calls_lower_to_mumei_lean_algebra():
    result = translate_contract("ff_add(x, y, p) == z && group_identity() == e")
    assert "((x + y) % p) = z" in result.lean_expr
    assert "(MumeiLean.Algebra.mumei_group_identity) = e" in result.lean_expr
    assert result.identifiers == ["x", "y", "p", "z", "e"]
    assert result.is_partial is False

    prime_result = translate_contract("is_prime(p) && mod_eq(x, y, p)")
    assert "(MumeiLean.Algebra.mumei_is_prime p)" in prime_result.lean_expr
    assert "(MumeiLean.Algebra.mumei_mod_eq x y p)" in prime_result.lean_expr
    assert prime_result.is_partial is False


def test_finite_field_and_group_public_lowering_helpers():
    assert translate_finite_field("ff_in_field", ["x", "p"]) == "(0 ≤ x ∧ x < p)"
    assert translate_finite_field("ff_add", ["a", "b", "p"]) == "((a + b) % p)"
    assert translate_finite_field("ff_mul", ["a", "b", "p"]) == (
        "(MumeiLean.Algebra.mumei_ff_mul a b p)"
    )
    assert translate_group_theory("group_inv", ["g"]) == (
        "(MumeiLean.Algebra.mumei_group_inv g)"
    )
    assert translate_finite_field("ff_mul", ["a", "b"]) is None
    assert translate_group_theory("ff_mul", ["a", "b", "p"]) is None


def test_crypto_primitive_calls_lower_to_mumei_lean_crypto():
    result = translate_contract(
        "decrypt(encrypt(message, key, nonce), key, nonce) == message && "
        "signature_verify(signature, message, public_key, n)"
    )
    assert "(MumeiLean.Crypto.encrypt message key nonce)" in result.lean_expr
    assert (
        "(MumeiLean.Crypto.decrypt "
        "(MumeiLean.Crypto.encrypt message key nonce) key nonce)"
        in result.lean_expr
    )
    assert "(MumeiLean.Crypto.signature_verify signature message public_key n)" in result.lean_expr
    assert result.identifiers == ["message", "key", "nonce", "signature", "public_key", "n"]
    assert result.is_partial is False
    assert result.translator_ir is not None
    assert "crypto_primitive_lowering" in result.translator_ir.lowering_rules
    assert "mumei_crypto_primitive_bridge" in result.translator_ir.requires_bridge_lemmas


def test_higher_order_predicate_call_types_predicate_binder():
    result = translate_contract("forall(x, 0, n, holds(P, x))")
    assert result.lean_expr == "(∀ x : Int, 0 ≤ x → x < n → (P x))"
    assert result.identifiers == ["n", "P"]
    assert result.predicate_identifiers == ["P"]
    assert result.is_partial is False
    assert result.translator_ir is not None
    binder_payload = result.translator_ir.to_dict()["binders"]
    assert {
        "mumei_name": "P",
        "lean_name": "P",
        "mumei_type": "predicate<i64>",
        "lean_type": "Int → Prop",
        "role": "free",
    } in binder_payload
    assert "higher_order_predicate_lowering" in result.translator_ir.lowering_rules


def test_sc_and_rtgs_calls_record_domain_lowering():
    sc = translate_contract("sc_withdraw_allowed(balance, amount)")
    assert (
        sc.lean_expr
        == "(MumeiLean.AdvancedPatterns.sc_withdraw_allowed balance amount)"
    )
    assert sc.is_partial is False
    assert sc.translator_ir is not None
    assert "smart_contract_lowering" in sc.translator_ir.lowering_rules
    assert "mumei_smart_contract_bridge" in sc.translator_ir.requires_bridge_lemmas

    rtgs = translate_contract(
        "rtgs_balance_conserved(before, debit, credit, after)"
    )
    assert (
        rtgs.lean_expr
        == "(MumeiLean.AdvancedPatterns.rtgs_balance_conserved "
        "before debit credit after)"
    )
    assert rtgs.is_partial is False
    assert rtgs.translator_ir is not None
    assert "rtgs_settlement_lowering" in rtgs.translator_ir.lowering_rules
    assert "mumei_rtgs_settlement_bridge" in rtgs.translator_ir.requires_bridge_lemmas


def test_guard_trace_lowering_normalizes_expected_outcome_and_classification():
    translator_ir = normalize_guard_trace_translator_ir(
        {
            "sort": "contract_obligation",
            "binders": [],
            "theorem_goal": "",
            "provenance_span": {"file": "", "line": 0, "col": 0, "len": 0},
            "lowering_rules": [],
            "guard_trace": {
                "ops": ["lock", "externalCall", "unlock"],
                "expected_outcome": "safe",
            },
        }
    )

    assert translator_ir["obligation_class"] == (
        OBLIGATION_CLASS_SMART_CONTRACT_GUARD_TRACE
    )
    assert (
        translator_ir["theorem_goal"]
        == "runGuard GuardState.Unlocked [GuardOp.lock, GuardOp.externalCall, "
        "GuardOp.unlock] = some GuardState.Unlocked"
    )
    assert "smart_contract_guard_trace_lowering" in translator_ir["lowering_rules"]
    assert (
        "MumeiLean.SmartContract.no_external_call_without_lock"
        in translator_ir["requires_bridge_lemmas"]
    )
    assert classify_obligation([], translator_ir["lowering_rules"]) == (
        OBLIGATION_CLASS_SMART_CONTRACT_GUARD_TRACE
    )
    assert guard_trace_expected_to_lean(True) == "some GuardState.Unlocked"
    assert guard_trace_expected_to_lean("unsafe") == "none"
    rendered = render_guard_trace_theorem(
        "guarded_reentrancy_trace",
        translator_ir["guard_trace"],
    )
    assert "theorem guarded_reentrancy_trace_correct" in rendered
    assert "runGuard GuardState.Unlocked" in rendered
    assert "by" in rendered
    assert "decide" in rendered


def test_translator_ir_serializes_guard_trace_metadata():
    ir = TranslatorIR(
        sort="contract_obligation",
        binders=[TranslatorIRBinder("lock", "lock", "i64", "Int")],
        theorem_goal="runGuard GuardState.Unlocked [GuardOp.lock] = none",
        guard_trace_ops=["lock"],
        guard_trace_expected_outcome="none",
    )

    payload = ir.to_dict()

    assert payload["guard_trace_ops"] == ["lock"]
    assert payload["guard_trace_expected_outcome"] == "none"


def test_normalize_guard_trace_translator_ir_without_expected_outcome_is_unchanged():
    translator_ir = {
        "sort": "contract_obligation",
        "guard_trace": {"ops": ["lock", "externalCall", "unlock"]},
        "lowering_rules": ["smart_contract_guard_trace_lowering"],
    }

    normalized = normalize_guard_trace_translator_ir(translator_ir)

    assert normalized is translator_ir
    assert "obligation_class" not in normalized
    assert "theorem_goal" not in normalized
    assert "guard_trace_expected_outcome" not in normalized


def test_nested_quantifier_with_finite_field_and_group_metadata():
    result = translate_contract(
        "forall(x, 0, p, exists(y, 0, p, ff_in_field(ff_add(x, y, p), p) && "
        "group_mul(group_inv(g), g) == group_identity()))"
    )
    assert "∀ x : Int" in result.lean_expr
    assert "∃ y : Int" in result.lean_expr
    assert "0 ≤ ((x + y) % p) ∧ ((x + y) % p) < p" in result.lean_expr
    assert "(MumeiLean.Algebra.mumei_group_mul (MumeiLean.Algebra.mumei_group_inv g) g)" in result.lean_expr
    assert "(MumeiLean.Algebra.mumei_group_identity)" in result.lean_expr
    assert result.identifiers == ["p", "g"]
    assert result.is_partial is False
    assert result.translator_ir is not None
    assert "finite_field_lowering" in result.translator_ir.lowering_rules
    assert "group_theory_lowering" in result.translator_ir.lowering_rules
    assert "mumei_finite_field_bridge" in result.translator_ir.requires_bridge_lemmas
    assert "mumei_group_theory_bridge" in result.translator_ir.requires_bridge_lemmas


def test_if_then_else_expression():
    result = translate_contract("if x > 0 then x else 0")
    assert result.lean_expr == "if x > 0 then x else 0"
    assert result.identifiers == ["x"]
    assert result.is_partial is False


def test_translate_body_handles_conditionals_and_arithmetic():
    result = translate_body("if x >= 0 then x else -x")
    assert result.lean_expr == "if x ≥ 0 then x else - x"
    assert result.identifiers == ["x"]
    assert result.is_partial is False


def test_translate_body_handles_mumei_braced_if_else():
    result = translate_body("if left == right { 1 } else { 0 }")
    assert result.lean_expr == "if left = right then 1 else 0"
    assert result.identifiers == ["left", "right"]
    assert result.is_partial is False


def test_translate_body_handles_list_string_and_quantifier_expressions():
    list_result = translate_body("[x, y, 3]")
    assert list_result.lean_expr == "[x, y, 3]"
    assert list_result.identifiers == ["x", "y"]
    assert list_result.is_partial is False

    string_result = translate_body('"ok"')
    assert string_result.lean_expr == '"ok"'
    assert string_result.identifiers == []
    assert string_result.is_partial is False

    quantifier_result = translate_body("forall(i, 0, n, arr[i] >= 0)")
    assert "∀ i : Int" in quantifier_result.lean_expr
    assert "arr.get! i.toNat ≥ 0" in quantifier_result.lean_expr
    assert quantifier_result.identifiers == ["n", "arr"]
    assert quantifier_result.array_identifiers == ["arr"]
    assert quantifier_result.is_partial is False


def test_translate_body_handles_saturating_abs_pattern():
    result = translate_body(
        "if x == (0 - 9223372036854775807 - 1) then 9223372036854775807 "
        "else if x >= 0 then x else 0 - x"
    )
    assert result.lean_expr == (
        "if x = ( 0 - 9223372036854775807 - 1 ) then 9223372036854775807 "
        "else if x ≥ 0 then x else 0 - x"
    )
    assert result.identifiers == ["x"]
    assert result.is_partial is False


def test_translate_body_handles_saturating_lower_bound_pattern():
    result = translate_body("if x < MIN then MIN else x")
    assert result.lean_expr == "if x < MIN then MIN else x"
    assert result.identifiers == ["x", "MIN"]
    assert result.is_partial is False


def test_translate_body_handles_match_expression():
    result = translate_body("match x { 0 => 0, 1 => 1, _ => x + 1 }")
    assert result.lean_expr == "(match x with | 0 => 0 | 1 => 1 | _ => x + 1)"
    assert result.identifiers == ["x"]
    assert result.is_partial is False


def test_translate_contract_handles_match_expression():
    result = translate_contract("match x { 0 => 1, 1 => 2, _ => 0 }")
    assert result.lean_expr == "(match x with | 0 => 1 | 1 => 2 | _ => 0)"
    assert result.identifiers == ["x"]
    assert result.is_partial is False


def test_forall_with_nested_match_expression():
    result = translate_contract(
        "forall(i, 0, n, match arr[i] { 0 => true, _ => false })"
    )
    assert "∀ i : Int" in result.lean_expr
    assert "match arr.get! i.toNat with | 0 => True | _ => False" in result.lean_expr
    assert result.identifiers == ["n", "arr"]
    assert result.array_identifiers == ["arr"]
    assert result.is_partial is False


def test_translate_body_handles_if_else_match_expression():
    result = translate_body("if x > 0 then x else match y { 0 => 0, _ => y }")
    assert (
        result.lean_expr
        == "if x > 0 then x else (match y with | 0 => 0 | _ => y)"
    )
    assert result.identifiers == ["x", "y"]
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


def test_string_identifier_used_in_scalar_call_marks_partial():
    result = translate_contract('len(name) >= 3 && starts_with(name, "Mr")')
    assert result.is_partial is True
    assert result.string_identifiers == ["name"]


def test_embedded_if_then_else_marks_partial_when_tail_is_ambiguous():
    result = translate_contract("a > 0 && if x > 0 then x else 0 && b > 0")
    assert result.is_partial is True


def test_if_then_else_allows_non_operator_else_tail():
    result = translate_contract("if x > 0 then x else y + 1")
    assert result.lean_expr == "if x > 0 then x else y + 1"
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


def test_translator_ir_compliance_accepts_formal_spec_mappings():
    result = translate_contract("forall(i, 0, n, arr[i] >= 0)")
    assert result.translator_ir is not None
    assert validate_translator_ir_compliance(result.translator_ir) == []
    assert "array_bounds_bridge" in result.translator_ir.lowering_rules
    assert "refinement_predicate_lowering" in result.translator_ir.lowering_rules
    assert "mumei_array_bounds_bridge" in result.translator_ir.requires_bridge_lemmas
    assert "mumei_array_get_bridge" in result.translator_ir.requires_bridge_lemmas
    assert any(
        note.startswith("array_bounds_bridge:")
        for note in result.translator_ir.semantic_gap_notes
    )
    assert any(
        hint.startswith("preserve i < arr.length")
        for hint in result.translator_ir.proof_trace_hints
    )


def test_translator_ir_semantic_gap_metadata_serializes_when_present():
    result = translate_contract("result == x * y && contains(s, \"needle\")")
    assert result.translator_ir is not None

    payload = result.translator_ir.to_dict()

    assert "integer_overflow_bridge" in payload["lowering_rules"]
    assert "string_regex_bridge" in payload["lowering_rules"]
    assert "semantic_gap_notes" in payload
    assert "proof_trace_hints" in payload
    bridge = payload["requires_bridge_lemmas"]
    assert "mumei_i64_overflow_bridge" in bridge
    assert "mumei_regex_bridge" in bridge


def test_translator_ir_regex_manual_lemma_requires_string_bridge():
    result = translate_contract("regex(s, \"needle\")")
    assert result.translator_ir is not None
    assert result.is_partial is True
    assert "string_regex_bridge" in result.translator_ir.lowering_rules
    assert "mumei_regex_bridge" in result.translator_ir.requires_bridge_lemmas
    assert any(
        note.startswith("string_regex_bridge:")
        for note in result.translator_ir.semantic_gap_notes
    )


def test_translator_ir_compliance_warns_on_spec_drift():
    ir = TranslatorIR(
        sort="contract_obligation",
        binders=[TranslatorIRBinder("x", "x", "decimal", "Decimal")],
        theorem_goal="x > 0",
        lowering_rules=["undocumented_rule"],
    )

    issues = validate_translator_ir_compliance(ir)

    assert len(issues) == 2
    assert any("undocumented_rule" in issue for issue in issues)
    assert any("decimal -> Decimal" in issue for issue in issues)


def test_translate_contract_prints_compliance_warnings(monkeypatch, capsys):
    def fake_validate_translator_ir_compliance(_translator_ir):
        return ["synthetic spec drift"]

    monkeypatch.setattr(
        expr_translator,
        "validate_translator_ir_compliance",
        fake_validate_translator_ir_compliance,
    )

    expr_translator.translate_contract("x > 0")

    assert (
        "TranslatorIR compliance warning: synthetic spec drift"
        in capsys.readouterr().out
    )


# ==== Advanced Contract Translation Tests ====


def test_implication_operator_translates_to_arrow():
    result = translate_contract("x > 0 ==> y > 0")
    assert "→" in result.lean_expr
    assert result.identifiers == ["x", "y"]
    assert result.is_partial is False


def test_implies_function_translates_to_arrow():
    result = translate_contract("implies(x > 0, y > 0)")
    assert "→" in result.lean_expr
    assert result.identifiers == ["x", "y"]
    assert result.is_partial is False


def test_let_binding_basic():
    result = translate_contract("let x = 5 in x > 0")
    assert "let x := 5" in result.lean_expr
    assert result.is_partial is False


def test_let_binding_with_complex_expr():
    result = translate_contract("let y = a + b in y > 0")
    assert "let y := a + b" in result.lean_expr
    assert result.is_partial is False


def test_let_binding_marks_partial_when_malformed():
    result = translate_contract("let x")
    assert result.is_partial is True


def test_new_crypto_functions_kdf():
    result = translate_contract("kdf(key, info, 32) > 0")
    assert "(MumeiLean.Crypto.kdf key info 32)" in result.lean_expr
    assert result.is_partial is False


def test_new_crypto_functions_hmac():
    result = translate_contract("hmac(key, message) > 0")
    assert "(MumeiLean.Crypto.hmac key message)" in result.lean_expr
    assert result.is_partial is False


def test_new_crypto_functions_commitment_hash():
    result = translate_contract("commitment_hash(value, randomness) > 0")
    assert "(MumeiLean.Crypto.commitment_hash value randomness)" in result.lean_expr
    assert result.is_partial is False


def test_new_crypto_functions_zk_verify():
    result = translate_contract("zk_verify(proof, public_input, circuit)")
    assert "(MumeiLean.Crypto.zk_verify proof public_input circuit)" in result.lean_expr
    assert result.is_partial is False


def test_new_algebra_functions_ff_zero_and_ff_one():
    result = translate_contract("ff_zero(p) == 0 && ff_one(p) == 1")
    assert "(MumeiLean.Algebra.mumei_ff_zero p) = 0" in result.lean_expr
    assert "(MumeiLean.Algebra.mumei_ff_one p) = 1" in result.lean_expr
    assert result.is_partial is False


def test_new_algebra_functions_ff_eq():
    result = translate_contract("ff_eq(a, b, p)")
    assert "(MumeiLean.Algebra.mumei_ff_eq a b p)" in result.lean_expr
    assert result.is_partial is False


def test_new_algebra_functions_group_order():
    result = translate_contract("group_order(g) > 1")
    assert "(MumeiLean.Algebra.mumei_group_order g)" in result.lean_expr
    assert result.is_partial is False


def test_new_algebra_functions_group_comm():
    result = translate_contract("group_comm(a, b)")
    assert "(MumeiLean.Algebra.mumei_group_comm a b)" in result.lean_expr
    assert result.is_partial is False


def test_quantifier_with_crypto_lowers_skolemize_rule():
    result = translate_contract(
        "forall(x, 0, n, hash(x, salt) > 0)"
    )
    assert "∀ x : Int" in result.lean_expr
    assert "(MumeiLean.Crypto.hash x salt)" in result.lean_expr
    assert result.is_partial is False
    assert result.translator_ir is not None
    assert "quantifier_skolemize_lowering" in result.translator_ir.lowering_rules
    assert "mumei_quantifier_skolemize_bridge" in result.translator_ir.requires_bridge_lemmas


def test_implication_lowering_rule_added():
    result = translate_contract("x > 0 ==> y > 0")
    assert result.translator_ir is not None
    assert "implication_lowering" in result.translator_ir.lowering_rules
    assert "mumei_implication_bridge" in result.translator_ir.requires_bridge_lemmas
    assert any(
        "implication_lowering:" in note
        for note in result.translator_ir.semantic_gap_notes
    )


def test_let_binding_lowering_rule_added():
    result = translate_contract("let x = 5 in x > 0")
    assert result.translator_ir is not None
    assert "let_binding_lowering" in result.translator_ir.lowering_rules
    assert "mumei_let_binding_bridge" in result.translator_ir.requires_bridge_lemmas


def test_complex_quantifier_with_algebra_and_implication():
    result = translate_contract(
        "forall(x, 0, p, is_prime(p) ==> ff_in_field(x, p))"
    )
    assert "∀ x : Int" in result.lean_expr
    assert "→" in result.lean_expr
    assert "(MumeiLean.Algebra.mumei_is_prime p)" in result.lean_expr
    assert "0 ≤ x ∧ x < p" in result.lean_expr
    assert result.is_partial is False


def test_nested_quantifier_with_let_binding():
    result = translate_contract(
        "forall(i, 0, n, let bound = n in arr[i] < bound)"
    )
    assert "∀ i : Int" in result.lean_expr
    assert "let bound := n" in result.lean_expr
    assert result.identifiers == ["n", "arr"]
    assert result.is_partial is False


def test_let_binding_same_name_free_outside_scope_marks_partial():
    result = translate_contract("x > 0 && let x = 1 in x > 0")
    assert result.is_partial is True


def test_crypto_roundtrip_with_quantifier():
    result = translate_contract(
        "forall(i, 0, n, decrypt(encrypt(i, key, i), key, i) == i)"
    )
    assert "∀ i : Int" in result.lean_expr
    assert "(MumeiLean.Crypto.encrypt i key i)" in result.lean_expr
    assert "(MumeiLean.Crypto.decrypt" in result.lean_expr
    assert result.is_partial is False


def test_multiple_quantifiers_with_algebra():
    result = translate_contract(
        "forall(x, 0, p, forall(y, 0, p, "
        "ff_add(x, y, p) == ff_add(y, x, p)))"
    )
    assert result.lean_expr.count("∀ ") == 2
    assert "((x + y) % p)" in result.lean_expr
    assert "((y + x) % p)" in result.lean_expr
    assert result.is_partial is False
    assert "finite_field_lowering" in result.translator_ir.lowering_rules


# ---- Obligation class tests ----


def test_obligation_class_arithmetic():
    result = translate_contract("x > 0 && y < 10")
    assert result.translator_ir is not None
    assert result.translator_ir.obligation_class == OBLIGATION_CLASS_ARITHMETIC


def test_obligation_class_quantifier():
    result = translate_contract("forall(i, 0, n, arr[i] >= 0)")
    assert result.translator_ir is not None
    assert result.translator_ir.obligation_class == OBLIGATION_CLASS_QUANTIFIER


def test_obligation_class_finite_field():
    result = translate_contract("ff_add(a, b, p) == ff_add(b, a, p)")
    assert result.translator_ir is not None
    assert result.translator_ir.obligation_class == OBLIGATION_CLASS_FINITE_FIELD


def test_obligation_class_group_theory():
    result = translate_contract("group_mul(a, b) == group_mul(b, a)")
    assert result.translator_ir is not None
    assert result.translator_ir.obligation_class == OBLIGATION_CLASS_GROUP_THEORY


def test_obligation_class_crypto():
    result = translate_contract("hash(m, s) == hash(m, s)")
    assert result.translator_ir is not None
    assert result.translator_ir.obligation_class == OBLIGATION_CLASS_CRYPTO


def test_obligation_class_smart_contract():
    result = translate_contract("sc_withdraw_allowed(balance, amount)")
    assert result.translator_ir is not None
    assert result.translator_ir.obligation_class == OBLIGATION_CLASS_SMART_CONTRACT


def test_obligation_class_rtgs():
    result = translate_contract("rtgs_balance_conserved(b, d, c, a)")
    assert result.translator_ir is not None
    assert result.translator_ir.obligation_class == OBLIGATION_CLASS_RTGS


def test_obligation_class_unknown():
    result = translate_contract("unknown_obligation(x)")
    assert result.translator_ir is not None
    assert result.translator_ir.obligation_class == OBLIGATION_CLASS_UNKNOWN


def test_obligation_class_crypto_trumps_quantifier():
    result = translate_contract(
        "forall(i, 0, n, decrypt(encrypt(i, key, i), key, i) == i)"
    )
    assert result.translator_ir is not None
    assert result.translator_ir.obligation_class == OBLIGATION_CLASS_CRYPTO


def test_obligation_class_ff_trumps_quantifier():
    result = translate_contract(
        "forall(x, 0, p, ff_in_field(x, p))"
    )
    assert result.translator_ir is not None
    assert result.translator_ir.obligation_class == OBLIGATION_CLASS_FINITE_FIELD


def test_obligation_bridge_lemmas_populated():
    lemmas = obligation_bridge_lemmas(OBLIGATION_CLASS_QUANTIFIER)
    assert len(lemmas) > 0
    assert "MumeiLean.Quantifiers.skolemize_exists" in lemmas


def test_obligation_bridge_lemmas_crypto():
    lemmas = obligation_bridge_lemmas(OBLIGATION_CLASS_CRYPTO)
    assert "MumeiLean.Crypto.encryption_roundtrip" in lemmas


def test_obligation_bridge_lemmas_merged_into_translator_ir():
    result = translate_contract("forall(i, 0, n, arr[i] >= 0)")
    assert result.translator_ir is not None
    bridge = result.translator_ir.requires_bridge_lemmas
    assert "MumeiLean.Quantifiers.skolemize_exists" in bridge


def test_obligation_class_in_translator_ir_dict():
    result = translate_contract("ff_mul(a, b, p) == ff_mul(b, a, p)")
    assert result.translator_ir is not None
    d = result.translator_ir.to_dict()
    assert "obligation_class" in d
    assert d["obligation_class"] == OBLIGATION_CLASS_FINITE_FIELD


def test_classify_obligation_direct():
    from expr_translator import _tokenize, _lowering_rules
    tokens = _tokenize("hash(m, s)")
    rules = _lowering_rules(tokens, [], [])
    assert classify_obligation(tokens, rules) == OBLIGATION_CLASS_CRYPTO


def test_obligation_class_nonlinear_monic_is_arithmetic():
    # PR3 path 6: a single non-conjunction nonlinear predicate has no
    # quantifier / crypto / ff markers, so it falls back to arithmetic.
    result = translate_contract("result >= 0")
    assert result.translator_ir is not None
    assert result.translator_ir.obligation_class == OBLIGATION_CLASS_ARITHMETIC


def test_obligation_class_forall_exists_alternation_is_quantifier():
    # PR3 path 7: nested forall/exists alternation classifies as quantifier.
    result = translate_contract(
        "forall(i, 0, n, exists(j, 0, n, arr[j] <= arr[i]))"
    )
    assert result.translator_ir is not None
    assert result.translator_ir.obligation_class == OBLIGATION_CLASS_QUANTIFIER


def test_obligation_class_inductive_forall_is_quantifier():
    # PR3 path 8: the induction obligation carries a bounded forall, so it
    # classifies as quantifier and routes to the induction bridge lemma.
    result = translate_contract("forall(k, 0, n, k * (k + 1) >= 0)")
    assert result.translator_ir is not None
    assert result.translator_ir.obligation_class == OBLIGATION_CLASS_QUANTIFIER


def test_obligation_bridge_lemmas_include_new_backing_lemmas():
    # PR3 paths 7 & 8 delegate to these existing lemmas; ensure they are
    # discoverable through the quantifier obligation registry.
    lemmas = obligation_bridge_lemmas(OBLIGATION_CLASS_QUANTIFIER)
    assert "MumeiLean.Quantifiers.forall_exists_swap_of_finite" in lemmas
    assert (
        "MumeiLean.AdvancedPatterns.int_nonnegative_induction_pattern" in lemmas
    )


def test_translator_version_is_v2():
    assert expr_translator.TRANSLATOR_VERSION == "mumei-lean-translator-ir-v2"
