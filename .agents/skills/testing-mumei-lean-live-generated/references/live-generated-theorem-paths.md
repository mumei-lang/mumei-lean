# Live generated theorem paths catalog

Read this when you need the full list of the twenty live generated theorem paths, their fixtures, and the per-path test commands and expected assertions.

## Live Generated Theorem Paths (20 total)

The bridge ships twenty live generated theorem paths. Each lowers a Z3 `unknown`
(or `spurious_candidate`) atom to a generated Lean theorem that builds with
`known_witness_used = false`:

1. `abs_saturating` — saturating i64 body semantics.
2. `bounded_mul_with_overflow_check` — nonlinear conjunction body semantics.
3. `constant_time_eq_flag` — crypto deterministic 0/1 witness.
4. `ff_zero_eq_zero` — finite-field equality via `MumeiLean.Algebra.ff_eq_refl`.
5. `verified_insertion_sort_ascending` — sort ascending preservation via `MumeiLean.Sort.insertion_sort_ascending_bridge`.
6. `poly_bound_monotone` — single non-conjunction nonlinear arithmetic (`result >= 0` over `x*x + 2*x + 1`) via `mumei_arith_deep`.
7. `exists_pivot_partition` — forall/exists quantifier alternation via `MumeiLean.Quantifiers.forall_exists_swap_of_finite`.
8. `sum_nonneg_inductive` — natural-number induction via `MumeiLean.AdvancedPatterns.int_nonnegative_induction_pattern`.
9. `rtgs_transfer_conservation` — RTGS balance conservation via `mumei_arith`.
10. `ff_mul_commutative` — finite-field commutativity (`ff_eq` over swapped `ff_mul` operands) via `MumeiLean.Algebra.ff_mul_comm_eq`.
11. `ff_mul_associative` — finite-field associativity (`ff_eq` over a re-associated `ff_mul` nesting) via `MumeiLean.Algebra.ff_mul_assoc_mod` + `ff_eq_refl`, selected by `translator_ir.bridge_pattern == "finite_field_associativity"`.
12. `ff_mul_add_distributive` — finite-field distributivity with no bridge lemma template; the deterministic tactic search (`scripts/tactic_search.py`) adopts `mumei_ff_mod`.
13. `predicate_guard_collapse` — predicate-parametric, classically-valid guard collapse; the widened ladder adopts `tauto`.
14. `ff_pow_square_expands` — modular square expanded into repeated modular multiplication; `mumei_ff_mod` does not reach under the exponent, so the ladder tail entry `mumei_ff_pow` is adopted.
15. `cei_compliant_withdraw` / `guarded_state_update` — `{ perform Eff.op…; <pure tail> }` bodies lower to the tail via `perform_statement_lowering` (spec §4.3); no bridge lemma, `bridge_lemma_hash` unchanged.
16. `move_once` / `read_before_move` — `{ let x = e; …; <tail> }` bodies substitute each binding into the tail via `let_statement_lowering` (spec §4.4); no bridge lemma, `bridge_lemma_hash` unchanged.
17. `clamp_to_range` — `{ if c { a } else { if … } }` bodies recurse through `translate_body` via `nested_if_lowering` (spec §4.5); `mumei_arith_deep`'s `split <;> omega` discharges the theorem, no bridge lemma, `bridge_lemma_hash` unchanged.
18. `take_point` — `p.x` field reads in `requires` / `body` lower to the scalar binder `p_x` via `struct_projection_lowering` (spec §4.6); `mumei_arith_deep` discharges the theorem, no bridge lemma, `bridge_lemma_hash` unchanged.
19. `join_all_last_result` — `task {…}` / `task_group:all {…}` bodies lower to the last task's value via `task_value_lowering` / `task_group_all_lowering` (spec §4.7); tags the new `concurrency_obligation` class and bumps `bridge_lemma_hash` to `5716cfdd…` (first catalog change).
20. `race_two_replicas` — `task_group:any { task {…}; … }` bodies lower to the candidate-value list `[e₁, …, eₙ]` via `task_group_any_lowering` (spec §4.7); the def is `List Int`, the theorem hypothesises `result ∈ <def>`, and `fin_cases` splits membership per candidate. Reuses the `concurrency_obligation` catalog — `bridge_lemma_hash` unchanged.

Focused pytest coverage for paths 19–20, Lake required:

```bash
cd /home/ubuntu/repos/mumei-lean
PATH="$HOME/.elan/bin:$PATH" python -m pytest tests/test_lean_bridge_e2e.py -q \
  -k "task_group"
```

Negative controls for paths 19–20 (unit level, no Lake needed):
`tests/test_expr_translator.py::test_translate_body_keeps_task_group_edge_cases_partial`
covers non-`task` group items, an empty group, an unknown join mode, a
task body that does not lower, a rebind on a non-`let` name, and residual
concurrency/ownership surfaces (`send`/`recv`/`acquire`/`<-` arrows, ...) —
all stay partial. `test_translate_body_lowers_task_and_task_group_all`
also pins the `any` Int-typed-element guard.

Focused pytest coverage for path 18, Lake required:

```bash
cd /home/ubuntu/repos/mumei-lean
PATH="$HOME/.elan/bin:$PATH" python -m pytest tests/test_lean_bridge_e2e.py -q \
  -k "struct_projection"
```

Negative controls for path 18 (unit level, no Lake needed):
`tests/test_expr_translator.py::test_translate_body_keeps_non_field_projection_partial`
covers a qualified effect name (`perform Eff.op`), a method call, postfix
access on a call result, a non-identifier member, a projected-name collision
with an existing binder, and a float literal — all stay partial.

Focused pytest coverage for path 17, Lake required:

```bash
cd /home/ubuntu/repos/mumei-lean
PATH="$HOME/.elan/bin:$PATH" python -m pytest tests/test_lean_bridge_e2e.py -q \
  -k "nested_if"
```

Negative controls for path 17 (unit level, no Lake needed):
`tests/test_expr_translator.py::test_translate_body_keeps_malformed_braced_if_partial`
covers trailing tokens after the else block, `else ifx`, a missing `else`,
and a nested `if` without its own `else` — all stay partial.

Focused pytest coverage for path 16, Lake required:

```bash
cd /home/ubuntu/repos/mumei-lean
PATH="$HOME/.elan/bin:$PATH" python -m pytest tests/test_lean_bridge_e2e.py -q \
  -k "let_sequence"
```

Negative controls for path 16 (unit level, no Lake needed):
`tests/test_expr_translator.py::test_translate_body_keeps_unsupported_statement_sequences_partial`
covers a trailing `let` with no tail, a bound name rebound inside the tail
(`let` / `forall` binder), a bound name in call position, `==` in place of
`=`, and a non-`let`/`perform` statement in the prefix — all stay partial.

Focused pytest coverage for path 15, Lake required:

```bash
cd /home/ubuntu/repos/mumei-lean
PATH="$HOME/.elan/bin:$PATH" python -m pytest tests/test_lean_bridge_e2e.py -q \
  -k "perform_sequence"
```

Negative controls for path 15 (unit level, no Lake needed):
`tests/test_expr_translator.py::test_translate_body_keeps_non_perform_sequence_blocks_partial`
covers a `perform` in tail position, a bare `perform` keyword as tail, a
non-`perform` statement in the prefix, and braces not enclosing the whole
source — all stay partial.

Focused pytest coverage for paths 9–11, Lake required:

```bash
cd /home/ubuntu/repos/mumei-lean
PATH="$HOME/.elan/bin:$PATH" python -m pytest tests/test_lean_bridge_e2e.py -q \
  -k "rtgs_transfer_conservation or finite_field_commutativity or finite_field_associativity"
```

Adversarial negative control for path 11: change the fixture `ensures` to an
operand order that is *not* the re-association of the body (e.g.
`ff_eq(result, ff_mul(b, ff_mul(a, c, p), p), p)`) and assert the rendered proof
falls back to `mumei_arith_deep` without citing `ff_mul_assoc_mod`
(`tests/test_ingest_cert.py::test_finite_field_associativity_requires_matching_operand_order`).

Focused pytest coverage for the three PR3 paths (6–8), Lake required:

```bash
cd /home/ubuntu/repos/mumei-lean
PATH="$HOME/.elan/bin:$PATH" python -m pytest tests/test_lean_bridge_e2e.py -q \
  -k "poly_bound_monotone or exists_pivot_partition or sum_nonneg_inductive"
```

Expected bridge assertions for each of the three fixtures
(`tests/fixtures/std_math_patterns_poly_bound.proof-cert.json`,
`tests/fixtures/std_list_exists_pivot_partition.proof-cert.json`,
`tests/fixtures/std_math_patterns_sum_nonneg.proof-cert.json`):

- `lake build` exits with status 0 and no `sorry` warning.
- Lean cert atom has `z3_check_result == "lean_verified"` and `status == "verified"`.
- `lean_metadata.known_witness_used is False`.
- Theorem names are `Generated.Std.Math.Patterns.poly_bound_monotone_correct`, `Generated.Std.List.exists_pivot_partition_correct`, and `Generated.Std.Math.Patterns.sum_nonneg_inductive_correct` respectively.

Non-Lake unit coverage:

```bash
cd /home/ubuntu/repos/mumei-lean
PYTHONPATH=scripts MUMEI_LEAN_SKIP_LIVE=1 python -m pytest \
  tests/test_ingest_cert.py tests/test_expr_translator.py \
  tests/test_export_cert.py tests/test_contract_vocabulary.py -q
```
