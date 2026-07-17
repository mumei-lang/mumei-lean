# Changelog

## 2026-07-17: Live generated theorem paths expanded from 5 to 8

- Added the 6th live generated theorem path `std/math/patterns.mm::poly_bound_monotone`: a single non-conjunction nonlinear-arithmetic obligation (`result >= 0` over `x*x + 2*x + 1`) lowered through the generic body-semantics path and discharged by `mumei_arith_deep`. Certificate solver class is `unknown`.
- Added the 7th live generated theorem path `std/list.mm::exists_pivot_partition`: a forall/exists quantifier-alternation obligation (Z3 `spurious_candidate`) discharged through `MumeiLean.Quantifiers.forall_exists_swap_of_finite` with an explicit identity choice witness.
- Added the 8th live generated theorem path `std/math/patterns.mm::sum_nonneg_inductive`: a natural-number induction obligation (Z3 `unknown`) discharged through `MumeiLean.AdvancedPatterns.int_nonnegative_induction_pattern`.
- `scripts/ingest_cert.py` selects the ∀∃ and induction proof shapes via explicit `translator_ir.bridge_pattern` markers (`forall_exists_swap`, `int_nonnegative_induction`), mirroring the sort branch; the nonlinear-monic path reuses the existing body-semantics route.
- All three new paths build with `known_witness_used = false` and no `sorry`, reuse existing backing lemmas, and therefore leave `bridge_lemma_hash` unchanged.
- Added fixtures `tests/fixtures/std_math_patterns_poly_bound.proof-cert.json`, `tests/fixtures/std_list_exists_pivot_partition.proof-cert.json`, `tests/fixtures/std_math_patterns_sum_nonneg.proof-cert.json` and unit/E2E coverage in `tests/test_ingest_cert.py`, `tests/test_expr_translator.py`, `tests/test_lean_bridge_e2e.py`, `tests/test_export_cert.py`.
- Synced the path count from **five** to **eight** across `README.md`, `docs/LEAN_HARNESS_CONTRACT.md`, `docs/LEAN_TRANSLATOR_SPEC.md` (new §5.12/§5.13, extended §5.8), `docs/ARCHITECTURE.md`, `docs/ROADMAP.md`, and `.agents/skills/testing-mumei-lean-live-generated/SKILL.md`.

## 2026-06-30: Sort ascending-preservation as 5th live generated theorem path

- Added a fifth live generated theorem path for `tests/fixtures/sort_ascending.mm::verified_insertion_sort_ascending`, backed by a proof-certificate fixture whose solver class is `unknown` due to Z3 Array+forall quantifier timeout on the `forall(i, 0, n-1, arr[i] <= arr[i+1])` ensures surface.
- `MumeiLean/Sort.lean` provides bridge lemmas `insertion_sort_ascending_bridge` and `sorted_adjacent_le` backed by mathlib's `List.insertionSort` and `List.Sorted`.
- Updated `docs/ROADMAP.md` live generated theorem coverage from four to **five** paths.

## 2026-06-28: Live generated Lean bridge coverage

- Added a fourth live generated theorem path for `std/algebra/finite_field.mm::ff_zero_eq_zero`, backed by a finite-field proof-certificate fixture whose solver class is `unknown` and whose `body_expr` lowers to `ff_zero(p)`.
- Extended generated theorem automation so finite-field equality obligations of the form `ff_eq(result, 0, p)` are discharged through `MumeiLean.Algebra.ff_eq_refl` without a known-witness override.
- Added a second live generated theorem path for `std/math/patterns.mm::bounded_mul_with_overflow_check`, backed by a proof-certificate fixture whose solver class is `unknown` and whose `body_expr` lowers to a complete Lean proof obligation.
- Extended generated theorem automation so body-semantics nonlinear postcondition conjunctions can be discharged by Lake without a known-witness override; successful exports keep `known_witness_used = false`.
- Updated roadmap and translator docs to mark the Lean fallback unknown-obligation bridge implemented while preserving the invariant that only Z3 `unknown` candidates with current `translator_version` and `bridge_lemma_hash` can become `lean_verified`.
