# Changelog

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
