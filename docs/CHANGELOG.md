# Changelog

## 2026-08-02: Live path count synced to thirteen

- Synced the live generated theorem path count from **eleven** to **thirteen** in `docs/LEAN_HARNESS_CONTRACT.md` and `.agents/skills/testing-mumei-lean-live-generated/SKILL.md`, matching `docs/ROADMAP.md`, `docs/ARCHITECTURE.md`, `docs/LEAN_TRANSLATOR_SPEC.md`, and the E2E fixtures. `translator_version` stays `mumei-lean-translator-ir-v2` and `bridge_lemma_hash` stays `ee8cd3ba96c3318b3f07445f4755619744d4e1f9a662af94f3cbce6d41ed4347`.
- Recorded the 12th live generated theorem path `std/algebra/finite_field.mm::ff_mul_add_distributive` (`tests/fixtures/std_algebra_finite_field_ff_mul_add_distributive.proof-cert.json`): a `finite_field_obligation` that no bridge lemma template covers, adopted by the deterministic tactic search (`scripts/tactic_search.py`, §12) as `mumei_ff_mod`, building `Generated.Std.Algebra.Finite_field.ff_mul_add_distributive_correct` with `known_witness_used = false`.
- Recorded the 13th live generated theorem path `std/core_predicates.mm::predicate_guard_collapse` (`tests/fixtures/std_core_predicates_guard_collapse.proof-cert.json`): a predicate-parametric, classically-valid guard collapse discharged by `tauto` from the widened 16-candidate ladder (§12.2), building `Generated.Std.Core_predicates.predicate_guard_collapse_correct` with `known_witness_used = false`. Both search-adopted paths substitute tactics only, so `bridge_lemma_hash` is unchanged.

## 2026-07-26: Finite-field associativity bridge as 11th live generated theorem path

- Added the 11th live generated theorem path `std/algebra/finite_field.mm::ff_mul_associative` (§5.15): an `ff_eq` obligation comparing a left-associated `ff_mul` body with its right-associated form (Z3 `unknown` on the nested `%` interaction), discharged by rewriting with `MumeiLean.Algebra.ff_mul_assoc_mod` and closing with `ff_eq_refl`, `known_witness_used = false`. `ff_add` is covered by the same lowering through `ff_add_assoc_mod`.
- The path is selected by the explicit `translator_ir.bridge_pattern == "finite_field_associativity"` marker (as in §5.12 / §5.13), so an `ensures` that is not the re-association of the body falls back to `mumei_arith_deep`; a negative-control test pins that behaviour.
- Both backing lemmas already exist in the catalog, so `bridge_lemma_hash` stays `ee8cd3ba96c3318b3f07445f4755619744d4e1f9a662af94f3cbce6d41ed4347`.
- Documented the two completed roadmap items with their originating PRs: RTGS `balance_conservation` (#8, extended in #44) and contract-expression translator / `mumei_arith` expansion (#100); CertParser/CertWriter native implementation (#3).
- Live path count synced from **ten** to **eleven** across `docs/ARCHITECTURE.md`, `docs/LEAN_HARNESS_CONTRACT.md`, `docs/ROADMAP.md`, `docs/LEAN_TRANSLATOR_SPEC.md`, and `.agents/skills/testing-mumei-lean-live-generated/SKILL.md`.

## 2026-07-26: Finite-field commutativity bridge as 10th live generated theorem path

- Added the 10th live generated theorem path `std/algebra/finite_field.mm::ff_mul_commutative`: an `ff_eq` obligation whose operands are a swapped `ff_mul` call (Z3 `unknown` on the nonlinear `%` interaction) discharged through the new `MumeiLean.Algebra.ff_mul_comm_eq` bridge lemma with `known_witness_used = false`. `ff_add` is covered by the same lowering through `ff_add_comm_eq`.
- Added lowering rule `finite_field_commutativity_lowering` (§5.14) and brace-unwrapping for finite-field helper bodies, so `{ ff_mul(a, b, p) }` lowers to the same Lean term as the bare call instead of falling back to the contract-only theorem shape.
- Extended the bridge lemma catalog: `MumeiLean/Algebra.lean` (`ff_add_comm_eq`, `ff_mul_comm_eq`, `ff_add_assoc_mod`, `ff_mul_assoc_mod`, `ff_pow_zero`, `ff_inv_zero`, `group_pow_zero`, `group_pow_add`, `group_conj_inv`, `mumei_group_pow_zero_int`), `MumeiLean/Quantifiers.lean` (`bounded_forall_imp`, `bounded_forall_of_field_range`, `nested_bounded_forall_intro`), `MumeiLean/Crypto.lean` (`hmac_modulus_bounds`, `commitment_modulus_bounds`), `MumeiLean/AdvancedPatterns.lean` (`finite_field_commutativity_pattern`, `group_conjugation_pattern`).
- `MumeiLean/Tactics.lean`: `mumei_arith` / `mumei_arith_deep` now try `ring1` and `field_simp`, and the new `mumei_field` cascade automates finite-field and group goals. `ring1` is used instead of `ring` because mathlib's `ring` succeeds after normalising an unclosed goal, which would swallow later stages of the cascade.
- `bridge_lemma_hash` bumped to `ee8cd3ba96c3318b3f07445f4755619744d4e1f9a662af94f3cbce6d41ed4347` (derived from the catalog); all pinned docs, fixtures, `scripts/export_cert.py`, and mumei-agent's `_SOLIDITY_GUARD_TRACE_BRIDGE_LEMMA_HASH` updated in the same change set.
- `MumeiLean/CertWriter.lean` keeps `z3_result_class` as parsed when a proof succeeds (previously overwritten with `lean_verified`), matching `scripts/export_cert.py`; `tests/test_cert_roundtrip.py` now pins `z3_result_class` / `escalation_reason` / `logic_fragment_tags` across the native round trip.
- Synced the live path count from **eight** to **ten** (including the previously undocumented RTGS conservation path) across `docs/LEAN_HARNESS_CONTRACT.md`, `docs/ARCHITECTURE.md`, `docs/ROADMAP.md`, and `.agents/skills/testing-mumei-lean-live-generated/SKILL.md`.

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
