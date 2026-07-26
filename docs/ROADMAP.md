# mumei-lean Roadmap

## Cross-project bridge contract

`mumei-lang/mumei/docs/CROSS_PROJECT_ROADMAP.md` owns the global V1 order. For this repo, the V1 rule is narrow: `mumei-lean` expands only the Z3 `unknown` complement path after V1-A/V1-B/V1-C/V1-D produce obligations that the SMT layer cannot close. It is not a general fallback for audit/spec/code findings.

Promotion to `lean_verified` requires a successful Lean build plus matching `translator_version` and `bridge_lemma_hash` in both the exported atom and `lean_result_metadata`; mismatches are `stale_translator`. PRs that update this roadmap should review the cross-project roadmap in the same diff and record relevant bridge regression commands from `tests/`.

Run the local contract vocabulary gate before opening a PR that touches `README.md`, `docs/LEAN_HARNESS_CONTRACT.md`, `docs/INTEGRATION.md`, or the bridge scripts:

```bash
PYTHONPATH=scripts MUMEI_LEAN_SKIP_LIVE=1 python -m pytest tests/test_contract_vocabulary.py -q
```

CI enforces the same gate through `.github/workflows/contract-vocabulary.yml`. This test also pins the `TRANSLATOR_VERSION`/`BRIDGE_LEMMA_HASH` constants against the values documented in `docs/LEAN_HARNESS_CONTRACT.md`, so it doubles as the bidirectional drift guard for the canonical `mumei/scripts/check_contract_vocabulary.py` gate.

## P9-G: Ecosystem Integration — ✅ Implemented

`mumei-lang/mumei-lean` は P9-G NLAE pipeline の Fidelity Checker を担当する。

### Implemented scope

- ✅ `scripts/known_witnesses.py` に `examples/nlae_integration_demo` 用 witness を登録
- ✅ `MumeiLean.SmartContract` に NLAE vault demo 用の Lean witness theorem を追加
- ✅ `mumei-agent.agent.nlae_pipeline.NLAEPipeline` から `run_lean_bridge()` 経由で呼び出される証明 backend を提供
- ✅ `mumei-demo/demos/nlae_integration/run_demo.sh` から 4 repo demo の Fidelity Checker として参照

### P9 completion

P9-D/E/F/G の完了により、NLAE integration milestone は実装済み。

## Contract Expression Translator Extension — ✅ Implemented

Extends the v1 bridge to formal **obligation class** taxonomy with v2 translator. Each escalated atom is now classified into one of eight obligation classes (`quantifier_obligation`, `finite_field_obligation`, `group_theory_obligation`, `crypto_primitive_obligation`, `arithmetic_obligation`, `smart_contract_obligation`, `rtgs_obligation`, `unknown_obligation`), and the classification is recorded in `TranslatorIR.obligation_class`. Each class maps to a set of canonical Lean bridge lemma entry points in `MumeiLean/AdvancedPatterns.lean`, `MumeiLean/Algebra.lean`, `MumeiLean/Crypto.lean`, and `MumeiLean/Quantifiers.lean`.

- ✅ `scripts/expr_translator.py`: obligation class taxonomy, `classify_obligation()`, `obligation_bridge_lemmas()`, bridge lemma merge into `TranslatorIR.requires_bridge_lemmas`
- ✅ `MumeiLean/AdvancedPatterns.lean`: obligation class bridge templates (bounded forall/exists, crypto roundtrip, finite field closure, group associativity)
- ✅ `tests/test_expr_translator.py`: 17 obligation class regression tests covering all 8 classes, priority ordering, bridge lemma population, and `TranslatorIR` serialization
- ✅ `translator_version` bumped to `mumei-lean-translator-ir-v2`, `bridge_lemma_hash` updated

## Lean fallback unknown-obligation bridge — ✅ Implemented

- `scripts/ingest_cert.py` now treats only `z3_result_class == "unknown"` or raw `z3_check_result == "unknown"` as Lean escalation candidates; `status == "unknown"` or `escalation_reason` alone is not enough.
- `scripts/expr_translator.py` lowers explicit `unknown_obligation(x)` placeholders into `MumeiLean.AdvancedPatterns.mumei_unknown_obligation x` and marks them with `unknown_obligation_requires_manual_lemma`, so generated Lean stays traceable without falsely promoting unresolved obligations.
- `scripts/export_cert.py`, `MumeiLean/CertParser.lean`, and `MumeiLean/CertWriter.lean` preserve unknown-escalation metadata (`z3_result_class`, `escalation_reason`, `logic_fragment_tags`) through parse/write paths.
- `MumeiLean/AdvancedPatterns.lean`, `Algebra.lean`, and `Crypto.lean` carry the reusable witness surface for unknown obligation triage: placeholder obligations, finite-field equality helpers, and deterministic crypto-input patterns.
- Live generated theorem coverage includes these **eight** paths (extended to ten by the catalog and finite-field commutativity work below): `std/math/abs.mm::abs_saturating`, `std/math/patterns.mm::bounded_mul_with_overflow_check`, `std/crypto/primitives.mm::constant_time_eq_flag`, `std/algebra/finite_field.mm::ff_zero_eq_zero`, `tests/fixtures/sort_ascending.mm::verified_insertion_sort_ascending`, `std/math/patterns.mm::poly_bound_monotone`, `std/list.mm::exists_pivot_partition`, and `std/math/patterns.mm::sum_nonneg_inductive`, matching the canonical roadmap entry. The bounded-multiplication path uses complete `body_expr` lowering plus mathlib-backed nonlinear arithmetic splitting; the crypto path lowers Mumei braced conditional body semantics for a deterministic 0/1 witness; the algebra path lowers finite-field `ff_zero(p)` body semantics and discharges `ff_eq(result, 0, p)` through `MumeiLean.Algebra.ff_eq_refl`; the sort ascending-preservation path lowers the `forall(i, 0, n-1, arr[i] <= arr[i+1])` ensures surface into `MumeiLean.Sort.insertion_sort_ascending_bridge` backed by mathlib's `List.insertionSort` and `List.Sorted`; the nonlinear-monic path (`poly_bound_monotone`) discharges a single non-conjunction `result >= 0` obligation over a perfect-square polynomial through `mumei_arith_deep` (nlinarith/positivity); the quantifier-alternation path (`exists_pivot_partition`) discharges a trigger-sensitive ∀∃ obligation through `MumeiLean.Quantifiers.forall_exists_swap_of_finite` with an explicit choice witness; the induction path (`sum_nonneg_inductive`) discharges a recursive nonnegativity obligation through `MumeiLean.AdvancedPatterns.int_nonnegative_induction_pattern`. All eight paths upgrade to `lean_verified` with `known_witness_used = false` only after Lake succeeds and the exported atom plus `lean_result_metadata` carry current `translator_version` and `bridge_lemma_hash` values. The last three paths add no new backing lemma and therefore leave `bridge_lemma_hash` unchanged.

## Finite-field / group / quantifier bridge lemma expansion — ✅ Implemented

Spec: [`docs/LEAN_TRANSLATOR_SPEC.md`](LEAN_TRANSLATOR_SPEC.md) §5.6 (tactics), §5.14 (commutativity bridge), §8 (lowering rules), §10 (catalog).

- ✅ `finite_field_commutativity_lowering` lowers `ff_eq` goals whose operands are swapped `ff_add` / `ff_mul` calls, and `scripts/ingest_cert.py` discharges them with `MumeiLean.Algebra.ff_add_comm_eq` / `ff_mul_comm_eq` instead of a `manual_lemma_reason`. Brace-wrapped finite-field bodies (`{ ff_mul(a, b, p) }`) now lower to the same term as the bare call.
- ✅ `MumeiLean/Algebra.lean` gains `ff_add_comm_eq`, `ff_mul_comm_eq`, `ff_add_assoc_mod`, `ff_mul_assoc_mod`, `ff_pow_zero`, `ff_inv_zero`, `group_pow_zero`, `group_pow_add`, `group_conj_inv`, `mumei_group_pow_zero_int`; `MumeiLean/Quantifiers.lean` gains `bounded_forall_imp`, `bounded_forall_of_field_range`, `nested_bounded_forall_intro`; `MumeiLean/Crypto.lean` gains `hmac_modulus_bounds`, `commitment_modulus_bounds`; `MumeiLean/AdvancedPatterns.lean` gains the `mumei_field` coverage patterns `finite_field_commutativity_pattern` / `group_conjugation_pattern`.
- ✅ `MumeiLean/Tactics.lean`: `mumei_arith` / `mumei_arith_deep` try `ring1` and `field_simp`, and the new `mumei_field` cascade (`ring1` → carrier `simp only` + `ring_nf` → `group` → `field_simp` → `ring_nf` → `omega` → `simp`) automates finite-field and group goals.
- ✅ `bridge_lemma_hash` bumped to `ee8cd3ba96c3318b3f07445f4755619744d4e1f9a662af94f3cbce6d41ed4347` with every pinned doc, fixture, `scripts/export_cert.py`, and mumei-agent's `_SOLIDITY_GUARD_TRACE_BRIDGE_LEMMA_HASH` updated in the same change set.
- ✅ `MumeiLean/CertWriter.lean` no longer rewrites `z3_result_class` when a proof succeeds, matching `scripts/export_cert.py`; `tests/test_cert_roundtrip.py` pins `z3_result_class` / `escalation_reason` / `logic_fragment_tags` across the native parse → write → parse round trip.

## Obligation class bridge lemma catalog and escalation timing — ✅ Implemented

Spec: [`docs/LEAN_TRANSLATOR_SPEC.md`](LEAN_TRANSLATOR_SPEC.md) §10 (catalog) and §11 (timing).

- ✅ Every one of the eight base obligation classes now has at least four backing bridge lemmas: `MumeiLean/Algebra.lean` gains the arithmetic (`arith_add_upper_bound`, `arith_add_monotone`, `arith_mul_nonneg_of_nonneg`, `arith_square_nonneg`, `arith_bounded_of_interval`) and RTGS (`rtgs_debit_leaves_nonnegative`, `rtgs_transfer_conserves_sum_of_amounts`) surface plus `ff_sub_self_eq_zero_mod` / `group_mul_left_cancel`; `MumeiLean/Quantifiers.lean` gains bounded-range decomposition (`bounded_forall_split_at`, `bounded_forall_shift`, `bounded_exists_of_nonempty_forall`); `MumeiLean/Crypto.lean` gains commitment/ZK stability lemmas; `MumeiLean/AdvancedPatterns.lean` gains the arithmetic, smart-contract, RTGS, and unknown-obligation templates.
- ✅ `BRIDGE_LEMMA_HASH` is now *derived* from the catalog by `expr_translator.compute_bridge_lemma_hash()` and pinned to `ee8cd3ba96c3318b3f07445f4755619744d4e1f9a662af94f3cbce6d41ed4347`; `tests/test_expr_translator.py::test_bridge_lemma_hash_matches_catalog` fails if the catalog and the constant drift. All pinned docs, fixtures, and `scripts/export_cert.py` were updated in the same diff, and mumei-agent's `_SOLIDITY_GUARD_TRACE_BRIDGE_LEMMA_HASH` must land the same value.
- ✅ Live generated theorem coverage is now **eleven** paths: the eight above plus `std/settlement.mm::rtgs_transfer_conservation` (`tests/fixtures/std_settlement_rtgs_conservation.proof-cert.json`), an `rtgs_obligation` conservation goal discharged by `mumei_arith` with `known_witness_used = false`, and `std/algebra/finite_field.mm::ff_mul_commutative` (`tests/fixtures/std_algebra_finite_field_ff_mul_commutative.proof-cert.json`), a `finite_field_obligation` whose swapped-operand `ff_eq` goal is discharged by `MumeiLean.Algebra.ff_mul_comm_eq`, and `std/algebra/finite_field.mm::ff_mul_associative` (`tests/fixtures/std_algebra_finite_field_ff_mul_associative.proof-cert.json`), a `finite_field_obligation` whose re-associated `ff_eq` goal is discharged by `MumeiLean.Algebra.ff_mul_assoc_mod` + `ff_eq_refl` (§5.15). The associativity path reuses existing catalog lemmas, so `bridge_lemma_hash` is unchanged.
- ✅ `scripts/bridge.py` measures the `lake build` wall-clock cost and reports it as `lean_solver_time_s` in each atom's `lean_result_metadata` and in the summary `lean_fallback` block; dry runs (`--no-build`) and missing Lake report `null` so the mumei benchmark can degrade to a zero-cost `SKIP`.
- ✅ `MumeiLean/CertParser.lean` / `CertWriter.lean` parse and re-emit `translator_version`, `bridge_lemma_hash`, `manual_lemma_reason`, and `lean_result_metadata` (including `lean_solver_time_s`), so the native path round-trips the Python bridge output without losing the harness contract.

Regression commands:

```bash
PYTHONPATH=scripts MUMEI_LEAN_SKIP_LIVE=1 python -m pytest -q
PYTHONPATH=scripts MUMEI_LEAN_SKIP_LIVE=1 python -m pytest tests/test_contract_vocabulary.py -q
PATH="$HOME/.elan/bin:$PATH" python -m pytest tests/test_cert_roundtrip.py tests/test_lean_bridge_e2e.py -q
PATH="$HOME/.elan/bin:$PATH" lake build
```
