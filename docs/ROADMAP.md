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
- Live generated theorem coverage now includes **eight** paths: `std/math/abs.mm::abs_saturating`, `std/math/patterns.mm::bounded_mul_with_overflow_check`, `std/crypto/primitives.mm::constant_time_eq_flag`, `std/algebra/finite_field.mm::ff_zero_eq_zero`, `tests/fixtures/sort_ascending.mm::verified_insertion_sort_ascending`, `std/math/patterns.mm::poly_bound_monotone`, `std/list.mm::exists_pivot_partition`, and `std/math/patterns.mm::sum_nonneg_inductive`, matching the canonical roadmap entry. The bounded-multiplication path uses complete `body_expr` lowering plus mathlib-backed nonlinear arithmetic splitting; the crypto path lowers Mumei braced conditional body semantics for a deterministic 0/1 witness; the algebra path lowers finite-field `ff_zero(p)` body semantics and discharges `ff_eq(result, 0, p)` through `MumeiLean.Algebra.ff_eq_refl`; the sort ascending-preservation path lowers the `forall(i, 0, n-1, arr[i] <= arr[i+1])` ensures surface into `MumeiLean.Sort.insertion_sort_ascending_bridge` backed by mathlib's `List.insertionSort` and `List.Sorted`; the nonlinear-monic path (`poly_bound_monotone`) discharges a single non-conjunction `result >= 0` obligation over a perfect-square polynomial through `mumei_arith_deep` (nlinarith/positivity); the quantifier-alternation path (`exists_pivot_partition`) discharges a trigger-sensitive ∀∃ obligation through `MumeiLean.Quantifiers.forall_exists_swap_of_finite` with an explicit choice witness; the induction path (`sum_nonneg_inductive`) discharges a recursive nonnegativity obligation through `MumeiLean.AdvancedPatterns.int_nonnegative_induction_pattern`. All eight paths upgrade to `lean_verified` with `known_witness_used = false` only after Lake succeeds and the exported atom plus `lean_result_metadata` carry current `translator_version` and `bridge_lemma_hash` values. The last three paths add no new backing lemma and therefore leave `bridge_lemma_hash` unchanged.
