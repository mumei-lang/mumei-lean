# mumei-lean Roadmap

## Cross-project bridge contract

`mumei-lang/mumei/docs/CROSS_PROJECT_ROADMAP.md` owns the global V1 order. For this repo, the V1 rule is narrow: `mumei-lean` expands only the Z3 `unknown` complement path after V1-A/V1-B/V1-C/V1-D produce obligations that the SMT layer cannot close. It is not a general fallback for audit/spec/code findings.

Promotion to `lean_verified` requires a successful Lean build plus matching `translator_version` and `bridge_lemma_hash` in both the exported atom and `lean_result_metadata`; mismatches are `stale_translator`. PRs that update this roadmap should review the cross-project roadmap in the same diff and record relevant bridge regression commands from `tests/`.

## P9-G: Ecosystem Integration — ✅ Implemented

`mumei-lang/mumei-lean` は P9-G NLAE pipeline の Fidelity Checker を担当する。

### Implemented scope

- ✅ `scripts/known_witnesses.py` に `examples/nlae_integration_demo` 用 witness を登録
- ✅ `MumeiLean.SmartContract` に NLAE vault demo 用の Lean witness theorem を追加
- ✅ `mumei-agent.agent.nlae_pipeline.NLAEPipeline` から `run_lean_bridge()` 経由で呼び出される証明 backend を提供
- ✅ `mumei-demo/demos/nlae_integration/run_demo.sh` から 4 repo demo の Fidelity Checker として参照

### P9 completion

P9-D/E/F/G の完了により、NLAE integration milestone は実装済み。

## Lean fallback unknown-obligation bridge — ✅ Implemented

- `scripts/ingest_cert.py` now treats only `z3_result_class == "unknown"` or raw `z3_check_result == "unknown"` as Lean escalation candidates; `status == "unknown"` or `escalation_reason` alone is not enough.
- `scripts/expr_translator.py` lowers explicit `unknown_obligation(x)` placeholders into `MumeiLean.AdvancedPatterns.mumei_unknown_obligation x` and marks them with `unknown_obligation_requires_manual_lemma`, so generated Lean stays traceable without falsely promoting unresolved obligations.
- `scripts/export_cert.py`, `MumeiLean/CertParser.lean`, and `MumeiLean/CertWriter.lean` preserve unknown-escalation metadata (`z3_result_class`, `escalation_reason`, `logic_fragment_tags`) through parse/write paths.
- `MumeiLean/AdvancedPatterns.lean`, `Algebra.lean`, and `Crypto.lean` carry the reusable witness surface for unknown obligation triage: placeholder obligations, finite-field equality helpers, and deterministic crypto-input patterns.
- Live generated theorem coverage now includes **five** paths: `std/math/abs.mm::abs_saturating`, `std/math/patterns.mm::bounded_mul_with_overflow_check`, `std/crypto/primitives.mm::constant_time_eq_flag`, `std/algebra/finite_field.mm::ff_zero_eq_zero`, and `tests/fixtures/sort_ascending.mm::verified_insertion_sort_ascending`, matching the canonical roadmap entry. The bounded-multiplication path uses complete `body_expr` lowering plus mathlib-backed nonlinear arithmetic splitting; the crypto path lowers Mumei braced conditional body semantics for a deterministic 0/1 witness; the algebra path lowers finite-field `ff_zero(p)` body semantics and discharges `ff_eq(result, 0, p)` through `MumeiLean.Algebra.ff_eq_refl`; the sort ascending-preservation path lowers the `forall(i, 0, n-1, arr[i] <= arr[i+1])` ensures surface into `MumeiLean.Sort.insertion_sort_ascending_bridge` backed by mathlib's `List.insertionSort` and `List.Sorted`. All five paths upgrade to `lean_verified` with `known_witness_used = false` only after Lake succeeds and the exported atom plus `lean_result_metadata` carry current `translator_version` and `bridge_lemma_hash` values.
