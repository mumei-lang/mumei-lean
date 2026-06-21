# mumei-lean Roadmap

## P9-G: Ecosystem Integration — ✅ Implemented

`mumei-lang/mumei-lean` は P9-G NLAE pipeline の Fidelity Checker を担当する。

### Implemented scope

- ✅ `scripts/known_witnesses.py` に `examples/nlae_integration_demo` 用 witness を登録
- ✅ `MumeiLean.SmartContract` に NLAE vault demo 用の Lean witness theorem を追加
- ✅ `mumei-agent.agent.nlae_pipeline.NLAEPipeline` から `run_lean_bridge()` 経由で呼び出される証明 backend を提供
- ✅ `mumei-demo/demos/nlae_integration/run_demo.sh` から 4 repo demo の Fidelity Checker として参照

### P9 completion

P9-D/E/F/G の完了により、NLAE integration milestone は実装済み。

## Lean fallback unknown-obligation bridge — In progress

- `scripts/ingest_cert.py` now treats `z3_result_class == "unknown"` and `status == "unknown"` as Lean escalation candidates, not only raw `z3_check_result == "unknown"`.
- `scripts/expr_translator.py` lowers explicit `unknown_obligation(x)` placeholders into `MumeiLean.AdvancedPatterns.mumei_unknown_obligation x` and marks them with `unknown_obligation_requires_manual_lemma`, so generated Lean stays traceable without falsely promoting unresolved obligations.
- `scripts/export_cert.py`, `MumeiLean/CertParser.lean`, and `MumeiLean/CertWriter.lean` preserve unknown-escalation metadata (`z3_result_class`, `escalation_reason`, `logic_fragment_tags`) through parse/write paths.
- `MumeiLean/AdvancedPatterns.lean`, `Algebra.lean`, and `Crypto.lean` carry the reusable witness surface for unknown obligation triage: placeholder obligations, finite-field equality helpers, and deterministic crypto-input patterns.
