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
