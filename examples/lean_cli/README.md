# Lean CLI executable example

This directory shows a small production-style CLI written directly in Lean 4.
The executable is built by Lake and exported together with `.lean-cert.json`.
The example pins the same Lean toolchain as the repository root.

The CLI combines ordinary commands (`greet`, `add`, `echo`) with a tiny
Mumei-DSL-shaped interpreter:

```text
mumei-dsl add <n> <m>
mumei-dsl len <text...>
mumei-dsl concat <left> <right>
```

`SimpleCli.lean` keeps the interpreter pure (`parseMiniMumei` +
`evalMiniMumei`) and exposes Lean theorems such as
`evalMiniMumei_add_matches_contract` as proof witnesses for the shipped
runtime behavior.

## Build with Lake

```bash
cd examples/lean_cli
PATH="$HOME/.elan/bin:$PATH" lake build simple-cli
.lake/build/bin/simple-cli greet Mumei
```

## Export binary + certificate

From the repository root:

```bash
python scripts/lean_to_executable.py \
  --project-dir examples/lean_cli \
  --module SimpleCli \
  --out-dir out/lean_cli
```

The output directory will contain:

```text
simple-cli
.lean-cert.json
```

The copied `.lean-cert.json` is the proof stamp for the executable artifact.
It records the Lean module, Lake target, `status: "verified"`, and the witness
theorems that justify the interpreter and Phase 4-6 demo commands.

## Commands

```bash
simple-cli --help
simple-cli greet Mumei
simple-cli add 2 40
simple-cli echo verified specs become production code
simple-cli mumei-dsl add 2 40
simple-cli mumei-dsl len verified specs
simple-cli mumei-dsl concat proof stamp
simple-cli merkle 7 3 4 7 1
simple-cli defi-transfer 20 30 5
simple-cli audit-commitment 10 20 30 60
```

The `merkle`, `defi-transfer`, and `audit-commitment` commands import the
committed Phase 4-6 witness modules from the repository root:

- `MumeiLean.MerkleTree`
- `MumeiLean.DeFi`
- `MumeiLean.ArkLibAudit`
