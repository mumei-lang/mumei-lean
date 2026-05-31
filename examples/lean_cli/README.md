# Lean CLI executable example

This directory shows a small production-style CLI written directly in Lean 4.
The executable is built by Lake and exported together with `.lean-cert.json`.
The example pins the same Lean toolchain as the repository root.

## Build with Lake

```bash
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

## Commands

```bash
simple-cli --help
simple-cli greet Mumei
simple-cli add 2 40
simple-cli echo verified specs become production code
simple-cli merkle 7 3 4 7 1
simple-cli defi-transfer 20 30 5
simple-cli audit-commitment 10 20 30 60
```

The `merkle`, `defi-transfer`, and `audit-commitment` commands import the
committed Phase 4-6 witness modules from the repository root:

- `MumeiLean.MerkleTree`
- `MumeiLean.DeFi`
- `MumeiLean.ArkLibAudit`
