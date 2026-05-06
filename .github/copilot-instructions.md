# mumei-lean Development Guide

Always reference these instructions first and fall back to search or shell commands only when you encounter unexpected information that does not match the info here.

## Working Effectively

### Repository Role

`mumei-lean` is the external Lean 4 backend for Mumei proof certificates. It translates Mumei `.proof-cert.json` atoms whose Z3 result is `unknown` into Lean 4 theorem files, checks them with Lake, and exports Mumei-compatible `.lean-cert.json` evidence.

There is currently no MCP server in this repository. Use the CLI scripts and Lake.

### Bootstrap and Build

Install the pinned toolchain:

```bash
elan toolchain install $(cat lean-toolchain)
```

Build:

```bash
mkdir -p generated/Generated
lake build
```

## Bridge Usage

Single certificate:

```bash
python scripts/bridge.py \
  --cert /path/to/module.proof-cert.json \
  --lean-cert-out out/module.lean-cert.json
```

Bundle:

```bash
python scripts/bridge.py \
  --bundle /path/to/std-proof-bundle.json \
  --lean-cert-out out/
```

Scan a Mumei checkout:

```bash
python scripts/bridge.py \
  --scan-unknown /path/to/mumei \
  --lean-cert-out out/ \
  --summary-json out/summary.json
```

Dry run:

```bash
python scripts/bridge.py \
  --scan-unknown /path/to/mumei \
  --lean-cert-out out/ \
  --no-build
```

## Test the Repository

Python bridge tests:

```bash
PYTHONPATH=scripts MUMEI_LEAN_SKIP_LIVE=1 python -m pytest -q
```

Lean library:

```bash
lake build
```

Live bridge checks when Lake is ready:

```bash
unset MUMEI_LEAN_SKIP_LIVE
PYTHONPATH=scripts python -m pytest -q
```

## Pipeline Details

The bridge performs:

1. Read `.proof-cert.json` or `std-proof-bundle.json`.
2. Collect `AtomCertificate` entries where `z3_check_result == "unknown"`.
3. Translate `requires` / `ensures` and simple `body_expr` terms into Lean theorem modules under `generated/`.
4. Run `lake build`.
5. Export `.lean-cert.json` with proved atoms marked `z3_check_result = "lean_verified"`.

## Repository Structure

| Path | Purpose |
| --- | --- |
| `lakefile.lean` | Lake config, Mathlib dependency, generated module target. |
| `lean-toolchain` | Pinned Lean toolchain. |
| `MumeiLean/` | Core Lean library, tactics, proof patterns, pilot proofs. |
| `scripts/bridge.py` | End-to-end bridge orchestrator. |
| `scripts/ingest_cert.py` | Certificate ingestion and Lean theorem generation. |
| `scripts/export_cert.py` | Lake log parsing and `.lean-cert.json` export. |
| `scripts/expr_translator.py` | Mumei expression to Lean proposition translation. |
| `tests/` | Python regression tests for bridge and translator. |
| `generated/` | Generated theorem namespace. |

## Common Validation

Before reporting success after bridge changes:

```bash
PYTHONPATH=scripts MUMEI_LEAN_SKIP_LIVE=1 python -m pytest -q
lake build
```

If generated theorem files were intentionally regenerated, inspect them before committing.
