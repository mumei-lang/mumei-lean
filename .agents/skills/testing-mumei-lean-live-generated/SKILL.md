---
name: testing-mumei-lean-live-generated
description: Test mumei-lean live generated theorem bridge paths end-to-end, including mumei-agent propagation and stale translator gates.
---

## Devin Secrets Needed

None for local Lean bridge, Lake, pytest, or mumei-agent integration testing.

## When to Use

Use this when changes touch:

- `scripts/ingest_cert.py`, `scripts/expr_translator.py`, `scripts/bridge.py`, or `scripts/export_cert.py` live generated theorem output.
- `tests/test_bridge.py::test_body_semantics_bridge_e2e_exports_lean_verified` or body-semantics fixtures.
- mumei-agent Lean fallback merge/proliferate behavior that consumes `.lean-cert.json` output.
- Stale `translator_version` / `bridge_lemma_hash` trust gates.

This is a shell-only flow; do not record the desktop unless a separate GUI/dashboard is being tested.

## Setup

From the mumei-lean repo, make sure the pinned Lean toolchain is on PATH:

```bash
cd /home/ubuntu/repos/mumei-lean
export PATH="$HOME/.elan/bin:$PATH"
mkdir -p generated/Generated
```

For mumei-agent integration, point the agent at the local mumei-lean checkout:

```bash
export MUMEI_LEAN_REPO=/home/ubuntu/repos/mumei-lean
```

## Primary Live Generated Bridge Test

Run the focused live E2E test with Lake enabled:

```bash
cd /home/ubuntu/repos/mumei-lean
PATH="$HOME/.elan/bin:$PATH" \
  python -m pytest tests/test_bridge.py::test_body_semantics_bridge_e2e_exports_lean_verified -q
```

Expected assertions:

- Test exits zero and is not skipped. If it skips, check whether `lake` is missing or `MUMEI_LEAN_SKIP_LIVE=1` is set.
- `abs_saturating` exports `z3_check_result == "lean_verified"` and `status == "verified"`.
- `lean_metadata.lean_theorem_name == "Generated.Std.Math.Abs.abs_saturating_correct"`.
- `lean_metadata.known_witness_used is False`; `True` means the path used the known witness fallback rather than the live generated theorem.

## mumei-agent Propagation Test

Run the focused agent E2E path against the same checkout:

```bash
cd /home/ubuntu/repos/mumei-agent
PATH="$HOME/.elan/bin:$PATH" \
MUMEI_LEAN_REPO=/home/ubuntu/repos/mumei-lean \
  uv run pytest --run-integration -q \
  tests/test_lean_bridge_e2e.py::test_lean_fallback_upgrades_unknown_to_lean_verified \
  tests/test_lean_bridge_e2e.py::test_proliferate_lean_fallback_summary_json
```

Expected assertions:

- Both tests exit zero and are not skipped.
- The merged `publish_result.proof_certificate.atoms[]` record keeps Lean metadata from the emitted Lean cert.
- `known_witness_used is False` for the live generated `abs_saturating` atom.
- Summary JSON records the expected `lean_verified_count` for the published certificate.

## Critical Regression: Stale Metadata Gate

Run stale translator/hash checks whenever promotion logic or metadata copying changes:

```bash
cd /home/ubuntu/repos/mumei-lean
PATH="$HOME/.elan/bin:$PATH" \
  python -m pytest \
  tests/test_bridge.py::test_stale_source_contract_is_not_lean_verified \
  tests/test_bridge.py::test_stale_lean_result_contract_is_not_lean_verified -q
```

Expected assertions:

- Stale `translator_version` or `bridge_lemma_hash` keeps `z3_check_result == "unknown"`.
- `lean_metadata.status == "stale_translator"` and result metadata is not accepted as proven.

## Broader Confidence Checks

Use these before opening or updating a PR when time allows:

```bash
cd /home/ubuntu/repos/mumei-lean
PATH="$HOME/.elan/bin:$PATH" python -m pytest -q
PATH="$HOME/.elan/bin:$PATH" lake build

cd /home/ubuntu/repos/mumei-agent
PATH="$HOME/.elan/bin:$PATH" MUMEI_LEAN_REPO=/home/ubuntu/repos/mumei-lean \
  uv run pytest --run-integration -q
```


## Finite-Field Live Generated Bridge Test

Use this when validating live-generated theorem paths for algebra/finite-field atoms. This is shell-only testing; do not record the desktop.

First generate a fresh mumei proof certificate from the adjacent mumei checkout:

```bash
rm -rf /home/ubuntu/mumei-ff-e2e
mkdir -p /home/ubuntu/mumei-ff-e2e
cd /home/ubuntu/repos/mumei
LLVM_SYS_170_PREFIX=/usr/lib/llvm-17 LIBCLANG_PATH=/usr/lib/x86_64-linux-gnu \
  ./target/debug/mumei verify --proof-cert \
  --output /home/ubuntu/mumei-ff-e2e/finite_field.proof-cert.json \
  std/algebra/finite_field.mm
```

Expected mumei certificate assertions for `ff_zero_eq_zero`:

- `z3_check_result == "unknown"`
- `z3_result_class == "unknown"`
- `status == "unknown"`
- `logic_fragment_tag == "finite_field"`
- `spec_validation_result.status == "unknown_fragment"`
- `body_expr == "{ ff_zero(p) }"`
- `translator_ir.lowering_rules` includes `finite_field_lowering`

Then run the bridge with Lake enabled:

```bash
cd /home/ubuntu/repos/mumei-lean
PATH="$HOME/.elan/bin:$PATH" \
  python scripts/bridge.py \
  --cert /home/ubuntu/mumei-ff-e2e/finite_field.proof-cert.json \
  --out-dir /home/ubuntu/mumei-ff-e2e/generated \
  --lean-cert-out /home/ubuntu/mumei-ff-e2e/finite_field.lean-cert.json \
  --module-prefix Generated
```

Expected bridge assertions:

- `lake build` exits with status 0.
- Generated Lean contains `MumeiLean.Algebra.mumei_ff_zero p` and `MumeiLean.Algebra.ff_eq_refl 0 p`.
- Lean cert atom `ff_zero_eq_zero` has `z3_check_result == "lean_verified"` and `status == "verified"`.
- `lean_metadata.known_witness_used is False`.
- `lean_metadata.lean_theorem_name == "Generated.Std.Algebra.Finite_field.ff_zero_eq_zero_correct"`.

Focused pytest coverage:

```bash
cd /home/ubuntu/repos/mumei-lean
PYTHONPATH=scripts MUMEI_LEAN_SKIP_LIVE=1 python -m pytest \
  tests/test_bridge.py::test_main_dry_run_with_finite_field_body_semantics_fixture \
  tests/test_lean_bridge_e2e.py::test_finite_field_zero_eq_upgrades_unknown_to_lean_verified \
  -q
```

The Lake-marked finite-field test should run and pass when `lake` is available; if it skips unexpectedly, check that `lake` is on `PATH` and that the fixture drivers compile with the pinned Lean toolchain.
