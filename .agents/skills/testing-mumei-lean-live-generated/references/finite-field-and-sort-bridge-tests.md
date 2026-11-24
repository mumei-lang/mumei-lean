# Finite-field and sort live generated bridge tests

Read this when validating live generated theorem paths for finite-field/algebra atoms or the sort ascending-preservation path, including fresh mumei certificate generation and expected outputs.

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


## Sort Ascending-Preservation Live Generated Bridge Test

Use this when validating the 5th live-generated theorem path for sort ascending-preservation obligations. This path handles atoms where Z3 produces a spurious counterexample (`z3_check_result == "spurious_candidate"`) due to Array + forall quantifier interaction.

First generate a fresh mumei proof certificate from the adjacent mumei checkout:

```bash
rm -rf /home/ubuntu/mumei-sort-e2e
mkdir -p /home/ubuntu/mumei-sort-e2e
cd /home/ubuntu/repos/mumei
LLVM_SYS_170_PREFIX=/usr/lib/llvm-17 LIBCLANG_PATH=/usr/lib/x86_64-linux-gnu \
  ./target/debug/mumei verify --proof-cert --escalate-lean \
  --output /home/ubuntu/mumei-sort-e2e/sort_ascending.proof-cert.json \
  tests/fixtures/sort_ascending.mm
```

Expected mumei certificate assertions for `verified_insertion_sort_ascending`:

- `z3_check_result == "spurious_candidate"`
- `z3_result_class == "sat"`
- `status == "failed"`
- `escalation_reason == "spurious_candidate"`
- `logic_fragment_tag == "quantifier_alternation"`
- `ensures` contains `forall(i, 0, result - 1, arr[i] <= arr[i + 1])`

Then run the bridge with Lake enabled:

```bash
cd /home/ubuntu/repos/mumei-lean
PATH="$HOME/.elan/bin:$PATH" \
  python scripts/bridge.py \
  --cert /home/ubuntu/mumei-sort-e2e/sort_ascending.proof-cert.json \
  --out-dir /home/ubuntu/mumei-sort-e2e/generated \
  --lean-cert-out /home/ubuntu/mumei-sort-e2e/sort_ascending.lean-cert.json \
  --module-prefix Generated
```

Expected bridge assertions:

- `lake build` exits with status 0.
- Generated Lean contains `MumeiLean.Sort.insertion_sort_ascending_bridge`.
- Lean cert atom `verified_insertion_sort_ascending` has `z3_check_result == "lean_verified"` and `status == "verified"`.
- `lean_metadata.known_witness_used is False`.
- `lean_metadata.lean_theorem_name == "Generated.Std.List.verified_insertion_sort_ascending_correct"`.

Focused pytest coverage:

```bash
cd /home/ubuntu/repos/mumei-lean
PYTHONPATH=scripts MUMEI_LEAN_SKIP_LIVE=1 python -m pytest \
  tests/test_bridge.py::test_sort_ascending_ingest_generates_bridge_theorem \
  tests/test_lean_bridge_e2e.py::test_sort_ascending_upgrades_spurious_to_lean_verified \
  -q
```

The Lake-marked sort ascending test should run and pass when `lake` is available; if it skips unexpectedly, check that `lake` is on `PATH` and that the fixture drivers compile with the pinned Lean toolchain.
