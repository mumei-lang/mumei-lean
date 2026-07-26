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

## Live Generated Theorem Paths (11 total)

The bridge ships eleven live generated theorem paths. Each lowers a Z3 `unknown`
(or `spurious_candidate`) atom to a generated Lean theorem that builds with
`known_witness_used = false`:

1. `abs_saturating` — saturating i64 body semantics.
2. `bounded_mul_with_overflow_check` — nonlinear conjunction body semantics.
3. `constant_time_eq_flag` — crypto deterministic 0/1 witness.
4. `ff_zero_eq_zero` — finite-field equality via `MumeiLean.Algebra.ff_eq_refl`.
5. `verified_insertion_sort_ascending` — sort ascending preservation via `MumeiLean.Sort.insertion_sort_ascending_bridge`.
6. `poly_bound_monotone` — single non-conjunction nonlinear arithmetic (`result >= 0` over `x*x + 2*x + 1`) via `mumei_arith_deep`.
7. `exists_pivot_partition` — forall/exists quantifier alternation via `MumeiLean.Quantifiers.forall_exists_swap_of_finite`.
8. `sum_nonneg_inductive` — natural-number induction via `MumeiLean.AdvancedPatterns.int_nonnegative_induction_pattern`.
9. `rtgs_transfer_conservation` — RTGS balance conservation via `mumei_arith`.
10. `ff_mul_commutative` — finite-field commutativity (`ff_eq` over swapped `ff_mul` operands) via `MumeiLean.Algebra.ff_mul_comm_eq`.
11. `ff_mul_associative` — finite-field associativity (`ff_eq` over a re-associated `ff_mul` nesting) via `MumeiLean.Algebra.ff_mul_assoc_mod` + `ff_eq_refl`, selected by `translator_ir.bridge_pattern == "finite_field_associativity"`.

Focused pytest coverage for paths 9–11, Lake required:

```bash
cd /home/ubuntu/repos/mumei-lean
PATH="$HOME/.elan/bin:$PATH" python -m pytest tests/test_lean_bridge_e2e.py -q \
  -k "rtgs_transfer_conservation or finite_field_commutativity or finite_field_associativity"
```

Adversarial negative control for path 11: change the fixture `ensures` to an
operand order that is *not* the re-association of the body (e.g.
`ff_eq(result, ff_mul(b, ff_mul(a, c, p), p), p)`) and assert the rendered proof
falls back to `mumei_arith_deep` without citing `ff_mul_assoc_mod`
(`tests/test_ingest_cert.py::test_finite_field_associativity_requires_matching_operand_order`).

Focused pytest coverage for the three PR3 paths (6–8), Lake required:

```bash
cd /home/ubuntu/repos/mumei-lean
PATH="$HOME/.elan/bin:$PATH" python -m pytest tests/test_lean_bridge_e2e.py -q \
  -k "poly_bound_monotone or exists_pivot_partition or sum_nonneg_inductive"
```

Expected bridge assertions for each of the three fixtures
(`tests/fixtures/std_math_patterns_poly_bound.proof-cert.json`,
`tests/fixtures/std_list_exists_pivot_partition.proof-cert.json`,
`tests/fixtures/std_math_patterns_sum_nonneg.proof-cert.json`):

- `lake build` exits with status 0 and no `sorry` warning.
- Lean cert atom has `z3_check_result == "lean_verified"` and `status == "verified"`.
- `lean_metadata.known_witness_used is False`.
- Theorem names are `Generated.Std.Math.Patterns.poly_bound_monotone_correct`, `Generated.Std.List.exists_pivot_partition_correct`, and `Generated.Std.Math.Patterns.sum_nonneg_inductive_correct` respectively.

Non-Lake unit coverage:

```bash
cd /home/ubuntu/repos/mumei-lean
PYTHONPATH=scripts MUMEI_LEAN_SKIP_LIVE=1 python -m pytest \
  tests/test_ingest_cert.py tests/test_expr_translator.py \
  tests/test_export_cert.py tests/test_contract_vocabulary.py -q
```

## Adversarial Checks (negative controls)

A green live run only proves something if the same pipeline visibly *refuses* bad input.
Run these alongside the positive paths whenever promotion logic, the translator contract,
or `MumeiLean/CertWriter.lean` changes. All of them work on `/tmp` copies; never mutate
repo fixtures in place.

Always pass `-rs` to pytest for live runs so a silent `SKIPPED` (Lake not on `PATH`, or
`MUMEI_LEAN_SKIP_LIVE=1` still exported from an earlier command) cannot be mistaken for a pass:

```bash
PATH="$HOME/.elan/bin:$PATH" PYTHONPATH=scripts python -m pytest \
  tests/test_lean_bridge_e2e.py tests/test_cert_roundtrip.py -q -rs
```

### 1. Unprovable goal must not be promoted

Copy any body-semantics fixture and mutate `ensures` (and `translator_ir.theorem_goal`) so the
generated theorem cannot close — e.g. keep body `{ ff_mul(a, b, p) }` but claim
`ff_eq(result, ff_add(b, a, p), p)`. Re-run `scripts/bridge.py`.

Expected: `lake build` exits 1 with `unsolved goals`, the bridge exits non-zero, and the atom
stays `z3_check_result == "unknown"` with `lean_metadata.status == "manual_lemma_required"` and
`all_verified == false`. If it still exports `lean_verified`, promotion is rubber-stamping.

### 2. Stale translator contract must be rejected even when the proof builds

Make two `/tmp` copies of a fixture: one with `bridge_lemma_hash` reverted to an older catalog
hash, one with `translator_version` set to an older value. Run the bridge on each.

Expected for both: `lake build` still exits **0** (the Lean proof is fine) but the atom is *not*
promoted — `z3_check_result == "unknown"`, `status == "unknown"`,
`lean_metadata.status == "stale_translator"`, `all_verified == false`. Seeing the build succeed
while the atom is refused is the point: it isolates the trust gate from proof validity.
The gate lives in `scripts/export_cert.py` (`_translator_contract_current`,
`_lean_result_contract_current`, and the `stale_translator` branch of `_upgrade_atom_list`).

### 3. Native writer must not rewrite escalation metadata

`tests/fixtures/cert_roundtrip_driver.lean` marks *every* atom `ProofResult.verified`, so it only
covers the promoted direction. For the non-promoted direction, copy the driver to `/tmp` and swap
the result constructor:

```bash
sed 's/ProofResult.verified)/ProofResult.failed "negative control")/' \
  tests/fixtures/cert_roundtrip_driver.lean > /tmp/rt_neg_driver.lean
PATH="$HOME/.elan/bin:$PATH" lake env lean --run /tmp/rt_neg_driver.lean /tmp/cert.json
```

Build the input cert from `tests/fixtures/pilot_proof_cert.json` with
`z3_result_class="unknown"`, `escalation_reason="z3_unknown"`,
`logic_fragment_tags=["finite_field","nonlinear_arithmetic"]` on every atom.

Expected:
- Verified driver: `first_atom_z3 == "lean_verified"` while `z3_result_class`,
  `escalation_reason`, and `logic_fragment_tags` come back byte-identical to the input.
  (A writer that still does `z3ResultClass := ...` would report `z3_result_class == "lean_verified"` —
  that is the regression this guards.)
- Failed driver: every atom field-for-field identical to the input, `first_atom_z3 == "unknown"`.

Known non-issue: `first_atom_translator_version` comes back as `""` for `pilot_proof_cert.json`
because that fixture carries no `translator_version`; do not chase it.

## Timing Expectations

With a warm mathlib cache (`.lake` around 5 GB) the whole live suite finishes in well under a
minute — 23 tests in ~32s, full live `pytest -q` at 286 passed in ~41s, and `lake build` replays
from cache. The `bridge body-semantics E2E` CI job has historically taken ~45 min instead; that is
cold-cache `lake exe cache get` time, not a code regression. If a *local* run suddenly takes tens
of minutes, suspect a cache miss (check `lake exe cache get` and `mkdir -p generated/Generated`)
rather than the bridge.
