# Development and Build Guide

### 3. Run the test suite

```bash
python -m pytest -v                         # Python bridge
MUMEI_LEAN_SKIP_LIVE=1 python -m pytest -q  # Skip live Lake-backed tests
lake build                                  # Lean library
```

Bridge E2E pytest coverage for the body-semantics path requires `lake` on
`PATH` and the pinned Lean toolchain installed:

```bash
python -m pytest \
    tests/test_lean_bridge_e2e.py \
    tests/test_bridge.py \
    -v \
    --run-integration \
    -k "lake_available"
```

`tests/test_lean_bridge_e2e.py` now runs the live generated theorem paths when
Lake is available instead of being globally skipped. The fixtures generate
`generated/Generated/Std/Math/Abs.lean`,
`generated/Generated/Std/Math/Patterns.lean`,
`generated/Generated/Std/Crypto/Primitives.lean`, and
`generated/Generated/Std/Algebra/Finite_field.lean`; all export
`z3_check_result = "lean_verified"` with `known_witness_used = false`.

The narrow smoke command used by CI for the `std_math_abs` fixture is:

```bash
mkdir -p out
python scripts/bridge.py \
    --cert tests/fixtures/std_math_abs.proof-cert.json \
    --out-dir generated \
    --lean-cert-out out/std_math_abs.lean-cert.json
python - <<'PY'
import json
payload = json.load(open("out/std_math_abs.lean-cert.json"))
atom = next(a for a in payload["atoms"] if a["name"] == "abs_saturating")
assert atom["z3_check_result"] == "lean_verified", atom
PY
```

### Lean fallback contract

The live-generated paths share one contract with mumei-agent docs:

1. Live-generated theorem paths: `Generated.Std.Math.Abs.abs_saturating_correct`
   in `generated/Generated/Std/Math/Abs.lean`,
   `Generated.Std.Math.Patterns.bounded_mul_with_overflow_check_correct` in
   `generated/Generated/Std/Math/Patterns.lean`,
   `Generated.Std.Crypto.Primitives.constant_time_eq_flag_correct` in
   `generated/Generated/Std/Crypto/Primitives.lean`,
   `Generated.Std.Algebra.Finite_field.ff_zero_eq_zero_correct` in
   `generated/Generated/Std/Algebra/Finite_field.lean`, and the sort
   ascending-preservation path (`verified_insertion_sort_ascending`) which
   lowers to `MumeiLean.Sort.insertion_sort_ascending_bridge` backed by
   mathlib's `List.Sorted`. When these modules build cleanly, their atoms
   record `known_witness_used = false` and may be promoted to `lean_verified`.
2. Known-witness fallback: if generated theorem attribution cannot be used but
   the committed witness still validates, the bridge records
   `lean_module = "MumeiLean.StdMathAbs"`, `known_witness_used = true`, and
   preserves the fallback as explicit metadata rather than pretending the
   live-generated path passed.
3. Failure classification is stable: `lake_missing` means Lake/toolchain is
   unavailable; `partial_translation` means the translator could not emit a
   complete proof obligation; `stale_translator` means `translator_version` or
   `bridge_lemma_hash` no longer matches the current contract. None of these may
   be exported as `lean_verified`.

For dry-run translation or source inspection, generated files can still be
written anywhere with `--no-build`:

```bash
python scripts/bridge.py \
    --cert tests/fixtures/std_math_abs.proof-cert.json \
    --out-dir /tmp/generated \
    --no-build
```
- If a CI runner lacks Lake or mathlib cache, set `MUMEI_LEAN_SKIP_LIVE=1` for
  non-live pytest, or run the bridge with `--no-build --no-export` to validate
  ingestion/translation shape without claiming `lean_verified`.

## Building

### Quick Build (Recommended)

Use the optimized build script for faster builds:

```bash
./scripts/build.sh
```

This script:

- Uses `LEAN_NUM_THREADS` for parallel compilation with all available CPU cores
- Fetches precompiled mathlib4 cache to avoid recompiling the entire library
- Performs incremental builds when possible

### Manual Build

For manual control:

```bash
# Update dependencies and fetch mathlib4 cache
lake update -R
lake exe cache get

# Build with parallel jobs (adjust number based on your CPU)
LEAN_NUM_THREADS=8 lake build
```

### Building Specific Targets

To build only specific modules (faster for development):

```bash
# Build only MumeiLean library (excludes Generated)
./scripts/build-target.sh MumeiLean

# Build specific module
./scripts/build-target.sh MumeiLean.Basic

# Build only Generated library
./scripts/build-target.sh Generated
```

### Performance Notes

- The first build will take longer as it downloads and compiles dependencies
- Subsequent builds are much faster due to Lake's incremental compilation
- The `.lake` directory contains build cache - do not delete it unless necessary
- mathlib4 is pinned to v4.15.0 for stability

## Design constraints (read me before extending)

1. **Typed translator contract preservation.** The bridge treats
   `TranslatorIRMetadata`, `binder_mapping`, `bridge_lemma_hash`,
   `manual_lemma_reason`, and `translator_version` as part of the proof
   contract, not as display-only fields.
2. **No mumei changes required.** mumei-lean is opt-in and ships
   exclusively over the existing certificate chain. The mumei compiler
   keeps treating any `z3_check_result != "unsat"` as unproven, so the
   new `"lean_verified"` value is forward-compatible.
3. **Python is the production bridge today.** The end-to-end JSON ↔ Lean
   source translation still lives in Python, while `MumeiLean.CertParser`
   and `MumeiLean.CertWriter` are implemented Lean.Json-based native
   parser/writer modules for downstream tooling that wants a pure Lean path.
4. **Scope is intentionally small.** The expression translator covers a fixed
   surface — arithmetic/boolean/comparison operators, literals, conditionals,
   compact `match`, typed quantifiers, array access, and known helper/domain
   calls — and emits body-semantics theorems when a certificate carries a
   supported `body_expr`. Finite-field, group-theory, and crypto helpers route
   through `MumeiLean.Algebra` / `MumeiLean.Crypto`; anything unsupported is
   preserved verbatim and gated for a hand-written witness. The full supported
   surface and current limitations are documented in
   [`docs/ARCHITECTURE.md`](./ARCHITECTURE.md).
5. **Targeted at Z3-`unknown`.** `mumei-lean` is *not* a replacement for
   Z3. Use it for the atoms Z3 cannot close (cryptographic correctness,
   abstract-algebraic invariants, etc.).
