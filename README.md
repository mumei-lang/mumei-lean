# mumei-lean

External **Lean 4** proof backend for the [mumei](https://github.com/mumei-lang/mumei)
formal verification language.

mumei verifies `requires`/`ensures` contracts automatically with the Z3 SMT
solver. For most atoms this is enough, but Z3 can return `unknown` on
contracts that lie beyond its decidable fragments — quantifier-heavy
properties, deep recursion, or domains like cryptographic primitives where a
hand-written proof is unavoidable.

`mumei-lean` is the *external complement*: it picks up those `unknown` atoms,
re-states them in Lean 4, lets you (or `mathlib4`) discharge the proof
obligation, and emits a mumei-compatible `.lean-cert.json` certificate that
the mumei resolver consumes through its existing
[Proof Certificate Chain (P5-A)](https://github.com/mumei-lang/mumei/blob/main/docs/PROOF_CERTIFICATE.md)
and `MUMEI_PROOF_BUNDLE` machinery (SI-5 Phase 3-C). The bridge now preserves
the typed Lean translator contract: `TranslatorIRMetadata`, binder mappings,
bridge lemma hashes, and manual lemma reasons move through ingestion, Lean
checking, and certificate export as auditable metadata.

> mumei's "fully automatic verification" philosophy is preserved. mumei-lean
> only steps in for the slice of contracts Z3 cannot close on its own, and the
> mumei compiler itself requires **zero changes** to consume the resulting
> certificates: they piggy-back on the existing 3-tier resolver lookup.

## Architecture in one picture

```mermaid
graph TD
    M["mumei verify --proof-cert"] -->|".proof-cert.json"| ML["mumei-lean"]
    M2["mumei build --emit verified-json"] -->|".verified.json"| ML
    ML -->|"Lean 4 theorem + tactic\n+ TranslatorIRMetadata"| LP["Lean Proof Check"]
    LP -->|".lean-cert.json\ntranslator_version + bridge_lemma_hash"| MR["mumei resolver\n(verify_import_certificate)"]
    MR -->|"mark_verified()"| MV["mumei verification pipeline"]
    AG["mumei-agent\n(proliferate / forge)"] -->|"Z3 unknown atoms"| ML
```

Full diagram and field-by-field schema in
[`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md), with the body-semantics
pipeline diagram in [`docs/BRIDGE_PIPELINE.md`](docs/BRIDGE_PIPELINE.md).
End-to-end usage and the mumei-side opt-in story live in
[`docs/INTEGRATION.md`](docs/INTEGRATION.md). The NLAH-style escalation
contract is documented in
[`docs/BRIDGE_HARNESS_SPEC.md`](docs/BRIDGE_HARNESS_SPEC.md), and the
artifact-level Lean verifier contract for `.proof-cert.json`, generated Lean,
`lake build`, `.lean-cert.json`, and summary JSON is documented in
[`docs/LEAN_HARNESS_CONTRACT.md`](docs/LEAN_HARNESS_CONTRACT.md).

## Repository layout

```
mumei-lean/
├── lakefile.lean          # Lean 4 build config (mathlib4 dependency)
├── lean-toolchain         # Pinned Lean toolchain (mathlib4-compatible)
├── MumeiLean.lean         # Public umbrella module
├── MumeiLean/
│   ├── Basic.lean         # Core types: MumeiContract, ProofResult
│   ├── CertParser.lean    # Lean.Json-based .proof-cert.json parser
│   ├── TheoremGen.lean    # Helpers used by generated Lean theorems
│   ├── Verify.lean        # Per-atom proof outcome helpers
│   ├── CertWriter.lean    # Lean.Json-based .lean-cert.json writer
│   ├── Pilot.lean         # Hand-proven pilot theorems (PR 3)
│   ├── Ownership.lean     # Ownership Transfer Protocol state proof
│   ├── Patterns.lean      # Reusable SC proof patterns
│   ├── Algebra.lean       # mathlib-backed finite-field/group helpers
│   ├── Crypto.lean        # Hash, signature, and crypto primitive proof patterns
│   ├── AdvancedPatterns.lean  # Reusable domain proof patterns
│   ├── StdMathAbs.lean    # std/math_abs Lean witness proofs
│   └── Settlement.lean    # RTGS settlement and balance proofs
├── scripts/
│   ├── expr_translator.py # mumei contract expr → Lean Prop translator
│   ├── ingest_cert.py     # .proof-cert.json → generated/*.lean
│   ├── export_cert.py     # lake build log + cert → .lean-cert.json
│   ├── bridge.py          # End-to-end orchestrator (humans run this)
│   ├── build.sh           # Optimized full Lake build
│   └── build-target.sh    # Optimized targeted Lake build
├── tests/                 # pytest suite for the Python bridge
├── docs/
│   ├── ARCHITECTURE.md
│   ├── BRIDGE_PIPELINE.md
│   ├── BRIDGE_HARNESS_SPEC.md
│   ├── LEAN_HARNESS_CONTRACT.md
│   ├── LEAN_TRANSLATOR_SPEC.md
│   ├── MATHLIB4_INTEGRATION.md
│   ├── LEAN_EXECUTABLE.md
│   └── INTEGRATION.md
└── .github/workflows/ci.yml
```

## Quick start

### 1. Install Lean 4

The repo pins its toolchain in
[`lean-toolchain`](./lean-toolchain). The easiest path is `elan`:

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
elan toolchain install $(cat lean-toolchain)
```

### 2. Run the bridge against a mumei certificate

```bash
# Single per-module certificate
python scripts/bridge.py \
    --cert /path/to/some_module/.proof-cert.json \
    --lean-cert-out out/.lean-cert.json

# Whole std bundle
python scripts/bridge.py \
    --bundle /path/to/std-proof-bundle.json \
    --lean-cert-out out/

# Bulk-scan a mumei checkout for unknown atoms
python scripts/bridge.py \
    --scan-unknown /path/to/mumei-checkout \
    --lean-cert-out out/ \
    --no-build         # quick dry run (skip `lake build`)
```

The orchestrator:

1. Reads the input cert(s) (auto-detects `ProofCertificate` vs
   `ProofBundle`).
2. Emits one Lean theorem per `unknown` atom into `generated/`
   (filenames mirror mumei module paths).
3. Runs `lake build` to discharge those theorems (anything left as
   `sorry` is treated as a failure).
4. Validates the translator contract metadata attached to each atom,
   including `translator_version`, `binder_mapping`, and `bridge_lemma_hash`.
5. Writes a mumei-compatible `.lean-cert.json` whose successful atoms
   carry `z3_check_result = "lean_verified"` and the same typed translator
   metadata required by downstream resolver validation.

Drop the resulting `.lean-cert.json` next to the source module (tier 1
of the mumei resolver), or roll it into a bundle and point
`MUMEI_PROOF_BUNDLE` at it (tier 3) — see
[`docs/INTEGRATION.md`](docs/INTEGRATION.md).

### 3. Run the test suite

```bash
python -m pytest -v       # Python bridge
lake build                # Lean library
```

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
4. **Scope is intentionally small.** The expression translator handles
   arithmetic comparisons, boolean connectives, integer literals,
   conditionals, compact `match x { ... }` expressions, typed bounded and
   unbounded quantifiers, `arr[i]`, list/string literals, and known calls.
   Finite-field helpers (`ff_add`, `ff_mul`, etc.) and group-theory helpers
   (`group_mul`, etc.) route through `MumeiLean.Algebra`; cryptographic
   primitives (`hash`, `signature_verify`, etc.) route through
   `MumeiLean.Crypto`; higher-order predicates (`holds(P, x)`) lower to
   direct Lean application (`P x`). If a certificate carries a supported
   `body_expr`, the bridge emits a Lean `def <atom>Result` plus an `h_body`
   equality so the theorem can prove postconditions from body semantics
   instead of only `requires → ensures`. Anything else is preserved verbatim
   and tagged `-- TODO: unproven` or falls back to the contract-only proof path.
   Current limitations: unknown function calls and domain-specific
   invariants that need bespoke lemmas still require a hand-written
   witness.
5. **Targeted at Z3-`unknown`.** `mumei-lean` is *not* a replacement for
   Z3. Use it for the atoms Z3 cannot close (cryptographic correctness,
   abstract-algebraic invariants, etc.).

## License

Apache-2.0; see [`LICENSE`](./LICENSE).
