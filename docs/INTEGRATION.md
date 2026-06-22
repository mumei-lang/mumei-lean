# Integration with mumei / mumei-agent

> How to wire mumei-lean into an existing mumei project without
> modifying the mumei compiler itself.


## Unknown obligation bridge contract

The only promoted Lean path is:

1. Scan mumei proof certificates for atoms whose `z3_result_class == "unknown"` or `z3_check_result == "unknown"`.
2. Translate each candidate to generated Lean with `translator_ir` metadata, `logic_fragment_tags`, and any `manual_lemma_reason` preserved.
3. Run `lake build` for the generated target unless the command is explicitly in `--no-build` dry-run mode.
4. Export `.lean-cert.json` with `lean_result_metadata` and the top-level atom fields `translator_version` and `bridge_lemma_hash`.
5. mumei accepts `lean_verified` only when those fields match its current constants; mismatches are `stale_translator` and must not be treated as proven.

Field handling is fixed:

| Field | Meaning |
| --- | --- |
| `z3_result_class` | Normalized solver class used for routing; only `unknown` is a Lean escalation candidate. |
| `escalation_reason` | Why Z3 could not close the obligation, such as timeout/resource limits, quantified reasoning, recursion, or a domain-specific fragment. |
| `logic_fragment_tags` | Ordered fragment tags used for bridge lemma selection, metrics, and mumei certificate parity. |
| `translator_ir` | Typed lowering contract emitted into generated Lean and copied into `.lean-cert.json` for mumei-side auditing. |
| `manual_lemma_reason` | Stable reason a generated theorem needs human lemma work; dry runs should emit `manual_lemma_required`, not `lean_verified`. |
| `stale_translator` | mumei-side rejection when `translator_version` or `bridge_lemma_hash` differs from the current mumei/mumei-lean contract. |

Current contract constants are `translator_version = mumei-lean-translator-ir-v1` and `bridge_lemma_hash = a8fd0b115fd29a6e87190bd041dbd5ab7a09ec89af6ac5b10ef152a1a0c0f643`.

## Bridge acceptance invariant

The bridge is a complement for Z3 `unknown` obligations only. A candidate can be promoted to `lean_verified` when all of these hold:

1. The source atom was routed from `z3_result_class == "unknown"` or `z3_check_result == "unknown"`.
2. Generated Lean builds successfully without unresolved manual-lemma placeholders.
3. The exported atom and `lean_result_metadata` both carry the current `translator_version`.
4. The exported atom and `lean_result_metadata` both carry the current `bridge_lemma_hash`.

If either `translator_version` or `bridge_lemma_hash` differs from the current mumei/mumei-lean contract, the failure condition is `stale_translator`. `sat`, `unsat`, parser failures, audit/spec issues, and ordinary mumei-agent findings are never upgraded by this bridge.

## End-to-end workflow

1. **Generate a mumei proof certificate** for the module(s) you care
   about:

   ```bash
   # In a mumei project
   mumei verify --emit proof-cert src/math.mm
   ```

   This drops `.proof-cert.json` next to the source. Atoms Z3 could not
   close show up with `"z3_check_result": "unknown"`. Certificates produced
   after PR #23 also carry typed translator contract metadata such as
   `translator_version`, `binder_mapping`, `bridge_lemma_hash`,
   `manual_lemma_reason`, and `translator_ir`.

   For P8-C escalation routing, mumei can emit the narrower escalation bundle
   shape instead of a full proof certificate:

   ```bash
   mumei verify \
       --emit escalation-bundle \
       --output out/math.escalation-bundle.json \
       src/math.mm
   ```

   The bundle contains only Lean candidates under `candidates[]`; each candidate
   preserves the proof identity and routing metadata the bridge needs:

   ```json
   {
     "summary": {
       "candidate_count": 1,
       "by_reason": {"z3_unknown": 1},
       "by_logic_fragment": {"linear_arithmetic": 1},
       "by_z3_result_class": {"unknown": 1}
     },
     "candidates": [
       {
         "name": "abs_saturating",
         "z3_check_result": "unknown",
         "z3_result_class": "unknown",
         "escalation_reason": "z3_unknown",
         "logic_fragment_tags": ["linear_arithmetic", "std_math_abs"],
         "proof_hash": "...",
         "translator_version": "...",
         "binder_mapping": {"result": "result"},
         "bridge_lemma_hash": "...",
         "manual_lemma_reason": null,
         "translator_ir": {"sort": "postcondition"}
       }
     ]
   }
   ```

2. **Run the bridge** in a checkout of `mumei-lean`:

   ```bash
   python scripts/bridge.py \
       --cert /path/to/.proof-cert.json \
       --lean-cert-out /tmp/math.lean-cert.json \
       --lean-version "$(lake --version | head -n1)"
   ```

   Or run the P8-C escalation bundle directly:

   ```bash
   python scripts/bridge.py \
       --escalation-bundle out/math.escalation-bundle.json \
       --lean-cert-out out/math.lean-cert.json
   ```

   This regenerates `generated/`, runs `lake build`, validates the translator
   contract metadata for the generated Lean theorem, and emits the
   mumei-compatible certificate.

3. **Consume the certificate** in mumei. Two routes exist (both
   already supported by `mumei-core/src/resolver.rs::verify_import_certificate`):

   * **Tier 1 — local certificate.** Replace the original
     `.proof-cert.json` next to the source module with the new
     `.lean-cert.json` (rename to `.proof-cert.json`). The resolver
     picks it up unchanged.

     ```bash
     cp /tmp/math.lean-cert.json src/.proof-cert.json
     ```

   * **Tier 3 — bundle fallback.** Bake the Lean-augmented certificate
     into the project's `std-proof-bundle.json` (the same artefact
     produced by `scripts/bundle_std_certs.py` in the mumei repo) and
     export `MUMEI_PROOF_BUNDLE`:

     ```bash
     export MUMEI_PROOF_BUNDLE=/path/to/std-proof-bundle.json
     mumei verify src/main.mm
     ```

     The resolver's 3-tier search will fall through to the bundle when
     no local `.proof-cert.json` exists.

## What does *not* change in mumei

* No mumei source file is modified.
* The mumei compiler keeps treating Lean results as proof-bearing only when
  the returned `translator_version` and `bridge_lemma_hash` match the current
  translator contract. Mismatches are reported as `stale_translator` so the
  obligation can be regenerated instead of silently reusing stale proof text.
* The `"lean_verified"` value is still forward-compatible for older mumei
  checkouts: versions that do not recognise it demote the atom to unproven
  rather than trusting it.

## Working with bundles

Bundles let downstream projects share a single Lean-augmented
certificate set across many modules. Keep translator contract fields in the
bundle unchanged; downstream resolvers use them for stale-translator detection.
Typical pipeline:

```bash
# 1. Generate per-module mumei certs (existing mumei flow).
mumei verify --emit proof-cert std/

# 2. Use mumei-lean to upgrade unknown atoms.
python scripts/bridge.py \
    --scan-unknown /path/to/mumei \
    --lean-cert-out /tmp/lean-certs/

# 3. Re-bundle (existing mumei script).
python /path/to/mumei/scripts/bundle_std_certs.py \
    --certs-dir /tmp/lean-certs \
    --output /path/to/std-proof-bundle.json
```

`bridge.py --scan-unknown <mumei-repo>` walks `<mumei-repo>/std/certs/`
and only re-emits certificates that contain at least one `unknown`
atom; everything else is left untouched.

## P8-C escalation bundle metadata

`mumei --emit escalation-bundle` is the preferred handoff when the caller only
wants Lean candidates, not a full proof-certificate pass-through. `scripts/ingest_cert.py`
detects the `"candidates"` envelope and treats each candidate like an atom whose
`z3_check_result == "unknown"` or whose `escalation_reason` explicitly routes it
to Lean.

Field usage:

| Field | Bridge usage |
|---|---|
| `z3_result_class` | Normalized solver class in `lean_metadata.z3_result_class` and summary metrics. |
| `escalation_reason` | Routing reason copied into generated theorem comments and `lean_metadata.diagnostics`. |
| `logic_fragment_tag` / `logic_fragment_tags` | Proof-strategy and mathlib-import selection hints; also emitted in diagnostics. |
| `translator_version` | Must match the bridge translator version before a `lean_verified` result is trusted downstream. |
| `binder_mapping` | Auditable Mumei→Lean variable mapping preserved in generated theorem metadata. |
| `bridge_lemma_hash` | Stale-bridge guard used by the mumei resolver when accepting Lean certificates. |
| `manual_lemma_reason` | Prevents silent promotion when the translator knows a hand-written lemma is required. |
| `translator_ir` | Typed lowering audit trail: obligation sort, binders, theorem goal, provenance span, lowering rules. |

Recommended CI shape:

```bash
mumei verify \
    --emit escalation-bundle \
    --output out/module.escalation-bundle.json \
    src/module.mm

python scripts/bridge.py \
    --escalation-bundle out/module.escalation-bundle.json \
    --lean-cert-out out/module.lean-cert.json \
    --summary-json out/module.lean-summary.json
```

If `manual_lemma_reason` is present or translation is partial, the bridge must
keep the atom unpromoted (`z3_check_result` remains `unknown`) and report the
reason in `lean_metadata.diagnostics`; it should not emit a false
`lean_verified` result.

## Bulk scanning (CI / observability)

For dashboarding which mumei modules still rely on Lean to discharge
their obligations, pair `--scan-unknown` with `--summary-json` and
`--no-build`:

```bash
python scripts/bridge.py \
    --scan-unknown /path/to/mumei \
    --out-dir out/generated \
    --lean-cert-out out/lean-certs \
    --summary-json out/scan-summary.json \
    --no-build
```

The summary JSON has the shape

```json
{
  "total_unknown": 5,
  "modules": [
    {"module": "std/list", "unknown_count": 3, "atoms": ["a", "b", "c"]},
    {"module": "std/math", "unknown_count": 2, "atoms": ["d", "e"]}
  ]
}
```

Useful properties:

* `total_unknown` is the number of atoms with `z3_check_result == "unknown"`
  ingested into Lean for this scan, *not* the count of certificates touched.
* Modules are grouped by the certificate's `module` key (e.g. the bundle
  shape's per-namespace key), so bundle inputs collapse naturally into
  per-namespace stats.
* The file is **always written** when `--summary-json` is set, even if
  the scan finds zero unknown atoms (the payload is
  `{"total_unknown": 0, "modules": []}`). This keeps CI artifact paths
  deterministic.

The `scan-unknown` job in `.github/workflows/ci.yml` runs this exact
command against the upstream `mumei-lang/mumei` checkout on every PR
and uploads `out/scan-summary.json` plus the regenerated
`out/lean-certs/` as a workflow artifact named `scan-unknown-summary`.
The job is informational (`continue-on-error: true`) so transient
upstream-repo issues do not block PRs.

## Working with mumei-agent

`mumei-agent`'s autonomous proliferation loop discovers gaps in
`std/`. When the agent's `mumei verify` step ends with `unknown` atoms,
the recommended path is:

1. Have `mumei-agent` emit the proof certificate as it does today.
2. Schedule a follow-up `mumei-lean` run (e.g. via
   `python scripts/bridge.py --cert <gen-cert>`) that turns the
   `unknown` atoms into Lean theorems for human / mathlib4 proofs while
   preserving `TranslatorIRMetadata`, binder mappings, and bridge lemma hashes.
3. Once `lake build` succeeds, the resulting `.lean-cert.json`
   feeds back into the `MUMEI_PROOF_BUNDLE` distributed by
   `homebrew-mumei` (SI-5 Phase 3-C).

Because the certificate format stays identical, no `mumei-agent`
strategy or prompt has to be aware of Lean. The bridge is a strict
post-processing pass.

## CI suggestions

The repo's `.github/workflows/ci.yml` runs the Python test suite and
`lake build`. Recommended additions for downstream projects:

* Cache `~/.elan` and the Lake build directory keyed on
  `lean-toolchain` + `lakefile.lean` to keep mathlib4 builds fast.
* Run `python -m pytest` on every PR to guard the bridge logic.
* Run `lake env lean --version` to record the exact toolchain in CI
  logs (and to embed via `--lean-version` in any released
  certificates).

## Troubleshooting

| Symptom                                                                  | Likely cause / fix                                                                                                |
|--------------------------------------------------------------------------|-------------------------------------------------------------------------------------------------------------------|
| `bridge.py` reports "no certificates with unknown atoms found"           | The mumei project has no `unknown` atoms — nothing for Lean to prove.                                             |
| `lake` is not on PATH                                                    | Install Lean 4 via `elan` (see `README.md`); `bridge.py` falls back to a conservative cert otherwise.             |
| `lake build` succeeds but `lean_verified` count is 0                     | The generated theorems still contain `sorry`. Provide manual proofs in `MumeiLean/...` or under `generated/`.     |
| mumei reports `stale_translator` for a Lean-verified atom                 | The certificate's `translator_version` or `bridge_lemma_hash` no longer matches the current translator. Regenerate the Lean theorem from a fresh `.proof-cert.json`. |
| `MUMEI_PROOF_BUNDLE` warnings on the mumei side                          | The bundle file is missing or unreadable; double-check the path. Local-tier certs always win regardless.          |
