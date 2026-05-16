# Integration with mumei / mumei-agent

> How to wire mumei-lean into an existing mumei project without
> modifying the mumei compiler itself.

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

2. **Run the bridge** in a checkout of `mumei-lean`:

   ```bash
   python scripts/bridge.py \
       --cert /path/to/.proof-cert.json \
       --lean-cert-out /tmp/math.lean-cert.json \
       --lean-version "$(lake --version | head -n1)"
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
