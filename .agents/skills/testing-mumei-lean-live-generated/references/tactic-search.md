# Automatic tactic search (spec §12) testing

Read this when changes touch `scripts/tactic_search.py`, the `residual` / `build_failure` bridge stages, `MumeiLean/Tactics.lean`, or `lean_result_metadata.tactic_search`, including the mumei CLI pipeline, no-false-promotion matrix, benchmarks, provenance and artifact hygiene.

## Automatic Tactic Search (spec §12) Testing

Use this when changes touch `scripts/tactic_search.py`, the `residual` / `build_failure` stages in
`scripts/bridge.py`, `MumeiLean/Tactics.lean` (`mumei_field`, `mumei_ff_mod`), or the
`lean_result_metadata.tactic_search` fields.

Shell-only flow — do not record the desktop.

### Full pipeline through the mumei CLI

```bash
cd /home/ubuntu/repos/mumei
MUMEI_LEAN_PATH=$HOME/repos/mumei-lean PATH="$HOME/.elan/bin:$PATH" \
  ./target/debug/mumei verify --proof-cert --escalate-lean \
  --output /tmp/out.proof.json std/algebra/finite_field.mm
```

Expected stdout markers: `Z3 returned unknown for atom ...` for every escalated atom,
`tactic search (build_failure) adopted \`<tactic>\` for atom <name>`,
`lake build ... exited with status 0`, then one `lean_verified: <atom>` line per promoted atom.

Caveats learned the hard way:

- Always pass `--output /tmp/...`; without it the CLI drops `<module>.proof.json` **and**
  `cross_spec.json` into the mumei repo root. `benchmarks/run_benchmarks.py` drops them too — delete
  them and re-check `git status --short` after every run.
- Before mumei PR #482 the CLI (escalation-bundle) cert exposed tactic-search provenance only as the
  diagnostics string `tactic_search_adopted=<id>`; the structured fields were visible only in a
  direct `python scripts/bridge.py --cert <cert> --out-dir <tmp> --lean-cert-out <tmp>` run. Since
  #482 both paths carry them — see "CLI-side tactic-search provenance" below.
- A full warm `bridge.py` run over one finite-field cert takes ~5-10s; a cold `lake build` a few minutes.

### Adversarial "no false promotion" matrix

Copy a fixture cert (e.g.
`tests/fixtures/std_algebra_finite_field_ff_mul_add_distributive.proof-cert.json`) to /tmp and mutate
the copy — never the fixture in-tree. Run `bridge.py --cert <copy> --out-dir /tmp/... --lean-cert-out /tmp/...`
and assert the atom stays `z3_check_result == "unknown"` for each case:

| Mutation / flag | Expected |
|---|---|
| `ensures` (+ `translator_ir.theorem_goal`) made mathematically false | `tactic_search.exhausted == true`, `adopted_tactic == null`, `lean_metadata.status == "manual_lemma_required"` |
| `translator_version` → `...-ir-v1`, or `bridge_lemma_hash` → junk | search still adopts and `lake build` exits 0, but `lean_metadata.status == "stale_translator"` |
| `--no-tactic-search` | no `tactic search` stdout line, no `tactic_search` key in `lean_metadata` |
| `--tactic-search-timeout 1` | `timed_out == true`, `adopted_tactic == null` |
| `env PATH=/usr/bin:/bin` (no `lake`) | `lake build ... status 127`, exit 0, no `tactic_search` metadata |

Determinism: run the same unmutated invocation twice into distinct out dirs and compare
`tactic_search.stage`, `adopted_tactic` and the whole `candidates_tried` list — they must be identical.

Probe hygiene: probes must exist only at `mumei-lean/.tactic_search/probe.lean`, which
`git check-ignore -v .tactic_search/` must report as ignored; nothing may land in `generated/`.

### Benchmark reporting (mumei side)

```bash
cd /home/ubuntu/repos/mumei
MUMEI_LEAN_PATH=$HOME/repos/mumei-lean PATH="$HOME/.elan/bin:$PATH" \
  python3 benchmarks/run_benchmarks.py --json /tmp/bench.json
```

Takes ~5-15 min. Assert per-category `escalated_atoms`, `lean_verified_atoms`,
`lean_discharge_rate == 1.0`, `tactic_search_adopted` and a numeric `avg_lean_solver_time_s`
(`SKIP` means the bridge was never invoked — usually a missing `MUMEI_LEAN_PATH`/`lake` on PATH).
Afterwards `git checkout docs/BENCHMARK_RESULTS.md`, since the script appends a run entry.

If `LEAN_TRANSLATOR_VERSION` / `LEAN_BRIDGE_LEMMA_HASH` in
`mumei-core/src/verification/types.rs` drift from the mumei-lean values, every escalation is rejected
as `stale_translator` and discharge rates silently drop to 0 — check those two constants first when
promotions unexpectedly disappear.

### CLI-side tactic-search provenance (mumei `LeanResultMetadata`)

Since mumei PR #482 the CLI escalation path preserves the bridge's structured provenance, so you can
assert it directly on `./<stem>.proof.json` written by
`mumei verify --proof-cert --escalate-lean` — you no longer need a direct `bridge.py --cert` run to
see it. Per atom, `lean_result_metadata` carries `known_witness_used`, `lean_solver_time_s` and a
`tactic_search` object (`stage`, `adopted_tactic`, `candidates_tried`, `search_time_s`, `exhausted`,
`timed_out`, `supersedes_manual_lemma_reason`). All are
`#[serde(default, skip_serializing_if = "Option::is_none")]`, so atoms that needed no search simply
omit `tactic_search` rather than emitting `null` — assert absence, not `null`.

These fields are **provenance only**. Promotion is decided solely by
`lean_candidate_metadata_is_current()` in `src/commands/verify.rs`: candidate `translator_version`
and `bridge_lemma_hash` must equal the constants in `mumei-core/src/verification/types.rs`, and the
metadata must have `status == "lean_verified"`, a non-empty `theorem_name`, and matching
version/hash inside the metadata. When testing new metadata fields, always confirm the gate does not
read them.

#### Stub-bridge injection harness (fastest way to attack the trust boundary)

`MUMEI_LEAN_PATH` may point at any directory containing `scripts/bridge.py`, so a ~40-line stub that
echoes the escalation bundle back with `z3_check_result = "lean_verified"` plus an attacker-chosen
`lean_metadata` lets you test promotion refusals in seconds instead of minutes (no Lean build at
all). Use a Z3-`unknown` fixture such as the Fermat-style
`ensures: x*x*x + y*y*y != z*z*z;`. Drive one variable per case and always include a
**valid control case that must promote**, otherwise a broken stub looks like a passing refusal.
Expected results: stale candidate `translator_version`/`bridge_lemma_hash`, metadata
`status != "lean_verified"`, empty `theorem_name`, or a stale metadata-internal version all leave the
atom at `z3_check_result == "unknown"` / `status == "escalation_candidate"`. Wrong-typed provenance
(e.g. `known_witness_used: "yes"`, `tactic_search: []`) makes `serde_json` reject the whole bridge
cert at `run_lean_bridge()`; the CLI prints
`⚠️  Lean escalation bridge failed: Failed to parse …: invalid type: string "yes", expected a boolean`,
exits 1 and applies nothing — verify it neither panics nor promotes.

Two behaviours that look alarming but are by design — do not report them as regressions without
context: (1) a refused candidate's attacker-supplied metadata is still copied verbatim into
`atom.lean_result_metadata` (including a `status: "lean_verified"` string) while the atom itself
stays `unknown`, because `apply_lean_cert_to_proof_certificate()` copies metadata before gating;
(2) `timed_out: true` / `exhausted: true` / `adopted_tactic: null` still promotes if the four gate
fields are valid, since the gate ignores search provenance.

#### verify-cert notes

`mumei verify-cert <cert.proof.json> <source.mm> [--allow-lean-verified]`. Without the flag
`lean_verified` atoms report `unproven`; with it they report `proven` — but **both invocations exit
0**, so assert on the `Results: N proven, … M unproven` line, not the exit code. A cert whose atom
`translator_version` is stale fails hard with
`❌ Failed to validate …: Lean translator metadata validation failed`. `certificate_hash` is a
SHA-256 over the whole serialized cert with the hash field blanked, so it *does* cover the new
provenance fields (recompute in Python with
`json.dumps(obj, separators=(',',':'), ensure_ascii=False)` after setting `certificate_hash` to `""`
— it matches byte-for-byte); however `verify-cert` only *prints* the stored hash and never
recompares it, so hand-edited provenance is not detected there. Keep that distinction in mind before
claiming a cert is "integrity checked".

#### Artifact hygiene (mumei side)

`mumei verify --proof-cert` and `benchmarks/run_benchmarks.py` drop `<stem>.proof.json` (and
`cross_spec.json`) into the *current working directory*. mumei's `.gitignore` covers these only at
the repo root (`/*.proof.json`, `cross_spec.json`), so run the CLI from the repo root or clean up
manually; verify with `git check-ignore -v <file>` and a final `git status --short`. Note that
`cargo test` can recreate `cross_spec.json`, so re-check hygiene *after* the regression gates, not
before.
