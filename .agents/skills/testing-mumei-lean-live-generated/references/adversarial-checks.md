# Adversarial checks (negative controls)

Read this when promotion logic, the translator contract, `MumeiLean/CertWriter.lean`, or external proof injection changes and you must show the pipeline refuses bad input.

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

### 4. External (AI) proof injection must never promote an unproved atom (B-2 / spec §13)

`scripts/bridge.py --external-proofs PATH` is the *only* path by which mumei-agent's AI proof
stage (`agent/lean_ai_proof.py`) reaches Lake: the agent hands over tactic scripts, the bridge
regenerates the statement from the certificate (`ingest_cert.py`), injects the script as
`IngestedAtom.auto_tactic`, builds, and exports through the same `export_cert.py` gates as any
other atom. The fixture `tests/fixtures/std_quintic_external_proof.proof-cert.json`
(`x > 0 → x⁵ > 0`) is out of reach for the `mumei_arith_deep` ladder, so any `lean_verified`
there can only come from the supplied script. Run the committed matrix with `-rs`:

```bash
PATH="$HOME/.elan/bin:$PATH" PYTHONPATH=scripts python -m pytest \
  tests/test_lean_bridge_e2e.py -q -rs -k external_proof_matrix
```

| `proofs[0]` entry | Expected |
|---|---|
| valid script (`intro hx; subst h_body; unfold quinticPosResult; …mul_pos…`) | bridge exit 0, `z3_check_result == "lean_verified"`, `lean_metadata.ai_proof_used == true`, `ai_proof_attempts` copied from the entry, `external_proof.source == "ai_generated_proof"` |
| script containing `sorry` (or `admit` / `native_decide` / `axiom` / `unsafe` / `run_cmd` …) | rejected *before* Lake: stderr `rejected: forbidden_token:sorry`, `lean_metadata.external_proof == {"rejected": "forbidden_token:sorry"}`, generated source has no `external_proof:` marker and no `sorry`; atom stays `unknown`, `ai_proof_used == false` |
| script that leaves goals open (`intro hx; subst h_body; unfold quinticPosResult`) | `lake build` exits 1, `lake_build_failures.json` has one entry `{"atom": "quintic_pos", "kind": "unsolved_goals", "line": …}`, atom stays `unknown`, `lean_metadata.status == "manual_lemma_required"`, `ai_proof_used == false` |
| script with a type error (`intro hx; exact hx`) | build fails with `kind == "type_mismatch"` in the failure report; atom stays `unknown`, `ai_proof_used == false` |
| `witness_lemma` pointing at a missing declaration | build fails (`unknown_identifier`); atom stays `unknown` |

In every failing row `bridge.py` must exit 1 and `all_verified == false`. Adversarial check #2
(stale `translator_version` / `bridge_lemma_hash`) applies unchanged to injected proofs: the
export gate, not the injected script, decides promotion. The structured
failure report (`--failure-report PATH`, default `<out-dir>/lake_build_failures.json`,
schema `mumei-lean-build-failures-v1`) is what mumei-agent feeds back to the model for the next
attempt — if a row fails to build but the report has no entry for the atom, the agent's repair
loop degrades to log-tail feedback, so treat a missing entry as a regression too. The
`external_proof_matrix` test asserts this: for the `unsolved_goals` / `type_mismatch` /
`missing_witness` rows it reads `<out-dir>/lake_build_failures.json` and requires an entry with
`atom == "quintic_pos"`, the expected `kind`, and an integer `line`; the `sorry` row is
rejected before Lake so no specific kind is required there.

Agent-side live check (same fixture, real Lake, scripted generator that first returns the
unsolved-goals script and then the valid one): `run_ai_proof_repair(...)` must show
`ai_proof_outcomes[0].attempt_log == [tactic_failed, accepted]`, the second request's
`feedback[0].failures[0].kind == "unsolved_goals"`, and the promoted atom's `lean_metadata`
carrying the bridge's `translator_version` / `bridge_lemma_hash` / `lean_theorem_name`
verbatim plus an `ai_proof_evidence.axiom_audit_log_path` whose log lists only
`propext`, `Classical.choice`, `Quot.sound`. An AI stage that still promotes from its own
`lake build` log instead of the exported `.lean-cert.json` is the regression this guards.
