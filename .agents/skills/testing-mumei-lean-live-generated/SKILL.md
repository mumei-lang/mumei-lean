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

## Timing Expectations

With a warm mathlib cache (`.lake` around 5 GB) the whole live suite finishes in well under a
minute — 23 tests in ~32s, full live `pytest -q` at 286 passed in ~41s, and `lake build` replays
from cache. The `bridge body-semantics E2E` CI job has historically taken ~45 min instead; that is
cold-cache `lake exe cache get` time, not a code regression. If a *local* run suddenly takes tens
of minutes, suspect a cache miss (check `lake exe cache get` and `mkdir -p generated/Generated`)
rather than the bridge.

## Reference Files

Detailed flows live in `references/`. Read only what the change needs:

| File | Read it when |
| --- | --- |
| [`references/finite-field-and-sort-bridge-tests.md`](references/finite-field-and-sort-bridge-tests.md) | validating live generated theorem paths for finite-field/algebra atoms or the sort ascending-preservation path, including fresh mumei certificate generation and expected outputs. |
| [`references/live-generated-theorem-paths.md`](references/live-generated-theorem-paths.md) | you need the full list of the twenty live generated theorem paths, their fixtures, and the per-path test commands and expected assertions. |
| [`references/adversarial-checks.md`](references/adversarial-checks.md) | promotion logic, the translator contract, `MumeiLean/CertWriter.lean`, or external proof injection changes and you must show the pipeline refuses bad input. |
| [`references/tactic-search.md`](references/tactic-search.md) | changes touch `scripts/tactic_search.py`, the `residual` / `build_failure` bridge stages, `MumeiLean/Tactics.lean`, or `lean_result_metadata.tactic_search`, including the mumei CLI pipeline, no-false-promotion matrix, benchmarks, provenance and artifact hygiene. |
| [`references/tactic-search-history-and-agent-propagation.md`](references/tactic-search-history-and-agent-propagation.md) | testing the learned candidate order (`data/tactic_search_history.json`, spec §12.5) or proving that a brand-new mumei-lean live path propagates through the mumei-agent API. |

- Read [`references/finite-field-and-sort-bridge-tests.md`](references/finite-field-and-sort-bridge-tests.md) when a finite-field or sort live path changes.
- Read [`references/live-generated-theorem-paths.md`](references/live-generated-theorem-paths.md) when adding or checking any of the twenty live paths.
- Read [`references/adversarial-checks.md`](references/adversarial-checks.md) when promotion logic or the trust boundary changes.
- Read [`references/tactic-search.md`](references/tactic-search.md) when the tactic search ladder or its metadata changes.
- Read [`references/tactic-search-history-and-agent-propagation.md`](references/tactic-search-history-and-agent-propagation.md) when the history artifact changes or a new live path must reach mumei-agent.
