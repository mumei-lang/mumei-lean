# Tactic search history and agent-side propagation of new live paths

Read this when testing the learned candidate order (`data/tactic_search_history.json`, spec §12.5) or proving that a brand-new mumei-lean live path propagates through the mumei-agent API.

### Tactic search history (learned candidate order, spec §12.5)

The ladder order can be re-ranked from a *pinned* artifact `data/tactic_search_history.json`
(schema `mumei-lean.tactic_search_history/v1`). Never let a test write the repo-pinned artifact:
always copy it to a temp path and pass `--tactic-search-history /tmp/.../hist.json`, then confirm
`git status --porcelain data/tactic_search_history.json` is empty afterwards.

CLI flags to exercise: `--tactic-search-history PATH`, `--no-tactic-search-history`,
`--record-tactic-search-history`.

| case | expected metadata (`lean_metadata.tactic_search`) |
|---|---|
| artifact records the atom's `(obligation_class, stage)` | `history_ranked == true`, non-null `history_fingerprint`, short `candidates_tried` (learned candidate probed first) |
| `--no-tactic-search-history` | `history_ranked == false`, `history_fingerprint == null`, `candidates_tried` = declared-order prefix; adopted tactic and generated proof unchanged |
| artifact missing / truncated JSON / different `schema` value | same as `--no-tactic-search-history`; the bridge must exit 0, never raise |
| artifact non-empty but no entry for *this* `(obligation_class, stage)` | `history_ranked == false` (the flag reports a ranking that actually moved this ladder, not artifact presence) |
| `--no-tactic-search-history --record-tactic-search-history` together | pre-existing entries survive and counts are incremented (recording re-reads and merges the artifact); a replace-instead-of-merge bug shows up as lost entries |

`obligation_class` comes from `translator_ir.obligation_class`, falling back to
`logic_fragment_tag` (so `predicate_guard_collapse` learns under `propositional`).

Useful strong signal that learning really reorders instead of being a no-op: compare
`candidates_tried` between a ranked run (e.g. `["tauto"]`) and `--no-tactic-search-history`
(the full declared prefix, 13 entries up to `tauto`) — the adopted tactic and the byte content of
the generated module must be identical in both.

Ranking must always be a permutation of the declared ladder. A cheap runtime property check is to
drive `tactic_history.load_history` + `tactic_search.ladder_for` (`PYTHONPATH=scripts`) with
adversarial artifacts — unknown candidate ids, duplicate entries, non-positive `successes`, ties —
and assert `sorted(result) == sorted(TACTIC_CANDIDATES)`, `len == 16`, no duplicates, ties keeping
declared order, and declared order returned when nothing applies.

Note: the run-level stdout line `tactic search ladder ranked by <path> (fingerprint …)` is printed
whenever the artifact is non-empty, even if no obligation was actually re-ranked — assert on the
per-atom `history_ranked` field, not on that log line.

### Agent-side propagation of a brand-new live path

`tests/test_lean_bridge_e2e.py` in mumei-agent only covers `abs_saturating`. To prove a *new*
mumei-lean path propagates, drive the agent API directly:

```bash
cd /home/ubuntu/repos/mumei-agent
PATH="$HOME/.elan/bin:$PATH" MUMEI_LEAN_REPO=/home/ubuntu/repos/mumei-lean uv run python - <<'PY'
from agent import lean_bridge
r = lean_bridge.run_lean_bridge(cert_path=..., lean_cert_out=..., mumei_lean_repo=...)
merged = lean_bridge.merge_lean_cert_into_proof_cert(src_cert_dict, r["lean_cert"])
PY
```

Assert the merged atom has `z3_check_result == "lean_verified"`, `status == "verified"`,
`all_verified is True`, `known_witness_used is False`. As negative controls, tamper the source
atom's `translator_version` or `bridge_lemma_hash` in the input dict: the merged atom must stay
`unknown` with no Lean metadata attached.

`run_lean_bridge` writes into the mumei-lean repo's `generated/` tree, so delete
`generated/Generated/Std/<Module>.lean` afterwards — the pytest suites use the same paths.
