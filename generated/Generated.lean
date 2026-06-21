/-!
# Generated

Root module for the `Generated` lake library. Actual theorem modules
are emitted on demand by `scripts/ingest_cert.py` into
`generated/Generated/**/*.lean` and picked up by lake via
`globs := #[.submodules `Generated]` in `lakefile.lean`.

This file intentionally contains no declarations — it exists so that
`lake build` can resolve the `Generated` library's source directory
even on a fresh clone where no certificates have been ingested yet.

Generated theorem modules must preserve the translator contract documented in
`docs/LEAN_TRANSLATOR_SPEC.md`: bridge metadata such as
`mumei_i64_overflow_bridge`, `mumei_array_get_bridge`, `lean_verified`,
`stale_translator`, and `bridge_lemma_hash` is managed by the Python bridge
before files appear under `generated/Generated/**`.
-/
