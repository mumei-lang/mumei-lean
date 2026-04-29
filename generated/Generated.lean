/-!
# Generated

Root module for the `Generated` lake library. Actual theorem modules
are emitted on demand by `scripts/ingest_cert.py` into
`generated/Generated/**/*.lean` and picked up by lake via
`globs := #[.submodules `Generated]` in `lakefile.lean`.

This file intentionally contains no declarations — it exists so that
`lake build` can resolve the `Generated` library's source directory
even on a fresh clone where no certificates have been ingested yet.
-/
