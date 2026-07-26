# Bridge Harness Specification

This document externalizes the `mumei-lean` escalation bridge as an NLAH-style
harness contract. The bridge remains deterministic Python + Lean 4 execution;
the contract below describes which artifacts are accepted, how state flows
between steps, and when an atom may be marked `lean_verified`.

For the artifact-level contract covering `.proof-cert.json`, generated Lean,
`lake build`, `.lean-cert.json`, and summary JSON, see
[`LEAN_HARNESS_CONTRACT.md`](LEAN_HARNESS_CONTRACT.md).

Vocabulary is inherited from the cross-project roadmap: `harness_contract`, `intent_fidelity`, `artifact_paths`, `budget_policy_fingerprint`, and `lean_verified` are the only canonical field names.


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

Current contract constants are `translator_version = mumei-lean-translator-ir-v2` and `bridge_lemma_hash = fec31244e29b7d6bd4790b0a25bceb7fce6bdf8f0b18d74d1c0ccdec8ecdc49d`.

## Scope

Covered entrypoints:

- `python scripts/bridge.py --cert <file.proof-cert.json>`
- `python scripts/bridge.py --bundle <std-proof-bundle.json>`
- `python scripts/bridge.py --escalation-bundle <file.escalation-bundle.json>`
- `python scripts/bridge.py --scan-unknown <mumei-repo>`

Runtime owners:

- `scripts/ingest_cert.py`: collect `unknown` atoms and emit generated Lean.
- `scripts/expr_translator.py`: lower Mumei contracts/body expressions to Lean.
- `lake build`: type-check generated proofs and tactics.
- `scripts/export_cert.py`: conservatively merge Lean results into Mumei
  certificates.
- `scripts/bridge.py`: orchestrate the full pipeline and write summaries.

## Acceptance Path

| Stage | Input | Output | Verifier gate | Stop condition |
| --- | --- | --- | --- | --- |
| B0 Input selection | `--cert`, `--bundle`, `--escalation-bundle`, or `--scan-unknown` | payload list | JSON parses; scan only returns certs with `z3_check_result == "unknown"` | no unknown atoms yields a zero-unknown summary |
| B1 Candidate collection | ProofCertificate / ProofBundle / escalation bundle | `IngestedAtom[]` | every candidate preserves atom name, module key, contract text, translator metadata, and escalation reason | partial translations remain candidates but are not emitted as proof atoms |
| B2 Lean source generation | proof-capable `IngestedAtom[]` | `generated/<Module>.lean` | module path is deterministic from module key and `--module-prefix` | generated files written or dry-run stops |
| B3 Lean build | generated Lean sources, `lakefile.lean`, pinned `lean-toolchain` | `generated/lake_build.log` | `lake build` exits 0 and produced no `sorry` or generated theorem errors | `--no-build`, `--ci-mode` fallback, lake missing, or build complete |
| B4 Failure attribution | build log, generated file paths | per-payload failed theorem names | unattributable or unrecognised build failures prove no atoms | attributed failures collected |
| B5 Certificate export | original cert(s), proved/failed atom names, metadata | `.lean-cert.json` | only atoms with current translator contract, no manual lemma reason, and no attributed failure become `lean_verified` | certificate written or `--no-export` |
| B6 Summary/reporting | candidate/module/metrics state | `--summary-json` payload | summary is JSON-serializable and includes harness contract metadata | summary written |

## Artifact Contracts

### Input certificate or bundle

- Must be valid JSON.
- Candidate atoms must have `z3_check_result == "unknown"`.
- Non-unknown atoms are forwarded unchanged.
- Translator contract fields (`translator_version`, `binder_mapping`,
  `bridge_lemma_hash`, `manual_lemma_reason`, `translator_ir`) are preserved
  when present.

### Generated Lean source

- Location: `--out-dir`, default `generated/`.
- One generated file per module key.
- Each proof-capable atom gets a theorem named `<atom>_correct`.
- For `std/math_abs`, the live theorem path is `generated/Generated/Std/Math/Abs.lean` with theorem `Generated.Std.Math.Abs.abs_saturating_correct`.
- Partial translations and manual lemma candidates remain visible in metadata
  but do not become false automatic proofs.

### Lake build log

- Location: `<out-dir>/lake_build.log`.
- `lake` missing is encoded as return code `127`.
- Any unattributable infrastructure or import-level failure is conservative:
  every lifted atom is treated as failed.
- `--ci-mode` may preserve generated artifacts and skip export after a build
  failure, but must set `ci_mode_fallback` in summaries.

### Lean certificate

- Location: `--lean-cert-out`.
- Schema: original mumei ProofCertificate/ProofBundle plus
  `lean_cert_schema_version`, `lean_version`, and `harness_contract`.
- Atom-level result:
  - success: `z3_check_result = "lean_verified"`, `status = "verified"`;
  - unresolved: original status retained with `lean_metadata.status` explaining
    `manual_lemma_required`, `partial_translation`, or `stale_translator`.
- Atom hashes and dependency/effect fields are forwarded verbatim.

### Summary JSON

- Location: `--summary-json`.
- Always written for scan mode, including zero-unknown scans.
- Contains `harness_contract`, module counts, CI fallback status, and metrics
  grouped by atom, logic fragment, and failure reason.

## Failure Taxonomy

| Class | Trigger | Harness behavior |
| --- | --- | --- |
| `proved` | Lean theorem builds and current translator metadata matches | mark atom `lean_verified` |
| `partial_translation` | translator cannot fully lower contract/body | keep unresolved and require follow-up translator/lemma work |
| `manual_lemma_required` | source atom carries manual lemma reason | keep unresolved; do not auto-trust generated proof text |
| `stale_translator` | `translator_version` or `bridge_lemma_hash` mismatch | keep unresolved; regenerate with current bridge |
| `lean_proof_unresolved` | theorem-level Lean failure, `sorry`, or unattributed proof failure | keep unresolved and attach diagnostics |
| `lake_missing` | `lake` absent from `PATH` | no atoms proven; caller may retry after toolchain setup |
| `known_witness_fallback` | generated path cannot be promoted but a committed witness such as `MumeiLean.StdMathAbs` validates | export explicit `known_witness_used = true` metadata; never mark the live path as passed |
| `ci_mode_fallback` | CI build failure under `--ci-mode` | preserve generated artifacts and skip export |
| `no_unknown_atoms` | scan found no candidates | write deterministic empty summary |

## Harness Metadata

`scripts/bridge.py` now attaches a versioned harness contract to summaries and
exported certificates:

```json
{
  "policy": "mumei-lean-bridge-harness/v1",
  "input_kind": "cert",
  "acceptance_path": [
    "collect_unknown_atoms",
    "translate_to_lean",
    "run_lake_build",
    "export_lean_certificate"
  ],
  "build_mode": "lake_build",
  "module_prefix": "Generated",
  "state_paths": {
    "generated_lean_dir": "generated",
    "lean_cert_out": "out/std_math.lean-cert.json"
  }
}
```

Atom-level `lean_metadata.harness` records the same policy at the candidate
stage, the artifact paths, the verifier gate, and the mapped failure taxonomy.

## Integration Expectations

- `mumei-agent` should call this bridge only for genuine Z3 `unknown`, timeout,
  or resource-limit obligations, not ordinary syntax/type errors.
- `mumei-demo` scenarios should treat `.lean-cert.json` and summary JSON paths
  as first-class artifacts when demonstrating L3 escalation.
- `mumei` resolver logic remains the authority for whether a returned
  certificate can be trusted; the bridge never bypasses content hashes or
  translator contract checks.
