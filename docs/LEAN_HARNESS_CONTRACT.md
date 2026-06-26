# Lean harness contract

This contract defines `mumei-lean` as the deep-proof verifier module for
Mumei obligations that Z3 returns as `unknown`. It narrows the broader
[`BRIDGE_HARNESS_SPEC.md`](BRIDGE_HARNESS_SPEC.md) into the artifact-level
contract that callers can use to validate inputs, generated Lean, `lake build`,
`.lean-cert.json`, and summary JSON outputs.

The cross-project roadmap is the sole upper roadmap. This contract uses the canonical field names `harness_contract`, `intent_fidelity`, `artifact_paths`, `budget_policy_fingerprint`, and `lean_verified` without aliases.


## Unknown obligation bridge contract

The only promoted Lean path is:

1. Scan mumei proof certificates for atoms whose `z3_result_class == "unknown"` or `z3_check_result == "unknown"`; `status == "unknown"` or an `escalation_reason` alone is not a Lean candidate.
2. Translate each candidate to generated Lean with `translator_ir` metadata, `logic_fragment_tags`, and any `manual_lemma_reason` preserved.
3. Run `lake build` for the generated target unless the command is explicitly in `--no-build` dry-run mode.
4. Export `.lean-cert.json` with `lean_result_metadata` and the top-level atom fields `translator_version` and `bridge_lemma_hash`.
5. mumei accepts `lean_verified` only when both the source atom and `lean_result_metadata` match the current `translator_version` and `bridge_lemma_hash`; any mismatch is `stale_translator` and must not be treated as proven.

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

## Lean fallback contract

The standard abs fixture is the reference path for fallback semantics:

| Case | Required metadata | Export rule |
| --- | --- | --- |
| Live generated theorem succeeds | `lean_module = "Generated.Std.Math.Abs"`, `lean_theorem_name = "Generated.Std.Math.Abs.abs_saturating_correct"`, `known_witness_used = false` | Atom may become `lean_verified`. |
| Known witness fallback succeeds | `lean_module = "MumeiLean.StdMathAbs"`, `known_witness_used = true`, fallback reason retained | Atom may be exported only with explicit fallback attribution. |
| `lake_missing` | Lake/toolchain unavailable | No atom becomes `lean_verified`; retry after toolchain setup. |
| `partial_translation` | Translator emitted incomplete obligation or body semantics | No atom becomes `lean_verified`; fix translator or add manual lemma. |
| `stale_translator` | `translator_version` or `bridge_lemma_hash` mismatch | No atom becomes `lean_verified`; regenerate with current bridge. |

`abs_saturating` is the canonical live case: the generated theorem is emitted
from i64::MIN saturation, non-negative, and negative branches, not from the
hand-written `MumeiLean.StdMathAbs` witness.

## Scope

Covered entrypoints:

- `python scripts/bridge.py --cert <file.proof-cert.json>`
- `python scripts/bridge.py --bundle <std-proof-bundle.json>`
- `python scripts/bridge.py --escalation-bundle <file.escalation-bundle.json>`
- `python scripts/bridge.py --scan-unknown <mumei-repo>`
- `python scripts/ingest_cert.py <file.proof-cert.json> --out-dir generated`
- `python scripts/export_cert.py --cert <file.proof-cert.json> --build-log generated/lake_build.log`
- `PATH="$HOME/.elan/bin:$PATH" lake build`

Runtime owners:

- `scripts/bridge.py`: owns end-to-end orchestration, harness metadata, build
  mode selection, summary JSON, and export/no-export decisions.
- `scripts/ingest_cert.py`: owns `.proof-cert.json` / bundle ingestion,
  `unknown` atom selection, generated Lean module paths, translator metadata,
  and manual-lemma gating.
- `scripts/expr_translator.py`: owns lowering Mumei contracts/body expressions
  into Lean terms and `translator_ir` compliance metadata.
- `lake build`: owns Lean kernel checking of generated modules and committed
  `MumeiLean` support libraries.
- `scripts/export_cert.py`: owns build-log attribution, translator freshness
  checks, and conservative `.lean-cert.json` upgrades.

The module does not replace Z3 and does not repair ordinary syntax, typing, or
resolver errors. Its accepted input surface is the subset of certificate atoms
whose solver result is `unknown` or whose upstream escalation bundle explicitly
routes them to Lean.

## Acceptance Path

| Stage | Input | Output | Verifier gate | Stop condition |
| --- | --- | --- | --- | --- |
| L0 Input selection | `.proof-cert.json`, proof bundle, escalation bundle, or scan root | Parsed payload list | JSON parses; candidate atoms have `z3_check_result == "unknown"` or are explicitly escalated | malformed JSON, no matching files, or zero unknown atoms |
| L1 Candidate ingestion | parsed payload list | `IngestedAtom[]` plus atom metadata | atom name, module key, contract text, body expression, `translator_version`, `bridge_lemma_hash`, `manual_lemma_reason`, and `translator_ir` are preserved | non-unknown atoms are forwarded unchanged; partial/manual candidates remain visible but gated |
| L2 Lean generation | proof-capable `IngestedAtom[]` | generated Lean modules under `--out-dir` | module path is deterministic from module key and `--module-prefix`; theorem names use `<atom>_correct`; translator IR declaration metadata is emitted | `--dry-run`, no proof-capable atoms, or generation failure |
| L3 Lean build | generated Lean, `lakefile.lean`, `lean-toolchain`, `MumeiLean` libraries | `generated/lake_build.log` or process output | `lake build` exits `0`; generated theorems elaborate without `sorry` or Lean errors | `--no-build`, missing `lake`, build failure, or successful kernel check |
| L4 Build attribution | build log and generated source locations | proved atom set, failed atom set, unattributed failure flag | every generated theorem failure is attributed by source location or conservatively treated as global failure | unattributed/import-level error proves no lifted atoms |
| L5 Certificate export | original certificate payloads, proved/failed sets, atom metadata | `.lean-cert.json` payload(s) | atom can become `lean_verified` only when Lean proved it, translator version/hash are current, no manual lemma is required, and no attributed failure applies | `--no-export`, stale translator metadata, manual lemma gate, or write failure |
| L6 Summary/reporting | payload counts, metadata, metrics, harness contract | summary JSON at `--summary-json` | JSON includes versioned harness metadata, artifact paths, CI fallback status, and per-atom failure taxonomy | summary written; in scan mode zero-unknown summary is still deterministic |

## Artifact Contracts

### `.proof-cert.json`

Input certificates must be valid JSON and must preserve the mumei proof
certificate shape expected by the resolver. For each atom:

- `name` is the stable atom identifier used for theorem names and build-log
  attribution.
- `module` / module-key fields determine generated Lean module paths.
- `z3_check_result == "unknown"` is required for automatic lifting; other
  solver results are passed through unchanged.
- `requires`, `ensures`, optional `body_expr`, dependency/effect fields, atom
  hashes, and source metadata are copied into bridge metadata without mutation.
- `translator_version`, `binder_mapping`, `bridge_lemma_hash`,
  `manual_lemma_reason`, and `translator_ir` are part of the proof contract,
  not display-only diagnostics.
- Missing translator metadata is filled by the current translator only for the
  generated bridge candidate; export still verifies freshness before upgrading.

Bundles and escalation bundles follow the same atom-level contract. A scan root
is accepted only as a source for locating concrete `.proof-cert.json` files that
contain unknown atoms.

### Generated Lean

Generated Lean is a deterministic intermediate verifier artifact.

- Default root: `generated/`; namespace/module prefix defaults to `Generated`.
- File path: `generated/<ModuleKey>.lean`, derived by `module_to_path`.
- Theorem name: `<atom>_correct` for each emitted proof-capable atom.
- If `body_expr` is supported, the bridge emits a `def <atom>Result` plus an
  `h_body` equality so postconditions can be proved from body semantics.
- If only contracts are supported, the bridge emits the contract-only theorem
  shape (`requires -> ensures`).
- Partial translations and atoms with `manual_lemma_reason` may appear in
  metadata/comments, but must not be silently promoted to automatic proof.
- Generated declarations record translator provenance such as binder mapping,
  `translator_ir` sort, `translator_version`, and `bridge_lemma_hash`.
- The artifact is buildable only with the pinned `lean-toolchain` and committed
  `lakefile.lean`/`MumeiLean` support library.

### Lake build log

`lake build` is the verifier gate between generated source and certificate
export.

- Command: `PATH="$HOME/.elan/bin:$PATH" lake build` from the repository root.
- Normal log location during bridge orchestration: `<out-dir>/lake_build.log`.
- Exit code `0` means the Lean kernel accepted the committed library and
  generated modules.
- Exit code `127` or missing `lake` is classified as `lake_missing`.
- Any generated theorem error, remaining `sorry`, or emitted Lean diagnostic is
  attributed to the owning atom when possible.
- Import-level, infrastructure, or otherwise unattributable Lean failures are
  conservative: no lifted atoms may be marked `lean_verified`.
- `--ci-mode` may preserve generated artifacts and write fallback summaries
  after build failure, but export must remain disabled unless verifier gates
  pass.

### `.lean-cert.json`

Lean certificates are resolver-facing output artifacts.

- Location: `--lean-cert-out`; directories are created by the bridge/exporter.
- Shape: original ProofCertificate or ProofBundle plus Lean fields.
- Required top-level Lean fields:
  - `lean_cert_schema_version`
  - `lean_version`
  - `harness_contract`
- Successful atom upgrade:
  - `z3_check_result = "lean_verified"`
  - `status = "verified"`
  - current `translator_version`
  - current `bridge_lemma_hash`
  - `lean_metadata.status = "lean_verified"`
- Unresolved atoms retain their original solver/status fields and receive
  `lean_metadata.status` explaining the gate that stopped export, such as
  `manual_lemma_required`, `partial_translation`, or `stale_translator`.
- Atom hashes, dependency hashes, effects, and source metadata are forwarded
  verbatim. If any atom is upgraded, stale certificate-level hashes are dropped
  rather than reused.
- Export never upgrades an atom solely because a generated file exists; the atom
  must be in the proved set and outside all failure gates.

### Summary JSON

Summary JSON is the harness-facing telemetry artifact.

- Location: `--summary-json`.
- Written for scan mode even when no unknown atoms are found.
- Includes `harness_contract.policy = "mumei-lean-bridge-harness/v1"`.
- Includes `input_kind`, `acceptance_path`, `build_mode`, `module_prefix`, and
  `state_paths.generated_lean_dir` / `state_paths.lean_cert_out`.
- Reports generated module counts, candidate counts, proved/failed atom sets,
  CI fallback status, and escalation metrics.
- Aggregates metrics by atom, logic fragment, and failure reason.
- Per-atom metadata records theorem name, proof path, translator contract
  fields, diagnostics, and mapped failure taxonomy.

## Failure Taxonomy

| Class | Trigger | Harness behavior |
| --- | --- | --- |
| `manual_lemma_required` | Atom carries `manual_lemma_reason` or generated proof depends on a hand-written witness not supplied by the automatic bridge | Keep atom unresolved; emit metadata/diagnostics; never auto-promote to `lean_verified` |
| `translator_ir` | `translator_ir` is missing required provenance, fails compliance checks, records partial lowering, or cannot represent the Mumei contract/body faithfully | Treat as translator work; generated Lean may be omitted or marked partial; keep atom unresolved |
| `bridge_lemma_hash` | Atom metadata carries a `bridge_lemma_hash` that differs from the current bridge lemma set | Treat as stale proof dependency; regenerate or re-ingest before trusting Lean output |
| `stale_translator` | `translator_version` or bridge lemma metadata does not match the current bridge/exporter | Keep atom unresolved and attach `lean_metadata.status = "stale_translator"` |
| `lake_missing` | `lake` is absent from `PATH` or returns command-not-found (`127`) | No atoms are proven; caller may retry after Lean/Lake setup; summaries should identify setup failure |
| `lean_verified` | Lean build succeeds for the generated theorem, translator metadata is current, no manual lemma gate applies, and no build-log attribution marks the atom failed | Mark atom `z3_check_result = "lean_verified"` and `status = "verified"` in `.lean-cert.json` |

Additional implementation statuses such as `partial_translation`,
`lean_proof_unresolved`, `ci_mode_fallback`, and `no_unknown_atoms` may appear
in diagnostics or aggregate summaries, but the classes above are the stable
artifact contract vocabulary consumed by downstream harnesses.

## Harness Metadata

Bridge invocations attach a versioned harness contract to summary JSON and
exported `.lean-cert.json` files:

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
  },
  "artifact_contracts": [
    "Only atoms with z3_check_result == unknown are lifted into Lean.",
    "Generated Lean theorem paths are recorded per atom in lean_metadata.proof_path.",
    "Lake failures are attributed conservatively; unattributable failures prove no atoms.",
    "Exported certificates preserve original atom hashes and mark only proved atoms as lean_verified."
  ],
  "verifier_gates": {
    "translator_contract": "translator_version and bridge_lemma_hash must match the current bridge.",
    "lean_build": "lake build exits 0 without sorry or generated theorem errors.",
    "manual_review": "partial translations, stale translator metadata, and manual lemma reasons remain unverified."
  }
}
```

Atom-level `lean_metadata.harness` records the compact stage metadata:

- `harness_policy`
- `harness_stage`
- `input_kind`
- `build_mode`
- `module_prefix`
- `artifact_contract`
- `verifier_gate`
- `failure_taxonomy`

These metadata fields are the handoff contract for mumei-agent, mumei-demo, and
downstream mumei resolver checks. The resolver remains the authority on whether
the returned certificate is accepted.
