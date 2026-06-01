# Lean executable code in Mumei

Mumei can use Lean 4 not only as a theorem prover, but also as the implementation
language for production tools. This follows the ArkLib-style approach: the code
that satisfies a formal specification is the code that ships.

## Pipeline

```text
Mumei DSL contract
  → mumei proof certificate
  → mumei-lean translation / Lean proof
  → Lean 4 module with executable entrypoint
  → Lake native binary
  → binary + .lean-cert.json artifact
```

The final artifact pair keeps the runtime executable and the proof evidence in
the same directory. Downstream packaging can therefore treat the binary as an
auditable asset rather than an untracked build output.

For the committed example this becomes:

```text
simple-cli mumei-dsl add 2 40
  → MiniMumeiExpr.add 2 40
  → evalMiniMumei (.add 2 40)
  → evalMiniMumei_add_matches_contract
  → lake build simple-cli
  → out/lean_cli/simple-cli + out/lean_cli/.lean-cert.json
```

`examples/lean_cli/.lean-cert.json` is intentionally small, but it acts as the
same artifact-level proof stamp expected from the full bridge: it names the
Lean module, Lake executable target, verification status, and witness theorem
names that justify the runtime behavior shipped in the binary.

## `scripts/lean_to_executable.py`

`lean_to_executable.py` builds a Lake executable target, copies the generated
binary to an output directory, and copies the matching `.lean-cert.json` beside
it.

```bash
python scripts/lean_to_executable.py \
  --project-dir examples/lean_cli \
  --module SimpleCli \
  --out-dir out/lean_cli \
  --run-args mumei-dsl add 2 40
```

Options:

- `--project-dir`: directory containing `lakefile.lean`.
- `--module`: Lean module root for the executable entrypoint.
- `--target`: Lake executable target. If omitted, the script derives a
  kebab-case target from the module leaf (`SimpleCli` → `simple-cli`).
- `--cert`: certificate path. If omitted, `<project-dir>/.lean-cert.json` is
  copied.
- `--binary-name`: optional filename for the copied executable.
- `--lake`: Lake command name, defaulting to `lake`.
- `--run-args`: optional smoke-test arguments passed to the copied executable
  after the binary and certificate are exported.
- `--run-timeout`: timeout in seconds for the `--run-args` smoke test.

If `lake build <target>` fails, the script exits non-zero and prints the Lake
output so CI can show the Lean elaboration or build error directly.
If `--run-args` is provided, the script also exits non-zero when the exported
binary cannot execute successfully.

## Lean CLI best practices

- Keep `main : List String → IO UInt32` small and deterministic.
- Put parsing and validation in pure functions returning `Except String α`.
- Avoid partial functions in production entrypoints.
- Prefer explicit exit codes: `0` for success, `2` for user input errors.
- Keep the executable target in `lakefile.lean` close to the module it builds.
- Store `.lean-cert.json` beside the Lean project or pass it explicitly with
  `--cert`.

## Example

See [`examples/lean_cli`](../examples/lean_cli/README.md). It defines:

- `SimpleCli.lean`: a small CLI with `greet`, `add`, `echo`, a miniature
  `mumei-dsl` interpreter, and Phase 4-6 demo commands.
- `lakefile.lean`: a minimal Lake project with a `simple-cli` executable target.
- `.lean-cert.json`: example proof metadata copied beside the binary.

Build and run it directly with Lake:

```bash
(cd examples/lean_cli && PATH="$HOME/.elan/bin:$PATH" lake build simple-cli)
examples/lean_cli/.lake/build/bin/simple-cli mumei-dsl add 2 40
examples/lean_cli/.lake/build/bin/simple-cli mumei-dsl len verified specs
```

Expected output:

```text
mumei-dsl result=42
mumei-dsl result=14
```

Export the binary and proof stamp from the repository root:

```bash
python scripts/lean_to_executable.py \
  --project-dir examples/lean_cli \
  --module SimpleCli \
  --out-dir out/lean_cli \
  --run-args mumei-dsl add 2 40

out/lean_cli/simple-cli mumei-dsl concat proof stamp
python -m json.tool out/lean_cli/.lean-cert.json
```

Expected output:

```text
wrote executable: .../out/lean_cli/simple-cli
wrote certificate: .../out/lean_cli/.lean-cert.json
mumei-dsl result=proofstamp
{
  "lean_cert_schema_version": "1.0-lean-executable-example",
  "module": "SimpleCli",
  "target": "simple-cli",
  "status": "verified",
  "proof_stamp": {
    "kind": "lean_executable_artifact",
    "dsl_surface": "mumei-dsl add | len | concat",
    "witness_theorems": [
      "evalMiniMumei_add_matches_contract",
      "evalMiniMumei_len_matches_contract",
      "evalMiniMumei_concat_matches_contract",
      "MumeiLean.MerkleTree.verify_merkle_root_matches_expected",
      "MumeiLean.DeFi.safe_transfer_preserves_uint256",
      "MumeiLean.ArkLibAudit.review_top_level_theorem_matches_commitment"
    ],
    "binary_target": "simple-cli"
  }
}
```

This demonstrates the complete local path from a small DSL surface to a Lean
interpreter, checked witness theorems, a native executable, and the colocated
`.lean-cert.json` proof stamp.

## Phase 4-6 demo pipeline

The Phase 4-6 demo proofs are committed as Lean witness modules:

| Demo | Lean module | CLI command |
|---|---|---|
| Merkle Tree Verification | `MumeiLean.MerkleTree` | `simple-cli merkle <root> <leaf> <sibling_hash> <expected_root> <hash_secure_flag>` |
| DeFi Invariant | `MumeiLean.DeFi` | `simple-cli defi-transfer <from_balance> <to_balance> <amount>` |
| ArkLib-Style Audit | `MumeiLean.ArkLibAudit` | `simple-cli audit-commitment <pre_hash> <post_hash> <invariant_hash> <expected_commitment>` |

Validate the Lean proof modules and export the executable:

```bash
PATH="$HOME/.elan/bin:$PATH" lake build \
  MumeiLean.MerkleTree \
  MumeiLean.DeFi \
  MumeiLean.ArkLibAudit

python scripts/lean_to_executable.py \
  --project-dir examples/lean_cli \
  --module SimpleCli \
  --out-dir out/phase46 \
  --run-args mumei-dsl add 2 40

out/phase46/simple-cli merkle 7 3 4 7 1
out/phase46/simple-cli defi-transfer 20 30 5
out/phase46/simple-cli audit-commitment 10 20 30 60
```

Expected CLI output:

```text
merkle accepted root=7
defi transfer accepted to_balance=35
audit commitment accepted commitment=60
```

The resulting directory contains:

```text
out/phase46/simple-cli
out/phase46/.lean-cert.json
```

This is the executable artifact pair for downstream demo packaging: the binary
implements the same Merkle, DeFi, and ArkLib-style contracts that the Lean
modules witness.

## Vision

The long-term Mumei path is for a DSL contract to generate proof obligations,
prove them through the existing mumei-lean bridge, and ship the Lean executable
that implements the same contract. The proof certificate is not a detached
report; it is part of the production artifact. This makes “proved specification”
and “deployed implementation” converge into the same release unit.
