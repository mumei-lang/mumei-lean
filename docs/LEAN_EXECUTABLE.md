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

## `scripts/lean_to_executable.py`

`lean_to_executable.py` builds a Lake executable target, copies the generated
binary to an output directory, and copies the matching `.lean-cert.json` beside
it.

```bash
python scripts/lean_to_executable.py \
  --project-dir examples/lean_cli \
  --module SimpleCli \
  --out-dir out/lean_cli
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

If `lake build <target>` fails, the script exits non-zero and prints the Lake
output so CI can show the Lean elaboration or build error directly.

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

- `SimpleCli.lean`: a small CLI with `greet`, `add`, and `echo` commands.
- `lakefile.lean`: a minimal Lake project with a `simple-cli` executable target.
- `.lean-cert.json`: example proof metadata copied beside the binary.

## Vision

The long-term Mumei path is for a DSL contract to generate proof obligations,
prove them through the existing mumei-lean bridge, and ship the Lean executable
that implements the same contract. The proof certificate is not a detached
report; it is part of the production artifact. This makes “proved specification”
and “deployed implementation” converge into the same release unit.
