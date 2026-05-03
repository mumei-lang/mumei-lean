import MumeiLean.Basic
import MumeiLean.CertParser
import MumeiLean.TheoremGen
import MumeiLean.Tactics
import MumeiLean.Verify
import MumeiLean.CertWriter
import MumeiLean.Pilot
import MumeiLean.Ownership
import MumeiLean.Patterns

/-!
# MumeiLean

Public umbrella module for the `MumeiLean` Lean library. Importing
`MumeiLean` re-exports the basic definitions, the certificate parser,
and the theorem-generation helpers used by the Python bridge.

Top-level layout:

* `MumeiLean.Basic`      – core type / contract / proof-result types
* `MumeiLean.CertParser` – native `.proof-cert.json` parser (`Lean.Json`)
* `MumeiLean.TheoremGen` – mumei `requires`/`ensures` → Lean `Prop` translator
* `MumeiLean.Tactics`    – mathlib4-backed `mumei_arith` combinator
* `MumeiLean.Verify`     – Lean-side proof checking helpers
* `MumeiLean.CertWriter` – native `.lean-cert.json` emitter (`Lean.Json`)
* `MumeiLean.Pilot`      – hand-proven pilot theorems exercising the
  bridge translator's `forall(..)` / `arr[i]` lowering (PR 3)
* `MumeiLean.Ownership`  – finite-state Ownership Transfer Protocol
  proof that transfer is unreachable without `accept`
* `MumeiLean.Patterns`   – reusable SC proof patterns (addition bounds,
  conservation, monotonicity)

The Python bridge under `scripts/` does the heavy lifting of
JSON ↔ Lean source translation; the modules above provide the
Lean-side primitives the generated theorems lean on.
-/
