/-!
# MumeiLean

Public umbrella module for the `MumeiLean` Lean library. Importing
`MumeiLean` re-exports the basic definitions, the certificate parser,
and the theorem-generation helpers used by the Python bridge.

Top-level layout:

* `MumeiLean.Basic`      – core type / contract / proof-result types
* `MumeiLean.CertParser` – `.proof-cert.json` parser (skeleton)
* `MumeiLean.TheoremGen` – mumei `requires`/`ensures` → Lean `Prop` translator
* `MumeiLean.Verify`     – Lean-side proof checking helpers
* `MumeiLean.CertWriter` – `.lean-cert.json` emitter (skeleton)

The Python bridge under `scripts/` does the heavy lifting of
JSON ↔ Lean source translation; the modules above provide the
Lean-side primitives the generated theorems lean on.
-/

import MumeiLean.Basic
import MumeiLean.CertParser
import MumeiLean.TheoremGen
import MumeiLean.Verify
import MumeiLean.CertWriter
