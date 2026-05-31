import MumeiLean.Basic
import MumeiLean.CertParser
import MumeiLean.TheoremGen
import MumeiLean.Tactics
import MumeiLean.Verify
import MumeiLean.CertWriter
import MumeiLean.Pilot
import MumeiLean.Ownership
import MumeiLean.Patterns
import MumeiLean.CryptoHelpers
import MumeiLean.Algebra
import MumeiLean.Crypto
import MumeiLean.Settlement
import MumeiLean.SmartContract
import MumeiLean.MerkleTree
import MumeiLean.DeFi
import MumeiLean.ArkLibAudit
import MumeiLean.MedicalDevice
import MumeiLean.StdMathAbs

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
* `MumeiLean.CryptoHelpers` – helper functions for modular arithmetic,
  powers, and Euler totient expressions emitted by the bridge translator
* `MumeiLean.Algebra`    – mathlib4-backed finite-field and group-theory
  helpers emitted by the bridge translator
* `MumeiLean.Crypto`     – reusable cryptographic proof patterns for
  RSA-style signature checks and finite-field bounds
* `MumeiLean.Settlement` – RTGS settlement temporal safety + balance
  conservation
* `MumeiLean.SmartContract` – reentrancy guard and withdrawal balance
  preservation proofs
* `MumeiLean.MerkleTree` – Phase 4 Merkle proof root binding witness
* `MumeiLean.DeFi` – Phase 5 ERC-20/Uint256 transfer bound witness
* `MumeiLean.ArkLibAudit` – Phase 6 reviewed top-level theorem witness
* `MumeiLean.MedicalDevice` – insulin-pump dosage bound and cumulative
  safety proofs
* `MumeiLean.StdMathAbs` – hand-written std/math + std/list proof
  witnesses for real standard-library atom contracts

The Python bridge under `scripts/` does the heavy lifting of
JSON ↔ Lean source translation; the modules above provide the
Lean-side primitives the generated theorems lean on.
-/
