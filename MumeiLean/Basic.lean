/-!
# MumeiLean.Basic

Core type and contract definitions for `mumei-lean`.

This module mirrors a small subset of mumei's compile-time model in
Lean 4:

* mumei primitive types are mapped to existing Lean types
  (`i64 → Int`, `u64 → Nat`, `f64 → Float`, `bool → Bool`, `Str → String`).
* `MumeiContract` encodes a mumei atom contract (`requires` / `ensures`)
  as a pair of `Prop`s, suitable for direct theorem statements.
* `ProofResult` records the outcome of a Lean-side proof attempt for a
  single atom; it is later serialised back into a mumei-compatible
  `AtomCertificate` JSON record by `scripts/export_cert.py`.

Only the minimum surface needed by the bridge pipeline lives here on
purpose — richer notions (effects, refinement types, etc.) are
intentionally deferred to follow-up modules.
-/

namespace MumeiLean

/-- mumei's `len(arr)` maps to an integer-sized domain length parameter. -/
def mumei_len (n : Int) : Int := n

/-- mumei's `abs(x)` as an `Int → Int` helper. -/
def mumei_abs (x : Int) : Int := if x ≥ 0 then x else -x

/-- mumei atom contract represented as a pair of `Prop`s.

`requires` is the precondition the caller must establish, `ensures`
is the postcondition the body of the atom guarantees.
-/
structure MumeiContract where
  name     : String
  requires : Prop
  ensures  : Prop

/-- Outcome of a Lean-side proof attempt for a single atom. -/
inductive ProofResult where
  | verified                        : ProofResult
  | failed   (reason : String)      : ProofResult
  | timeout                         : ProofResult
  deriving Repr, Inhabited

/-- Convert a `ProofResult` to the `z3_check_result` string used in
mumei `AtomCertificate` JSON. The bridge uses the new
`"lean_verified"` value for successful proofs; failures map to the
existing `"unknown"` so the resolver continues to treat them as
unproven. -/
def ProofResult.toZ3CheckResult : ProofResult → String
  | .verified   => "lean_verified"
  | .failed _   => "unknown"
  | .timeout    => "unknown"

/-- Convert a `ProofResult` to the `status` string used in mumei
`AtomCertificate` JSON. -/
def ProofResult.toStatus : ProofResult → String
  | .verified   => "verified"
  | .failed _   => "failed"
  | .timeout    => "failed"

end MumeiLean
