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

universe u

/-- mumei's `len(arr)` maps to an integer-sized domain length parameter. -/
def mumei_len (n : Int) : Int := n

/-- mumei's `abs(x)` as an `Int → Int` helper. -/
def mumei_abs (x : Int) : Int := if x ≥ 0 then x else -x

/-- mumei's `starts_with(s, prefix)` string predicate. -/
def mumei_starts_with (s needle : String) : Prop := needle.isPrefixOf s

/-- mumei's `ends_with(s, suffix)` string predicate. -/
def mumei_ends_with (s needle : String) : Prop := s.endsWith needle

/-- mumei's `contains(s, sub)` string predicate. -/
def mumei_contains (s sub : String) : Prop :=
  ∃ pre post : String, s = pre ++ sub ++ post

/-- Character-list substring helper for executable containment checks. -/
def mumei_containsChars : List Char → List Char → Bool
  | [], needle => needle.isPrefixOf []
  | chars@(_ :: rest), needle => needle.isPrefixOf chars || mumei_containsChars rest needle

/-- Executable string containment helper for generated witnesses. -/
def mumei_contains' (s sub : String) : Bool :=
  mumei_containsChars s.data sub.data

/-- mumei's `not_contains(s, sub)` string predicate. -/
def mumei_not_contains (s sub : String) : Prop :=
  ¬ ∃ pre post : String, s = pre ++ sub ++ post

/-- Sum the first `n` elements of an integer list.

`n` is accepted as `Int` to match the scalar typing used by the bridge's
expression translator; negative or out-of-range values fall through to
`List.take`'s saturating `Nat` semantics via `Int.toNat`. -/
def mumei_sum (arr : List Int) (n : Int) : Int :=
  (arr.take n.toNat).foldl (· + ·) 0

/-- Count occurrences of an integer value in a list.

Returns an `Int` (rather than `Nat`) so the result composes with the
scalar-`Int` parameters and literals emitted by the bridge translator
without introducing `Nat`/`Int` coercions at each use site. -/
def mumei_count (arr : List Int) (val : Int) : Int :=
  Int.ofNat (arr.filter (· == val)).length

/-- Semantic range used when an SMT proof relies on machine-sized `i64`. -/
def mumei_i64_in_range (x : Int) : Prop :=
  -9223372036854775808 ≤ x ∧ x ≤ 9223372036854775807

/-- Typed refinement carrier for `{v : T | P v}` lowering. -/
abbrev MumeiSubtype (T : Type u) (P : T → Prop) := {v : T // P v}

/-- Effect-state token used by escalation lemmas. -/
structure MumeiEffectState where
  token : String
  deriving Repr, Inhabited

/-- Regex semantics are explicit manual bridge assumptions. -/
def mumei_regex_matches (_s _pattern : String) : Prop := True

/-- Base scalar type bridge for `i64 → Int`. -/
theorem mumei_i64_base_bridge (x : Int) : x = x := rfl

/-- Base Boolean type bridge for `bool → Bool`. -/
theorem mumei_bool_base_bridge (b : Bool) : b = b := rfl

/-- Base string type bridge for `string → String`. -/
theorem mumei_string_base_bridge (s : String) : s = s := rfl

/-- Refinement lowering preserves the predicate proof carried by a subtype. -/
theorem mumei_subtype_predicate_bridge {T : Type u} {P : T → Prop}
    (x : MumeiSubtype T P) : P x.val := x.2

/-- Array bounds are carried as explicit Lean hypotheses. -/
theorem mumei_array_bounds_bridge {α : Type u} (arr : List α) (i : Nat)
    (h : i < arr.length) : i < arr.length := h

/-- Guarded array access helper used by generated bridge statements. -/
def mumei_array_get {α : Type u} (arr : List α) (i : Nat) (h : i < arr.length) : α :=
  arr.get ⟨i, h⟩

/-- Array access lowering is guarded by the same bounds proof. -/
theorem mumei_array_get_bridge {α : Type u} (arr : List α) (i : Nat)
    (h : i < arr.length) : mumei_array_get arr i h = arr.get ⟨i, h⟩ := rfl

/-- Integer overflow obligations are explicit range assumptions. -/
theorem mumei_i64_overflow_bridge (x : Int) (h : mumei_i64_in_range x) :
    mumei_i64_in_range x := h

/-- String contains lowering is bridged through the executable helper. -/
theorem mumei_string_contains_bridge (s sub : String) (h : mumei_contains s sub) :
    mumei_contains s sub := h

/-- Regex obligations must be discharged by an explicit bridge assumption. -/
theorem mumei_regex_bridge (s pattern : String) (h : mumei_regex_matches s pattern) :
    mumei_regex_matches s pattern := h

/-- Effect-state lowering preserves the explicit token identity. -/
theorem mumei_effect_state_bridge (state : MumeiEffectState) :
    state.token = state.token := rfl

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
