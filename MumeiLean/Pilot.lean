import MumeiLean.Basic

/-!
# MumeiLean.Pilot

Pilot Lean proofs corresponding to mumei atoms whose `requires` /
`ensures` were translated by the Python `scripts/expr_translator.py`
extensions (bounded `forall` quantifiers and `arr[i]` array access).
PR 4 lowers `arr[i]` to `List.get!` semantics, so these proofs use
`arr : List Int` and `arr.get! i` to match the bridge's emitted shape.

These are *not* `sorry` placeholders — they are the smallest hand-proven
witnesses that the translator's emitted Lean Props are well-formed and
provable, end-to-end. The bridge pipeline can swap in machine-generated
versions of the same shape later.

The atom names are kept in sync with the `tests/fixtures/pilot_proof_cert.json`
fixture so that `scripts/bridge.py --no-build` round-trips the fixture
into theorems that match these declarations by name.
-/

namespace MumeiLean.Pilot

/-- Pilot 1: identity-on-arrays.

mumei atom shape::

    atom pilot_array_identity(arr: List i64, n: i64)
    requires: n >= 0 && forall(i, 0, n, arr[i] >= 0);
    ensures:  forall(i, 0, n, arr[i] >= 0);
    body:     -- pure: returns arr unchanged

The Z3 verifier returns `unknown` for the post-store `forall` shape
because it cannot quantify over arbitrary list contents. In Lean the
proof is trivial: `ensures` is literally the `requires` quantifier, so
the proof is reflexive. -/
theorem pilot_array_identity_correct
    (arr : List Int) (n : Int)
    (h : n ≥ 0 ∧ (∀ i : Int, 0 ≤ i → i < n → arr.get! i.toNat ≥ 0)) :
    (∀ i : Int, 0 ≤ i → i < n → arr.get! i.toNat ≥ 0) :=
  h.2

/-- Pilot 2: lower bound shifts under a constant offset.

mumei atom shape::

    atom pilot_array_offset(arr: List i64, n: i64)
    requires: n >= 0 && forall(i, 0, n, arr[i] >= 1);
    ensures:  forall(i, 0, n, arr[i] >= 0);

A weaker lower bound on every element follows from the stronger one. -/
theorem pilot_array_offset_correct
    (arr : List Int) (n : Int)
    (h : n ≥ 0 ∧ (∀ i : Int, 0 ≤ i → i < n → arr.get! i.toNat ≥ 1)) :
    (∀ i : Int, 0 ≤ i → i < n → arr.get! i.toNat ≥ 0) := by
  intro i hlo hhi
  have hge1 := h.2 i hlo hhi
  omega

end MumeiLean.Pilot
