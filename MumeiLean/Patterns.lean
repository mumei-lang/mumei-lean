import Mathlib.Tactic

/-!
# MumeiLean.Patterns

Reusable proof patterns for safety-critical mumei contracts that need
structural Lean proofs beyond the `mumei_arith` arithmetic fallback.

The Phase 2 RTGS demo's balance-conservation proof is the first target:
it needs reusable lemmas for bounded addition, transfer conservation over
balances, and queue/counter monotonicity.
-/

namespace MumeiLean.Patterns

theorem add_bounded (a b max : Int)
    (ha : a ≥ 0) (hb : b ≥ 0) (hsum : a + b ≤ max) :
    a + b ≤ max ∧ a + b ≥ 0 := by
  omega

theorem repeated_add_bounded (vals : List Int) (max : Int)
    (_hmax : max ≥ 0)
    (hvals : ∀ v ∈ vals, v ≥ 0)
    (hsum : vals.foldl (· + ·) 0 ≤ max) :
    vals.foldl (· + ·) 0 ≤ max ∧ vals.foldl (· + ·) 0 ≥ 0 := by
  constructor
  · exact hsum
  · rw [← List.sum_eq_foldl]
    exact List.sum_nonneg hvals

def clamp (x minVal maxVal : Int) : Int :=
  if x < minVal then minVal else if x > maxVal then maxVal else x

theorem bounded_mul_with_overflow_check (a b limit : Int)
    (ha_nonneg : a ≥ 0) (hb_nonneg : b ≥ 0)
    (_ha_bound : a ≤ limit) (_hb_bound : b ≤ limit)
    (_hlimit_nonneg : limit ≥ 0)
    (hprod_bound : a * b ≤ limit) :
    0 ≤ a * b ∧ a * b ≤ limit := by
  constructor
  · exact mul_nonneg ha_nonneg hb_nonneg
  · exact hprod_bound

theorem clamp_preserves_order (x minVal maxVal : Int)
    (hmin : minVal ≤ maxVal) :
    minVal ≤ clamp x minVal maxVal ∧ clamp x minVal maxVal ≤ maxVal := by
  unfold clamp
  split
  · omega
  · split <;> omega

theorem round_trip_conversion (x lower upper scale : Int)
    (hlower : lower ≤ x) (hupper : x ≤ upper)
    (_hscale : scale > 0)
    (hdiv : (x * scale) / scale = x) :
    lower ≤ (x * scale) / scale ∧ (x * scale) / scale ≤ upper := by
  omega

theorem sum_invariant (before after : List Int)
    (hperm : before.Perm after) :
    after.sum = before.sum := by
  exact hperm.sum_eq.symm

theorem count_invariant {α : Type} [DecidableEq α] (before after : List α) (target : α)
    (hperm : before.Perm after) :
    (after.filter (· = target)).length = (before.filter (· = target)).length := by
  exact (hperm.filter (fun x => x = target)).length_eq.symm

theorem transfer_preserves_sum (from_bal to_bal amount : Int)
    (hamt : amount ≥ 0) (hfrom : from_bal ≥ amount) :
    (from_bal - amount) + (to_bal + amount) = from_bal + to_bal := by
  have hamount_nonneg : amount ≥ 0 := hamt
  have hfrom_ge : from_bal ≥ amount := hfrom
  omega

theorem list_set_sub_sum (balances : List Int) (i : Nat) (amount : Int)
    (hi : i < balances.length) :
    (balances.set i (balances[i] - amount)).sum = balances.sum - amount := by
  rw [List.sum_set]
  simp [hi]
  have hsplit := List.sum_take_add_sum_drop balances i
  rw [← hsplit]
  omega

theorem list_set_add_sum (balances : List Int) (i : Nat) (amount : Int)
    (hi : i < balances.length) :
    (balances.set i (balances[i] + amount)).sum = balances.sum + amount := by
  rw [List.sum_set]
  simp [hi]
  have hsplit := List.sum_take_add_sum_drop balances i
  rw [← hsplit]
  omega

theorem list_transfer_preserves_sum (balances : List Int) (i j : Nat) (amount : Int)
    (hi : i < balances.length) (hj : j < balances.length) (hij : i ≠ j)
    (hamt : amount ≥ 0) :
    ((balances.set i (balances[i] - amount)).set j (balances[j] + amount)).sum =
      balances.sum := by
  have hj_after : j < (balances.set i (balances[i] - amount)).length := by
    simpa [List.length_set] using hj
  have hget_after : (balances.set i (balances[i] - amount))[j] = balances[j] := by
    rw [List.getElem_set_of_ne]
    exact hij
  rw [← hget_after]
  rw [list_set_add_sum (balances.set i (balances[i] - amount)) j amount hj_after]
  rw [list_set_sub_sum balances i amount hi]
  have hamount_nonneg : amount ≥ 0 := hamt
  omega

theorem monotone_comp {f g : Int → Int}
    (hf : ∀ x y, x ≤ y → f x ≤ f y)
    (hg : ∀ x y, x ≤ y → g x ≤ g y) :
    ∀ x y, x ≤ y → f (g x) ≤ f (g y) := by
  intro x y hxy
  exact hf _ _ (hg _ _ hxy)

theorem counter_monotone (counter : Int) (step : Int)
    (hstep : step > 0) :
    counter + step > counter := by
  omega

end MumeiLean.Patterns
