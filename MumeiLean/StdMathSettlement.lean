import Mathlib.Tactic

/-!
# MumeiLean.StdMathSettlement

Reusable settlement and smart-contract arithmetic lemmas for frequently
escalated standard-library proof obligations.
-/

namespace MumeiLean.StdMathSettlement

theorem safe_add_bounded (a b max : Int)
    (ha : a ≥ 0) (hb : b ≥ 0) (hbound : a + b ≤ max) :
    a + b ≥ 0 ∧ a + b ≤ max := by
  constructor <;> omega

theorem conservation_law (a b x : Int) :
    (a - x) + (b + x) = a + b := by
  omega

theorem monotone_transfer (from_balance to_balance amount₁ amount₂ : Int)
    (h_amounts : amount₁ ≤ amount₂) :
    from_balance - amount₂ ≤ from_balance - amount₁ ∧
      to_balance + amount₁ ≤ to_balance + amount₂ := by
  constructor <;> omega

end MumeiLean.StdMathSettlement
