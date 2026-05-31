/-!
# MumeiLean.DeFi

Lean witness module for the Phase 5 DeFi Invariant demo.
-/

namespace MumeiLean.DeFi

def uint256Max : Int := 100

def checkedUint256 (value : Int) : Int :=
  value

def safeTransfer (_fromBalance toBalance amount : Int) : Int :=
  checkedUint256 (toBalance + amount)

theorem safe_transfer_preserves_uint256
    (fromBalance toBalance amount : Int)
    (_hFrom : fromBalance ≥ amount)
    (hToNonnegative : toBalance ≥ 0)
    (hAmountNonnegative : amount ≥ 0)
    (hCreditBound : toBalance + amount ≤ uint256Max) :
    safeTransfer fromBalance toBalance amount ≥ 0 ∧
      safeTransfer fromBalance toBalance amount ≤ uint256Max ∧
      safeTransfer fromBalance toBalance amount = toBalance + amount := by
  unfold safeTransfer checkedUint256
  constructor
  · exact Int.add_nonneg hToNonnegative hAmountNonnegative
  · constructor
    · exact hCreditBound
    · rfl

end MumeiLean.DeFi
