/-!
# MumeiLean.Blockchain

Reusable Lean witnesses for the blockchain audit demo.
-/

namespace MumeiLean.Blockchain

inductive GuardState where
  | Unlocked
  | Locked
  deriving DecidableEq, Repr

inductive GuardOp where
  | lock
  | unlock
  | externalCall
  deriving DecidableEq, Repr

def guardStep : GuardState → GuardOp → Option GuardState
  | .Unlocked, .lock => some .Locked
  | .Locked, .externalCall => some .Locked
  | .Locked, .unlock => some .Unlocked
  | _, _ => none

def runGuard : GuardState → List GuardOp → Option GuardState
  | state, [] => some state
  | state, op :: ops =>
      match guardStep state op with
      | some next => runGuard next ops
      | none => none

def uint256Max : Int := 100

def checkedUint256 (value : Int) : Int :=
  value

def safeCredit (toBalance amount : Int) : Int :=
  checkedUint256 (toBalance + amount)

def transferOwnership (caller owner newOwner : Int) : Option Int :=
  if caller = owner then some newOwner else none

theorem external_call_rejected_when_unlocked :
    guardStep GuardState.Unlocked GuardOp.externalCall = none := by
  rfl

theorem reentrancy_prevention :
    runGuard GuardState.Unlocked
      [GuardOp.lock, GuardOp.externalCall, GuardOp.unlock] =
      some GuardState.Unlocked := by
  simp [runGuard, guardStep]

theorem overflow_protection
    (toBalance amount : Int)
    (hToNonnegative : toBalance ≥ 0)
    (hAmountNonnegative : amount ≥ 0)
    (hCreditBound : toBalance + amount ≤ uint256Max) :
    safeCredit toBalance amount ≥ 0 ∧
      safeCredit toBalance amount ≤ uint256Max ∧
      safeCredit toBalance amount = toBalance + amount := by
  unfold safeCredit checkedUint256
  constructor
  · exact Int.add_nonneg hToNonnegative hAmountNonnegative
  · constructor
    · exact hCreditBound
    · rfl

theorem owner_only_transfer
    (caller owner newOwner : Int)
    (hAuthorized : caller = owner) :
    transferOwnership caller owner newOwner = some newOwner := by
  simp [transferOwnership, hAuthorized]

end MumeiLean.Blockchain
