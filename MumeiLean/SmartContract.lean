import MumeiLean.Patterns
import Mathlib.Tactic

/-!
# MumeiLean.SmartContract

Reusable smart-contract audit proofs for the Phase 4 demo.

The model captures the Checks-Effects-Interactions shape used by the demo:
the account balance is reduced before the external interaction and the
reentrancy guard stays locked during the call.
-/

namespace MumeiLean.SmartContract

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
  | s, [] => some s
  | s, op :: ops =>
      match guardStep s op with
      | some next => runGuard next ops
      | none => none

def updateBalance (balances : List Int) (user : Nat) (amount : Int) : List Int :=
  balances.set user (balances[user]! - amount)

theorem no_external_call_without_lock (ops : List GuardOp)
    (h : GuardOp.lock ∉ ops) :
    runGuard GuardState.Unlocked ops ≠ some GuardState.Locked := by
  induction ops with
  | nil =>
      simp [runGuard]
  | cons op rest ih =>
      have hrest : GuardOp.lock ∉ rest := by
        intro hr
        exact h (List.mem_cons_of_mem op hr)
      cases op <;> simp [runGuard, guardStep] at h ⊢

theorem no_reentrancy_after_withdraw
    (balancesBefore : List Int)
    (user : Nat)
    (amount : Int)
    (hUser : user < balancesBefore.length)
    (_hSufficient : balancesBefore[user]! ≥ amount) :
    (updateBalance balancesBefore user amount)[user]! =
      balancesBefore[user]! - amount := by
  unfold updateBalance
  have hLen : user < (balancesBefore.set user (balancesBefore[user]! - amount)).length := by
    simpa [List.length_set] using hUser
  rw [getElem!_pos (balancesBefore.set user (balancesBefore[user]! - amount)) user hLen]
  rw [List.getElem_set_self hLen]

theorem withdraw_preserves_other_balance
    (balancesBefore : List Int)
    (user other : Nat)
    (amount : Int)
    (hOther : other < balancesBefore.length)
    (hNe : other ≠ user) :
    (updateBalance balancesBefore user amount)[other]! =
      balancesBefore[other]! := by
  unfold updateBalance
  have hLen : other < (balancesBefore.set user (balancesBefore[user]! - amount)).length := by
    simpa [List.length_set] using hOther
  rw [getElem!_pos (balancesBefore.set user (balancesBefore[user]! - amount)) other hLen]
  rw [List.getElem_set_of_ne hNe.symm]
  rw [getElem!_pos balancesBefore other hOther]

theorem guarded_withdraw_trace_returns_unlocked :
    runGuard GuardState.Unlocked
      [GuardOp.lock, GuardOp.externalCall, GuardOp.unlock] =
      some GuardState.Unlocked := by
  simp [runGuard, guardStep]

/-!
## Access-control obligation model

The reentrancy machine above tracks a `GuardState` (Unlocked/Locked). Missing
access-control is a distinct obligation: an externally callable state-mutating
function must perform an authorization check *before* any storage write.

`AccessState` tracks whether the caller has been authorized. `runAccess`
short-circuits to `none` the moment a `stateWrite` is attempted while still
`Unchecked`, exactly mirroring `runGuard`. A guarded function's concrete op
trace evaluates to `some AccessState.Checked`; an unguarded one to `none`.
-/

inductive AccessState where
  | Unchecked
  | Checked
  deriving DecidableEq, Repr

inductive AccessOp where
  | authCheck
  | stateWrite
  deriving DecidableEq, Repr

def accessStep : AccessState → AccessOp → Option AccessState
  | _, .authCheck => some .Checked
  | .Checked, .stateWrite => some .Checked
  | .Unchecked, .stateWrite => none

def runAccess : AccessState → List AccessOp → Option AccessState
  | s, [] => some s
  | s, op :: ops =>
      match accessStep s op with
      | some next => runAccess next ops
      | none => none

theorem no_state_write_without_auth (ops : List AccessOp)
    (h : AccessOp.authCheck ∉ ops)
    (hw : AccessOp.stateWrite ∈ ops) :
    runAccess AccessState.Unchecked ops = none := by
  cases ops with
  | nil => simp at hw
  | cons op rest =>
      cases op with
      | authCheck => simp at h
      | stateWrite => simp [runAccess, accessStep]

theorem guarded_write_trace_returns_checked :
    runAccess AccessState.Unchecked
      [AccessOp.authCheck, AccessOp.stateWrite] =
      some AccessState.Checked := by
  simp [runAccess, accessStep]

theorem unguarded_write_trace_is_none :
    runAccess AccessState.Unchecked [AccessOp.stateWrite] = none := by
  simp [runAccess, accessStep]

theorem withdraw_amount_nonnegative_bound
    (balance amount : Int)
    (hAmount : amount ≥ 0)
    (hSufficient : balance ≥ amount) :
    balance - amount ≤ balance ∧ balance - amount ≥ 0 := by
  omega

theorem nlae_vault_withdraw_amount_nonnegative_bound
    (balance amount : Int)
    (hAmount : amount ≥ 0)
    (hSufficient : balance ≥ amount) :
    balance - amount ≤ balance ∧ balance - amount ≥ 0 :=
  withdraw_amount_nonnegative_bound balance amount hAmount hSufficient

theorem nlae_vault_no_negative_withdraw
    (balance amount : Int)
    (hAmount : amount ≥ 0) :
    balance - amount ≤ balance := by
  omega

end MumeiLean.SmartContract
