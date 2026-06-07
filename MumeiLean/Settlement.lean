import MumeiLean.Patterns
import Mathlib.Tactic

/-!
# MumeiLean.Settlement

RTGS settlement protocol: formal proof that balance is conserved
across any sequence of settlement operations.

This module proves RTGS safety properties:
1. **No settlement without validation**: `Settled` is unreachable
   without passing through `Validated` (temporal safety).
2. **Balance conservation**: the sum of all account balances is
   invariant under any sequence of transfer operations (global
   conservation).
3. **Queue termination and affected-account non-negativity** for the
   finite settlement queue model.

The balance conservation proof builds on
`MumeiLean.Patterns.list_transfer_preserves_sum`.

## Scope and non-goals

This module proves only the **global sum** is invariant under transfers.
The following properties are intentionally **out of scope** and are left
for future modules:

* **Rejection of validated transactions** — `step` only allows `reject`
  from `Pending`, not from `Validated`. Extending the state machine is
  orthogonal to the conservation proof.
-/

namespace MumeiLean.Settlement

-- ============================================================
-- Part 1: State machine — temporal safety
-- ============================================================

inductive State where
  | Pending
  | Validated
  | Settled
  deriving DecidableEq, Repr

inductive Op where
  | validate
  | settle
  | reject
  deriving DecidableEq, Repr

def step : State → Op → Option State
  | .Pending, .validate => some .Validated
  | .Validated, .settle => some .Settled
  | .Pending, .reject => some .Pending
  | _, _ => none

def run : State → List Op → Option State
  | s, [] => some s
  | s, op :: ops =>
      match step s op with
      | some next => run next ops
      | none => none

theorem no_settlement_without_validate_from_non_validated
    (s : State) (ops : List Op)
    (hs : s ≠ State.Validated) (hs2 : s ≠ State.Settled)
    (h : Op.validate ∉ ops) :
    run s ops ≠ some State.Settled := by
  induction ops generalizing s with
  | nil =>
      cases s <;> simp [run] at hs hs2 ⊢
  | cons op rest ih =>
      have hrest : Op.validate ∉ rest := by
        intro hr
        exact h (List.mem_cons_of_mem op hr)
      cases s <;> cases op <;> simp [run, step] at h hs hs2 ⊢
      · exact ih State.Pending (by simp) (by simp) hrest

theorem no_settlement_without_validate
    (ops : List Op)
    (h : Op.validate ∉ ops) :
    run State.Pending ops ≠ some State.Settled :=
  no_settlement_without_validate_from_non_validated
    State.Pending ops (by simp) (by simp) h

-- ============================================================
-- Part 2: Balance conservation
-- ============================================================

structure Transfer where
  from_idx : Nat
  to_idx : Nat
  amount : Int
  h_amount : amount ≥ 0

def apply_transfer (balances : List Int) (t : Transfer)
    (hf : t.from_idx < balances.length) (_ht : t.to_idx < balances.length)
    (_hne : t.from_idx ≠ t.to_idx) : List Int :=
  (balances.set t.from_idx (balances[t.from_idx] - t.amount)).set
    t.to_idx (balances[t.to_idx] + t.amount)

theorem single_transfer_preserves_sum (balances : List Int) (t : Transfer)
    (hf : t.from_idx < balances.length) (ht : t.to_idx < balances.length)
    (hne : t.from_idx ≠ t.to_idx) :
    (apply_transfer balances t hf ht hne).sum = balances.sum := by
  unfold apply_transfer
  exact MumeiLean.Patterns.list_transfer_preserves_sum
    balances t.from_idx t.to_idx t.amount hf ht hne t.h_amount

structure ValidTransfer (balances : List Int) where
  transfer : Transfer
  h_from : transfer.from_idx < balances.length
  h_to : transfer.to_idx < balances.length
  h_ne : transfer.from_idx ≠ transfer.to_idx

def apply_valid_transfer (balances : List Int) (t : ValidTransfer balances) : List Int :=
  apply_transfer balances t.transfer t.h_from t.h_to t.h_ne

theorem valid_transfer_preserves_sum (balances : List Int) (t : ValidTransfer balances) :
    (apply_valid_transfer balances t).sum = balances.sum := by
  exact single_transfer_preserves_sum
    balances t.transfer t.h_from t.h_to t.h_ne

theorem balance_conservation
    (balances : List Int) (from_idx to_idx : Nat) (amount : Int)
    (h_amount : amount > 0)
    (h_from_idx : from_idx < balances.length)
    (h_to_idx : to_idx < balances.length)
    (h_distinct : from_idx ≠ to_idx)
    (_h_from_balance : balances.get! from_idx ≥ amount) :
    ((balances.set from_idx (balances.get! from_idx - amount)).set
      to_idx (balances.get! to_idx + amount)).sum = balances.sum := by
  have h_from_get : balances.get! from_idx = balances[from_idx] := by
    simpa [List.get!_eq_getD] using
      (List.getD_eq_getElem balances (default : Int) h_from_idx)
  have h_to_get : balances.get! to_idx = balances[to_idx] := by
    simpa [List.get!_eq_getD] using
      (List.getD_eq_getElem balances (default : Int) h_to_idx)
  rw [h_from_get, h_to_get]
  exact MumeiLean.Patterns.list_transfer_preserves_sum
    balances from_idx to_idx amount h_from_idx h_to_idx h_distinct (by omega)

def process_queue (balances : List Int) : List Transfer → List Int
  | [] => balances
  | t :: rest =>
      if h_from : t.from_idx < balances.length then
        if h_to : t.to_idx < balances.length then
          if h_distinct : t.from_idx ≠ t.to_idx then
            process_queue (apply_transfer balances t h_from h_to h_distinct) rest
          else
            process_queue balances rest
        else
          process_queue balances rest
      else
        process_queue balances rest
termination_by queue => queue.length
decreasing_by
  all_goals simp_wf

theorem settlement_terminates (balances : List Int) (queue : List Transfer) :
    ∃ final, process_queue balances queue = final := by
  exact ⟨process_queue balances queue, rfl⟩

theorem affected_accounts_nonnegative
    (from_balance to_balance amount : Int)
    (h_amount : amount ≥ 0)
    (h_from_balance : from_balance ≥ amount)
    (h_to_balance : to_balance ≥ 0) :
    from_balance - amount ≥ 0 ∧ to_balance + amount ≥ 0 := by
  constructor <;> linarith

theorem no_negative_balance
    (balances : List Int) (from_idx to_idx : Nat) (amount : Int)
    (h_amount : amount ≥ 0)
    (h_from_idx : from_idx < balances.length)
    (h_to_idx : to_idx < balances.length)
    (h_all_nonnegative : ∀ i (hi : i < balances.length), balances[i] ≥ 0)
    (h_from_balance : balances.get! from_idx ≥ amount) :
    ∀ i
      (hi : i < ((balances.set from_idx (balances[from_idx] - amount)).set
        to_idx (balances[to_idx] + amount)).length),
      ((balances.set from_idx (balances[from_idx] - amount)).set
        to_idx (balances[to_idx] + amount))[i] ≥ 0 := by
  have h_from_get : balances.get! from_idx = balances[from_idx] := by
    simpa [List.get!_eq_getD] using
      (List.getD_eq_getElem balances (default : Int) h_from_idx)
  rw [h_from_get] at h_from_balance
  intro i hi
  have hi_orig : i < balances.length := by
    simpa [List.length_set] using hi
  by_cases h_to : i = to_idx
  · subst i
    rw [List.getElem_set_self]
    exact (affected_accounts_nonnegative
      balances[from_idx] balances[to_idx] amount h_amount h_from_balance
      (h_all_nonnegative to_idx h_to_idx)).2
  · have h_to_ne : to_idx ≠ i := by
      intro h
      exact h_to h.symm
    have hi_after : i < (balances.set from_idx (balances[from_idx] - amount)).length := by
      simpa [List.length_set] using hi_orig
    rw [List.getElem_set_of_ne h_to_ne (balances[to_idx] + amount) hi]
    by_cases h_from : i = from_idx
    · subst i
      rw [List.getElem_set_self]
      exact (affected_accounts_nonnegative
        balances[from_idx] balances[to_idx] amount h_amount h_from_balance
        (h_all_nonnegative to_idx h_to_idx)).1
    · have h_from_ne : from_idx ≠ i := by
        intro h
        exact h_from h.symm
      rw [List.getElem_set_of_ne h_from_ne (balances[from_idx] - amount) hi_after]
      exact h_all_nonnegative i hi_orig

inductive TransferTrace : List Int → List Int → Type where
  | nil (balances : List Int) : TransferTrace balances balances
  | cons {before after final : List Int} (t : ValidTransfer before)
      (h_after : after = apply_valid_transfer before t)
      (rest : TransferTrace after final) : TransferTrace before final

theorem trace_balance_conservation {initial final : List Int}
    (trace : TransferTrace initial final) :
    final.sum = initial.sum := by
  induction trace with
  | nil balances =>
      simp
  | cons t h_after rest ih =>
      rw [ih, h_after]
      exact valid_transfer_preserves_sum _ t

end MumeiLean.Settlement
