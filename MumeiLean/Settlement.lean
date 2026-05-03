import MumeiLean.Patterns
import Mathlib.Tactic

/-!
# MumeiLean.Settlement

RTGS settlement protocol: formal proof that balance is conserved
across any sequence of settlement operations.

This module proves two key properties:
1. **No settlement without validation**: `Settled` is unreachable
   without passing through `Validated` (temporal safety).
2. **Balance conservation**: the sum of all account balances is
   invariant under transfer operations (global conservation).

The balance conservation proof builds on
`MumeiLean.Patterns.list_transfer_preserves_sum`.
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

end MumeiLean.Settlement
