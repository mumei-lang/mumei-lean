import MumeiLean.Basic

/-!
# MumeiLean.Ownership

Lean model of the Phase 1 Ownership Transfer Protocol demo in
`std/ownership.mm`.

The protocol has three states. A transfer can only reach `Transferred`
through the `accept` operation after a pending transfer has been proposed.
The main theorem proves that any operation trace without `accept` cannot
reach `Transferred` from `Idle`; the helper theorem gives the same property
from `PendingTransfer`.
-/

namespace MumeiLean.Ownership

inductive State
  | Idle
  | PendingTransfer
  | Transferred
  deriving DecidableEq, Repr

inductive Op
  | propose
  | accept
  | cancel
  deriving DecidableEq, Repr

def step : State → Op → Option State
  | .Idle, .propose => some .PendingTransfer
  | .Idle, .accept => none
  | .Idle, .cancel => none
  | .PendingTransfer, .propose => none
  | .PendingTransfer, .accept => some .Transferred
  | .PendingTransfer, .cancel => some .Idle
  | .Transferred, .propose => none
  | .Transferred, .accept => none
  | .Transferred, .cancel => none

def run : State → List Op → Option State
  | s, [] => some s
  | s, op :: ops =>
      match step s op with
      | some next => run next ops
      | none => none

theorem no_transfer_without_accept_from_nontransferred
    (s : State) (ops : List Op)
    (hs : s ≠ State.Transferred)
    (h : Op.accept ∉ ops) :
    run s ops ≠ some State.Transferred := by
  induction ops generalizing s with
  | nil =>
      cases s <;> simp [run] at hs ⊢
  | cons op rest ih =>
      have hrest : Op.accept ∉ rest := by
        intro hr
        exact h (List.mem_cons_of_mem op hr)
      cases s <;> cases op <;> simp [run, step] at h hs ⊢
      · exact ih State.PendingTransfer (by simp) hrest
      · exact ih State.Idle (by simp) hrest

theorem no_transfer_without_accept_from_pending
    (ops : List Op)
    (h : Op.accept ∉ ops) :
    run State.PendingTransfer ops ≠ some State.Transferred :=
  no_transfer_without_accept_from_nontransferred
    State.PendingTransfer ops (by simp) h

theorem no_transfer_without_accept
    (ops : List Op)
    (h : Op.accept ∉ ops) :
    run State.Idle ops ≠ some State.Transferred :=
  no_transfer_without_accept_from_nontransferred
    State.Idle ops (by simp) h

end MumeiLean.Ownership
