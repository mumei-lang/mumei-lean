import MumeiLean.Basic

/-!
# MumeiLean.Concurrency

Value-level bridge lemmas for Mumei's structured-concurrency surface
(`task { … }`, `task_group:all { … }`, `task_group:any { … }`).

These lemmas back the `concurrency_obligation` class in
`docs/LEAN_TRANSLATOR_SPEC.md` §10: the translator lowers a `task_group:all`
body to its last task's value and a `task_group:any` body to list
membership over the task results, and these declarations make that
semantics explicit in the trusted kernel.
-/

namespace MumeiLean.Concurrency

/-- A bare `task { e }` evaluates to its body's value. -/
def taskValue (v : Int) : Int :=
  v

/-- `task_group:all { task { e₁ }; …; task { eₙ } }` runs all children to
completion and yields the last task's value `eₙ`. -/
def taskGroupAll (xs : List Int) (h : xs ≠ []) : Int :=
  xs.getLast h

/-- `task_group:any { task { e₁ }; …; task { eₙ } }` yields whichever task
finishes first, so its result is some member of the result list. -/
def taskGroupAnyResult (xs : List Int) (r : Int) : Prop :=
  r ∈ xs

/-- The group value of `task_group:all` is exactly the last entry. -/
theorem task_group_all_result_last (xs : List Int) (h : xs ≠ [])
    (P : Int → Prop) (hp : P (xs.getLast h)) : P (taskGroupAll xs h) :=
  hp

/-- `task_group:any` case split: if every member of the task results list
satisfies `P`, then so does the group's result. -/
theorem task_group_any_result_mem (xs : List Int) (P : Int → Prop) (r : Int)
    (mem : taskGroupAnyResult xs r) (all : ∀ v ∈ xs, P v) : P r :=
  all r mem

/-- A bare `task` body is the value itself. -/
theorem task_value_result (v : Int) (P : Int → Prop) (hp : P v) :
    P (taskValue v) :=
  hp

end MumeiLean.Concurrency
