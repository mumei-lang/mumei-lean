import MumeiLean

/-!
Compile-time regression for the widened tactic search ladder
(`docs/LEAN_TRANSLATOR_SPEC.md` §12.2).

Each example is a goal shape from one of the non-arithmetic classes the ladder
was widened to cover, discharged by the candidate the ladder declares for it.
The goals are stated the way `scripts/ingest_cert.py` renders generated
theorems (`requires → ensures` after `intros`), so a candidate that compiles
here is a candidate the probe module can adopt.
-/

open MumeiLean

namespace TacticLadderDriver

/-- Propositional class (`tauto`): classical guard collapse `aesop` cannot close. -/
example (p q : Int → Prop) (x : Int) : ((p x → q x) → p x) → p x := by
  intros; tauto

/-- List class (`mumei_list`): the recursive `mumei_count` helper is opaque to
`omega`, `aesop` and the generic fallback cascade. -/
example (arr : List Int) (v result : Int) (h_body : result = mumei_count arr v) :
    v ≥ 0 → result ≥ 0 := by
  rw [h_body]; intros; mumei_list

/-- List class (`mumei_list`): length arithmetic through `mumei_len`. -/
example (xs ys : List Int) : (xs ++ ys).length = xs.length + ys.length := by
  intros; mumei_list

/-- Order class (`mumei_order`): product monotonicity, which needs the ordering
lemma applied structurally rather than a linear-arithmetic decision. -/
example (a b c d : Int) (h1 : a ≤ b) (h2 : 0 ≤ c) (h3 : c ≤ d) (h4 : 0 ≤ a) :
    a * c ≤ b * d := by
  intros; mumei_order

/-- Induction class (`mumei_induct`): relating a recursive helper to
`List.length` needs a structural induction step. -/
example (arr : List Int) (v : Int) : mumei_count arr v ≤ (arr.length : Int) := by
  intros; mumei_induct

end TacticLadderDriver
