import Mathlib.Tactic
import MumeiLean.Algebra

/-!
# MumeiLean.Tactics

mathlib4-backed tactic combinators reused by the Lean theorems that
`scripts/ingest_cert.py` generates from mumei `unknown` atoms.

The bridge previously emitted `sorry` as the proof body for every
generated theorem, which forced every contract — even purely
arithmetic ones — to be hand-proven. PR 4 wires up `mumei_arith`
instead: a small `first` cascade over the five mathlib tactics that
between them discharge most of the obligations the mumei verifier
flags as `unknown` (linear arithmetic, congruence, normalisation,
finite-state decidability, and generic simp closure).

`scripts/ingest_cert.py` emits

```
  mumei_arith <;> sorry
```

as the default body so theorems `mumei_arith` cannot fully close still
type-check (with a `sorry` warning that `scripts/export_cert.py` reads
as a failure marker). When `mumei_arith` discharges every subgoal the
`sorry` is unreachable, no warning is emitted, and the bridge marks
the atom as `lean_verified` in the resulting `.lean-cert.json`.
-/

namespace MumeiLean

/-- Combined tactic for mumei arithmetic obligations.

Tries `omega`, then `linarith`, then `nlinarith`, then `norm_num`, then
`ring1` / `ring_nf`, then `field_simp`, then `decide`, then `simp`. The
`ring1` and `field_simp` stages close the commutative-ring and
finite-field/division-shaped goals emitted by the finite-field and
crypto lowering rules. The `decide` stage discharges finite-state machine properties
when all relevant propositions have `Decidable` instances. The final
`simp` always succeeds (it may simplify rather than close the goal),
which means `mumei_arith` itself never fails — it just leaves unsolved
subgoals for the caller to dispatch (e.g. via `<;> sorry`).
-/
macro "mumei_arith" : tactic =>
  `(tactic|
    (intros
     first
     | omega
     | linarith
     | nlinarith
     | norm_num
     | ring1
     | ring_nf
     | field_simp
     | decide
     | split
     | (cases ‹_›)
     | (rcases ‹_› with ⟨_, _⟩)
     | simp))

/-- Deeper arithmetic automation for generated theorems that unfold body semantics. -/
macro "mumei_arith_deep" : tactic =>
  `(tactic|
    (intros
     first
     | omega
     | linarith
     | nlinarith
     | (repeat' constructor <;> first | positivity | nlinarith | ring)
     | norm_num
     | ring1
     | ring_nf
     | field_simp
     | decide
     | (simp; omega)
     | (simp; repeat' constructor <;> first | positivity | nlinarith | ring)
     | (split <;> omega)
     | (cases ‹_›; omega)
     | (rcases ‹_› with ⟨_, _⟩; omega)))

/-- Mathlib-oriented fallback for algebraic generated goals. -/
macro "mumei_mathlib" : tactic =>
  `(tactic|
    (intros
     first
     | ring_nf
     | field_simp
     | group
     | aesop
     | simp))

/-- Finite-field / group automation for generated theorems whose goal is stated
through the `MumeiLean.Algebra` helpers.

The helpers are definitions over `Int` residues, so the cascade first unfolds
the finite-field carrier and then normalises with `ring1` / `field_simp`; the
`group` stage covers goals stated in a mathlib `Group`. Like `mumei_arith` the
final `simp` always succeeds, so the tactic never fails outright. -/
macro "mumei_field" : tactic =>
  `(tactic|
    (intros
     first
     | ring1
     | (simp only [MumeiLean.Algebra.mumei_ff_eq, MumeiLean.Algebra.mumei_ff_add,
          MumeiLean.Algebra.mumei_ff_mul] <;> ring_nf)
     | group
     | field_simp
     | ring_nf
     | omega
     | simp))

end MumeiLean
