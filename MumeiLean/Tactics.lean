import Mathlib.Tactic

/-!
# MumeiLean.Tactics

mathlib4-backed tactic combinators reused by the Lean theorems that
`scripts/ingest_cert.py` generates from mumei `unknown` atoms.

The bridge previously emitted `sorry` as the proof body for every
generated theorem, which forced every contract — even purely
arithmetic ones — to be hand-proven. PR 4 wires up `mumei_arith`
instead: a small `first` cascade over the four mathlib tactics that
between them discharge most of the obligations the mumei verifier
flags as `unknown` (linear arithmetic, congruence, normalisation, and
generic simp closure).

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

Tries `omega`, then `linarith`, then `norm_num`, then `simp`. The
final `simp` always succeeds (it may simplify rather than close the
goal), which means `mumei_arith` itself never fails — it just leaves
unsolved subgoals for the caller to dispatch (e.g. via
`<;> sorry`).
-/
macro "mumei_arith" : tactic =>
  `(tactic| (intros; first | omega | linarith | norm_num | simp))

end MumeiLean
