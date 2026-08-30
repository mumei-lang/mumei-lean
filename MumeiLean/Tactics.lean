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

/-- Modular normalisation for finite-field goals stated through the
`MumeiLean.Algebra.mumei_ff_*` helpers over `Int` residues.

The helpers reduce modulo `p` at every step, so goals such as finite-field
distributivity and associativity carry one `% p` per operation, which `ring_nf`
alone cannot merge. This stage unfolds the helpers and collapses every inner
reduction with the `MumeiLean.Algebra.emod_{mul,add}_emod_*` lemmas, leaving a
single `polynomial % p` on each side, then compares the two polynomials.

It is the `mumei_ff_mod` entry of the automatic tactic search ladder
(`docs/LEAN_TRANSLATOR_SPEC.md` §12.2). -/
macro "mumei_ff_mod" : tactic =>
  `(tactic|
    (simp only [MumeiLean.Algebra.mumei_ff_eq, MumeiLean.Algebra.mumei_ff_add,
       MumeiLean.Algebra.mumei_ff_sub, MumeiLean.Algebra.mumei_ff_mul,
       Int.emod_emod_of_dvd _ (dvd_refl _),
       MumeiLean.Algebra.emod_mul_emod_left,
       MumeiLean.Algebra.emod_mul_emod_right,
       MumeiLean.Algebra.emod_add_emod_left,
       MumeiLean.Algebra.emod_add_emod_right]
     first
     | done
     | rfl
     | (ring_nf; done)
     | (rw [mul_assoc]; done)
     | (rw [mul_add]; done)
     | omega))

/-- Modular normalisation for finite-field goals whose terms also contain
`MumeiLean.Algebra.mumei_ff_pow` exponentiations.

`mumei_ff_pow a e p` reduces to `a ^ e.toNat % p`, so a goal relating a power to
its expansion carries both a `Int.toNat` literal and a reduction under the
exponent. `mumei_ff_mod` leaves those in place: neither the literal nor
`(a % p) ^ n % p` is covered by its rewrite set. This stage adds the `toNat`
literal reduction and `MumeiLean.Algebra.emod_pow_emod` so that a power term
also collapses into a single `polynomial % p`, then compares polynomials.

It is the `mumei_ff_pow` entry of the automatic tactic search ladder
(`docs/LEAN_TRANSLATOR_SPEC.md` §12.2). -/
macro "mumei_ff_pow" : tactic =>
  `(tactic|
    (simp only [MumeiLean.Algebra.mumei_ff_eq, MumeiLean.Algebra.mumei_ff_add,
       MumeiLean.Algebra.mumei_ff_sub, MumeiLean.Algebra.mumei_ff_mul,
       MumeiLean.Algebra.mumei_ff_pow, MumeiLean.Algebra.mumei_ff_one,
       MumeiLean.Algebra.mumei_ff_zero, Int.reduceToNat,
       Int.emod_emod_of_dvd _ (dvd_refl _),
       MumeiLean.Algebra.emod_mul_emod_left,
       MumeiLean.Algebra.emod_mul_emod_right,
       MumeiLean.Algebra.emod_add_emod_left,
       MumeiLean.Algebra.emod_add_emod_right,
       MumeiLean.Algebra.emod_pow_emod]
     first
     | done
     | rfl
     | (ring_nf; done)
     | omega))

/-- List automation for generated goals stated through the `MumeiLean`
list helpers (`mumei_count`, `mumei_sum`, `mumei_len`).

The helpers are plain definitions, so neither `omega` nor `aesop` can see
through them: the goal `0 ≤ mumei_count arr v` is an opaque atom for both. This
stage unfolds the helpers together with the structural `List.length` /
`List.mem` simp lemmas and closes the resulting arithmetic goal.

It is the `mumei_list` entry of the automatic tactic search ladder
(`docs/LEAN_TRANSLATOR_SPEC.md` §12.2). -/
macro "mumei_list" : tactic =>
  `(tactic|
    (try simp only [ge_iff_le, MumeiLean.mumei_count, MumeiLean.mumei_sum,
       MumeiLean.mumei_len, List.length_append, List.length_reverse,
       List.length_cons, List.length_nil, List.mem_append, List.mem_cons]
     first
     | omega
     | exact Int.ofNat_nonneg _
     | positivity
     | (simp_all; done)
     | (simp; done)))

/-- Order/lattice automation for generated goals whose shape is a `≤` / `<`
chain rather than a linear-arithmetic identity.

`omega` already decides linear `min` / `max` goals over `Int`, so this stage
covers what it cannot: transitivity through hypotheses and monotonicity of
products, where the ordering steps have to be applied structurally.

It is the `mumei_order` entry of the automatic tactic search ladder
(`docs/LEAN_TRANSLATOR_SPEC.md` §12.2). -/
macro "mumei_order" : tactic =>
  `(tactic|
    (try simp only [ge_iff_le, min_def, max_def]
     first
     | omega
     | (split_ifs <;> omega)
     | (apply le_trans <;> assumption)
     | (apply mul_le_mul <;>
        first | assumption | positivity | omega | linarith)
     | (gcongr <;> first | assumption | positivity | omega | linarith)))

/-!
## `mumei_induct`

Structural induction for generated goals over a list or natural-number
binder.

Recursive helpers such as `mumei_count` only reduce once their list argument is
in constructor form, so goals relating them to `List.length` need an induction
step no closing tactic in the ladder performs. The binder is selected by type
(`‹List Int›`, then `‹Nat›`), which keeps the tactic deterministic without
naming the binder in the generated proof.

It is the `mumei_induct` entry of the automatic tactic search ladder
(`docs/LEAN_TRANSLATOR_SPEC.md` §12.2).

`hygiene` is disabled for this macro only: `‹List Int›` has to resolve against
the *caller's* local context to pick the binder to induct on. -/
set_option hygiene false in
macro "mumei_induct" : tactic =>
  `(tactic|
    (first
     | (induction ‹List Int› <;>
        simp_all [MumeiLean.mumei_count, MumeiLean.mumei_sum, List.filter] <;>
        split <;> simp_all <;> omega)
     | (induction ‹List Int› <;> simp_all <;> omega)
     | (induction ‹Nat› <;> simp_all <;> omega)))

end MumeiLean
