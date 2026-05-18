import Mathlib.Tactic
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.NatPrime
import Mathlib.Data.ZMod.Basic

/-!
# MumeiLean.Algebra

Mathlib-backed helpers for finite-field and group-theory expressions emitted by
`scripts/expr_translator.py`.
-/

namespace MumeiLean.Algebra

universe u

abbrev MumeiFF (p : Nat) := ZMod p

def mumei_ff_add (a b p : Int) : Int :=
  (a + b) % p

def mumei_ff_sub (a b p : Int) : Int :=
  (a - b) % p

def mumei_ff_mul (a b p : Int) : Int :=
  (a * b) % p

def mumei_ff_neg (a p : Int) : Int :=
  (-a) % p

def mumei_ff_pow (a e p : Int) : Int :=
  (a ^ e.toNat) % p

def mumei_ff_inv (a p : Int) : Int :=
  if a = 0 then 0 else (a ^ (p - 2).toNat) % p

def mumei_ff_div (a b p : Int) : Int :=
  mumei_ff_mul a (mumei_ff_inv b p) p

def mumei_ff_in_field (a p : Int) : Prop :=
  0 ≤ a ∧ a < p

def mumei_is_prime (p : Int) : Prop :=
  Nat.Prime p.natAbs

def mumei_mod_eq (a b p : Int) : Prop :=
  a ≡ b [ZMOD p]

def mumei_group_mul (a b : Int) : Int :=
  a * b

def mumei_group_inv (a : Int) : Int :=
  -a

def mumei_group_pow (a n : Int) : Int :=
  a ^ n.toNat

def mumei_group_identity : Int :=
  0

theorem ff_add_in_field (a b p : Int) (hp : 0 < p) :
    mumei_ff_in_field (mumei_ff_add a b p) p := by
  unfold mumei_ff_in_field mumei_ff_add
  constructor
  · exact Int.emod_nonneg (a + b) (ne_of_gt hp)
  · exact Int.emod_lt_of_pos (a + b) hp

theorem ff_mul_in_field (a b p : Int) (hp : 0 < p) :
    mumei_ff_in_field (mumei_ff_mul a b p) p := by
  unfold mumei_ff_in_field mumei_ff_mul
  constructor
  · exact Int.emod_nonneg (a * b) (ne_of_gt hp)
  · exact Int.emod_lt_of_pos (a * b) hp

theorem zmod_add_comm (p : Nat) (a b : MumeiFF p) :
    a + b = b + a := by
  simpa using add_comm a b

theorem zmod_mul_assoc (p : Nat) (a b c : MumeiFF p) :
    (a * b) * c = a * (b * c) := by
  ring

theorem group_mul_assoc {G : Type u} [Group G] (a b c : G) :
    (a * b) * c = a * (b * c) := by
  simp [mul_assoc]

theorem group_left_inv {G : Type u} [Group G] (a : G) :
    a⁻¹ * a = 1 := by
  simp

end MumeiLean.Algebra
