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

-- New: field identity elements
def mumei_ff_zero (_p : Int) : Int := 0

def mumei_ff_one (_p : Int) : Int := 1

-- New: field equality modulo p
def mumei_ff_eq (a b p : Int) : Prop :=
  a % p = b % p

def mumei_group_mul (a b : Int) : Int :=
  a * b

def mumei_group_inv (a : Int) : Int :=
  -a

def mumei_group_pow (a n : Int) : Int :=
  a ^ n.toNat

def mumei_group_identity : Int :=
  0

-- New: group order (abstract, axiomatized as input parameter)
def mumei_group_order (g : Int) : Int := g

-- New: commutativity check (for abelian groups)
def mumei_group_comm (a b : Int) : Prop :=
  mumei_group_mul a b = mumei_group_mul b a

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

-- New: subtraction closure
theorem ff_sub_in_field (a b p : Int) (hp : 0 < p) :
    mumei_ff_in_field (mumei_ff_sub a b p) p := by
  unfold mumei_ff_in_field mumei_ff_sub
  constructor
  · exact Int.emod_nonneg (a - b) (ne_of_gt hp)
  · exact Int.emod_lt_of_pos (a - b) hp

-- New: negation closure
theorem ff_neg_in_field (a p : Int) (hp : 0 < p) :
    mumei_ff_in_field (mumei_ff_neg a p) p := by
  unfold mumei_ff_in_field mumei_ff_neg
  constructor
  · exact Int.emod_nonneg (-a) (ne_of_gt hp)
  · exact Int.emod_lt_of_pos (-a) hp

-- New: zero is in field
theorem ff_zero_in_field (p : Int) (hp : 0 < p) :
    mumei_ff_in_field (mumei_ff_zero p) p := by
  unfold mumei_ff_in_field mumei_ff_zero
  exact ⟨le_refl 0, hp⟩

-- New: additive identity
theorem ff_add_zero (a p : Int) :
    mumei_ff_add a (mumei_ff_zero p) p = a % p := by
  unfold mumei_ff_add mumei_ff_zero
  simp

-- New: multiplicative identity
theorem ff_mul_one (a p : Int) :
    mumei_ff_mul a (mumei_ff_one p) p = a % p := by
  unfold mumei_ff_mul mumei_ff_one
  simp

-- New: ff_eq reflexivity
theorem ff_eq_refl (a p : Int) :
    mumei_ff_eq a a p := by
  unfold mumei_ff_eq
  rfl

-- New: commutativity of field add
theorem ff_add_comm (a b p : Int) :
    mumei_ff_add a b p = mumei_ff_add b a p := by
  unfold mumei_ff_add
  ring

-- New: commutativity of field mul
theorem ff_mul_comm (a b p : Int) :
    mumei_ff_mul a b p = mumei_ff_mul b a p := by
  unfold mumei_ff_mul
  ring

-- New: distributivity
theorem ff_mul_add_distrib (a b c p : Int) :
    mumei_ff_mul a (mumei_ff_add b c p) p =
    (a * ((b + c) % p)) % p := by
  unfold mumei_ff_mul mumei_ff_add
  rfl

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

-- New: right inverse
theorem group_right_inv {G : Type u} [Group G] (a : G) :
    a * a⁻¹ = 1 := by
  simp

-- New: identity laws
theorem group_mul_one {G : Type u} [Group G] (a : G) :
    a * 1 = a := by
  simp

theorem group_one_mul {G : Type u} [Group G] (a : G) :
    1 * a = a := by
  simp

-- New: inverse of inverse
theorem group_inv_inv {G : Type u} [Group G] (a : G) :
    a⁻¹⁻¹ = a := by
  simp

-- New: inverse of product
theorem group_mul_inv_rev {G : Type u} [Group G] (a b : G) :
    (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  simp [mul_inv_rev]

-- New: group commutativity witness for Int
theorem mumei_group_comm_int (a b : Int) :
    mumei_group_comm a b := by
  unfold mumei_group_comm mumei_group_mul
  ring

end MumeiLean.Algebra
