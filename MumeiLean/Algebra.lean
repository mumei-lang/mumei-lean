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

-- field identity elements
def mumei_ff_zero (_p : Int) : Int := 0

def mumei_ff_one (_p : Int) : Int := 1

-- field equality modulo p
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

-- group order (abstract, axiomatized as input parameter)
def mumei_group_order (g : Int) : Int := g

-- commutativity check (for abelian groups)
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

-- subtraction closure
theorem ff_sub_in_field (a b p : Int) (hp : 0 < p) :
    mumei_ff_in_field (mumei_ff_sub a b p) p := by
  unfold mumei_ff_in_field mumei_ff_sub
  constructor
  · exact Int.emod_nonneg (a - b) (ne_of_gt hp)
  · exact Int.emod_lt_of_pos (a - b) hp

-- negation closure
theorem ff_neg_in_field (a p : Int) (hp : 0 < p) :
    mumei_ff_in_field (mumei_ff_neg a p) p := by
  unfold mumei_ff_in_field mumei_ff_neg
  constructor
  · exact Int.emod_nonneg (-a) (ne_of_gt hp)
  · exact Int.emod_lt_of_pos (-a) hp

-- zero is in field
theorem ff_zero_in_field (p : Int) (hp : 0 < p) :
    mumei_ff_in_field (mumei_ff_zero p) p := by
  unfold mumei_ff_in_field mumei_ff_zero
  exact ⟨le_refl 0, hp⟩

-- additive identity
theorem ff_add_zero (a p : Int) :
    mumei_ff_add a (mumei_ff_zero p) p = a % p := by
  unfold mumei_ff_add mumei_ff_zero
  simp

-- multiplicative identity
theorem ff_mul_one (a p : Int) :
    mumei_ff_mul a (mumei_ff_one p) p = a % p := by
  unfold mumei_ff_mul mumei_ff_one
  simp

-- ff_eq reflexivity
theorem ff_eq_refl (a p : Int) :
    mumei_ff_eq a a p := by
  unfold mumei_ff_eq
  rfl

theorem ff_eq_symm (a b p : Int) :
    mumei_ff_eq a b p → mumei_ff_eq b a p := by
  unfold mumei_ff_eq
  intro h
  exact h.symm

theorem ff_eq_trans (a b c p : Int) :
    mumei_ff_eq a b p → mumei_ff_eq b c p → mumei_ff_eq a c p := by
  unfold mumei_ff_eq
  intro hab hbc
  exact hab.trans hbc

theorem ff_one_in_field (p : Int) (hp : 1 < p) :
    mumei_ff_in_field (mumei_ff_one p) p := by
  unfold mumei_ff_in_field mumei_ff_one
  omega

-- commutativity of field add
theorem ff_add_comm (a b p : Int) :
    mumei_ff_add a b p = mumei_ff_add b a p := by
  unfold mumei_ff_add
  ring_nf

-- commutativity of field mul
theorem ff_mul_comm (a b p : Int) :
    mumei_ff_mul a b p = mumei_ff_mul b a p := by
  unfold mumei_ff_mul
  ring_nf

-- distributivity
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

-- right inverse
theorem group_right_inv {G : Type u} [Group G] (a : G) :
    a * a⁻¹ = 1 := by
  simp

-- identity laws
theorem group_mul_one {G : Type u} [Group G] (a : G) :
    a * 1 = a := by
  simp

theorem group_one_mul {G : Type u} [Group G] (a : G) :
    1 * a = a := by
  simp

-- inverse of inverse
theorem group_inv_inv {G : Type u} [Group G] (a : G) :
    a⁻¹⁻¹ = a := by
  simp

-- inverse of product
theorem group_mul_inv_rev {G : Type u} [Group G] (a b : G) :
    (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  simp [mul_inv_rev]

-- group commutativity witness for Int
theorem mumei_group_comm_int (a b : Int) :
    mumei_group_comm a b := by
  unfold mumei_group_comm mumei_group_mul
  ring

def mumei_conserved_sum (before debit credit after : Int) : Prop :=
  after = before - debit + credit

theorem rtgs_transfer_conserves_sum
    (before debit credit : Int)
    (hBalanced : debit = credit) :
    mumei_conserved_sum before debit credit before := by
  unfold mumei_conserved_sum
  subst credit
  omega

theorem sc_subtraction_nonnegative
    (balance amount : Int)
    (hSufficient : amount ≤ balance) :
    0 ≤ balance - amount := by
  omega

/-! ### Arithmetic obligation bridge lemmas -/

theorem arith_add_upper_bound (a b limit : Int) (h : a ≤ limit - b) :
    a + b ≤ limit := by
  omega

theorem arith_add_monotone (a b c : Int) (h : a ≤ b) :
    a + c ≤ b + c := by
  omega

theorem arith_mul_nonneg_of_nonneg (a b : Int) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ a * b :=
  mul_nonneg ha hb

theorem arith_square_nonneg (a : Int) : 0 ≤ a * a :=
  mul_self_nonneg a

theorem arith_bounded_of_interval (lo hi x : Int) (hlo : lo ≤ x) (hhi : x ≤ hi) :
    lo ≤ x ∧ x ≤ hi :=
  ⟨hlo, hhi⟩

/-! ### RTGS obligation bridge lemmas -/

theorem rtgs_debit_leaves_nonnegative (balance debit : Int)
    (hSufficient : debit ≤ balance) (_hBalance : 0 ≤ balance) :
    0 ≤ balance - debit := by
  omega

theorem rtgs_transfer_conserves_sum_of_amounts
    (before debit credit after : Int)
    (hAfter : after = before - debit + credit) :
    mumei_conserved_sum before debit credit after := by
  unfold mumei_conserved_sum
  exact hAfter

/-! ### Finite-field and group obligation bridge lemmas -/

theorem ff_sub_self_eq_zero_mod (a p : Int) :
    mumei_ff_sub a a p = 0 % p := by
  unfold mumei_ff_sub
  simp

theorem group_mul_left_cancel {G : Type u} [Group G] (a b c : G)
    (h : a * b = a * c) : b = c :=
  mul_left_cancel h

/-! ### Finite-field commutativity and associativity modulo `p`

These close the `mumei_ff_eq` / `mumei_ff_add` / `mumei_ff_mul` obligations the
ring-normalising stages of `mumei_arith` reach but cannot finish, and back the
finite-field commutativity generated theorem path (spec §5.14). -/

theorem ff_add_comm_eq (a b p : Int) :
    mumei_ff_eq (mumei_ff_add a b p) (mumei_ff_add b a p) p := by
  unfold mumei_ff_eq mumei_ff_add
  ring_nf

theorem ff_mul_comm_eq (a b p : Int) :
    mumei_ff_eq (mumei_ff_mul a b p) (mumei_ff_mul b a p) p := by
  unfold mumei_ff_eq mumei_ff_mul
  ring_nf

theorem ff_add_assoc_mod (a b c p : Int) :
    mumei_ff_add (mumei_ff_add a b p) c p =
      mumei_ff_add a (mumei_ff_add b c p) p := by
  unfold mumei_ff_add
  rw [Int.emod_add_emod, Int.add_emod_emod, add_assoc]

theorem ff_mul_assoc_mod (a b c p : Int) :
    mumei_ff_mul (mumei_ff_mul a b p) c p =
      mumei_ff_mul a (mumei_ff_mul b c p) p := by
  unfold mumei_ff_mul
  conv_lhs => rw [Int.mul_emod, Int.emod_emod_of_dvd _ (dvd_refl p)]
  conv_rhs => rw [Int.mul_emod, Int.emod_emod_of_dvd _ (dvd_refl p)]
  rw [← Int.mul_emod, ← Int.mul_emod, mul_assoc]

/-! ### Modular normalisation lemmas

The `mumei_ff_*` helpers reduce modulo `p` at every step, so a generated
finite-field goal carries one `% p` per operation. These lemmas pull an inner
reduction out of a product / sum, which collapses an arbitrarily nested
`mumei_ff_*` term into a single `polynomial % p`. `mumei_ff_mod`
(`MumeiLean/Tactics.lean`) uses them as a `simp only` set, after which `ring_nf`
compares the two polynomials. -/

theorem emod_mul_emod_left (a b p : Int) : (a % p) * b % p = a * b % p := by
  conv_lhs => rw [Int.mul_emod, Int.emod_emod_of_dvd _ (dvd_refl p), ← Int.mul_emod]

theorem emod_mul_emod_right (a b p : Int) : a * (b % p) % p = a * b % p := by
  conv_lhs => rw [Int.mul_emod, Int.emod_emod_of_dvd _ (dvd_refl p), ← Int.mul_emod]

theorem emod_add_emod_left (a b p : Int) : ((a % p) + b) % p = (a + b) % p :=
  Int.emod_add_emod a p b

theorem emod_add_emod_right (a b p : Int) : (a + (b % p)) % p = (a + b) % p :=
  Int.add_emod_emod a b p

theorem ff_pow_zero (a p : Int) :
    mumei_ff_pow a 0 p = 1 % p := by
  unfold mumei_ff_pow
  norm_num

theorem ff_inv_zero (p : Int) :
    mumei_ff_inv 0 p = 0 := by
  unfold mumei_ff_inv
  simp

/-! ### Group power and conjugation bridge lemmas -/

theorem group_pow_zero {G : Type u} [Group G] (a : G) :
    a ^ (0 : Nat) = 1 :=
  pow_zero a

theorem group_pow_add {G : Type u} [Group G] (a : G) (m n : Nat) :
    a ^ (m + n) = a ^ m * a ^ n :=
  pow_add a m n

theorem group_conj_inv {G : Type u} [Group G] (a b : G) :
    (a * b * a⁻¹)⁻¹ = a * b⁻¹ * a⁻¹ := by
  group

theorem mumei_group_pow_zero_int (a : Int) :
    mumei_group_pow a 0 = 1 := by
  unfold mumei_group_pow
  norm_num

end MumeiLean.Algebra
