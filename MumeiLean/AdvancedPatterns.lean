import Mathlib.Tactic
import MumeiLean.Algebra
import MumeiLean.Crypto

/-!
# MumeiLean.AdvancedPatterns

Reusable proof patterns for obligations that typically escape SMT automation:
nested quantifiers, higher-order predicates, inductive definitions, finite-field
closure, group laws, and cryptographic primitive wrappers.
-/

namespace MumeiLean.AdvancedPatterns

open MumeiLean.Algebra
open MumeiLean.Crypto
open MumeiLean.CryptoHelpers

def mumei_unknown_obligation (_witness : Int) : Prop :=
  True

def sc_reentrancy_guard (locked phase : Int) : Prop :=
  locked = 1 → phase ≠ 0

def sc_balance_preserved (before after : Int) : Prop :=
  after = before

def sc_withdraw_allowed (balance amount : Int) : Prop :=
  0 ≤ amount ∧ amount ≤ balance

def sc_no_negative_balance (balance : Int) : Prop :=
  0 ≤ balance

def rtgs_validated (state : Int) : Prop :=
  1 ≤ state

def rtgs_settled (state : Int) : Prop :=
  state = 2

def rtgs_balance_conserved (before debit credit after : Int) : Prop :=
  mumei_conserved_sum before debit credit after

def rtgs_trace_safe (validated settled : Int) : Prop :=
  settled = 1 → validated = 1

theorem unknown_obligation_intro (witness : Int) :
    mumei_unknown_obligation witness := by
  trivial

theorem sc_withdraw_allowed_intro (balance amount : Int)
    (hAmount : 0 ≤ amount) (hBalance : amount ≤ balance) :
    sc_withdraw_allowed balance amount := by
  exact ⟨hAmount, hBalance⟩

theorem sc_no_negative_after_withdraw (balance amount : Int)
    (hAllowed : sc_withdraw_allowed balance amount) :
    sc_no_negative_balance (balance - amount) := by
  unfold sc_withdraw_allowed sc_no_negative_balance at *
  omega

theorem rtgs_balance_conserved_refl (before amount : Int) :
    rtgs_balance_conserved before amount amount before := by
  unfold rtgs_balance_conserved
  exact rtgs_transfer_conserves_sum before amount amount rfl

theorem rtgs_trace_safe_intro (validated : Int) :
    rtgs_trace_safe validated 0 := by
  unfold rtgs_trace_safe
  intro h
  omega

theorem bounded_forall_weaken (lo hi : Int) (P Q : Int → Prop)
    (hmap : ∀ i : Int, lo ≤ i → i < hi → P i → Q i)
    (hall : ∀ i : Int, lo ≤ i → i < hi → P i) :
    ∀ i : Int, lo ≤ i → i < hi → Q i := by
  intro i hlo hhi
  exact hmap i hlo hhi (hall i hlo hhi)

theorem bounded_exists_map (lo hi : Int) (P Q : Int → Prop)
    (hmap : ∀ i : Int, lo ≤ i → i < hi → P i → Q i)
    (hex : ∃ i : Int, lo ≤ i ∧ i < hi ∧ P i) :
    ∃ i : Int, lo ≤ i ∧ i < hi ∧ Q i := by
  rcases hex with ⟨i, hlo, hhi, hp⟩
  exact ⟨i, hlo, hhi, hmap i hlo hhi hp⟩

theorem nested_forall_swap (P : Int → Int → Prop)
    (h : ∀ i : Int, ∀ j : Int, P i j) :
    ∀ j : Int, ∀ i : Int, P i j := by
  intro j i
  exact h i j

theorem higher_order_predicate_apply (P : Int → Prop) (x : Int)
    (h : P x) :
    P x := by
  exact h

theorem nat_induction_pattern (P : Nat → Prop)
    (h0 : P 0)
    (hstep : ∀ n : Nat, P n → P (n + 1)) :
    ∀ n : Nat, P n := by
  intro n
  induction n with
  | zero => exact h0
  | succ n ih =>
      simpa [Nat.succ_eq_add_one] using hstep n ih

theorem int_nonnegative_induction_pattern (P : Int → Prop)
    (h0 : P 0)
    (hstep : ∀ n : Nat, P n → P (n + 1)) :
    ∀ n : Int, 0 ≤ n → P n := by
  intro n hn
  lift n to Nat using hn
  induction n with
  | zero =>
      simpa using h0
  | succ n ih =>
      simpa [Nat.succ_eq_add_one, Int.ofNat_add] using hstep n ih

theorem finite_field_binary_closed (op : Int → Int → Int) (a b p : Int)
    (hclosed : ∀ x y : Int, mumei_ff_in_field (op x y) p)
    (_ha : mumei_ff_in_field a p)
    (_hb : mumei_ff_in_field b p) :
    mumei_ff_in_field (op a b) p := by
  exact hclosed a b

theorem group_hom_preserves_mul {G H : Type} [Group G] [Group H]
    (f : G → H)
    (hmul : ∀ a b : G, f (a * b) = f a * f b) :
    ∀ a b : G, f (a * b) = f a * f b := by
  exact hmul

theorem hash_stability_under_equal_inputs (m₁ m₂ salt₁ salt₂ : Int)
    (hm : m₁ = m₂) (hs : salt₁ = salt₂) :
    hash m₁ salt₁ = hash m₂ salt₂ := by
  simp [hm, hs]

theorem signature_pattern (signature message publicKey modulus : Int)
    (h : signature_verify signature message publicKey modulus) :
    mumei_pow signature publicKey ≡ message [ZMOD modulus] := by
  exact signature_verify_sound signature message publicKey modulus h

theorem encryption_pattern (plaintext ciphertext key nonce : Int)
    (h : ciphertext = encrypt plaintext key nonce) :
    decrypt ciphertext key nonce = plaintext := by
  exact encryption_roundtrip_of_ciphertext plaintext ciphertext key nonce h

end MumeiLean.AdvancedPatterns
