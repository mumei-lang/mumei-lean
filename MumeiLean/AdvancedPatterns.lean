import Mathlib.Tactic
import MumeiLean.Algebra
import MumeiLean.Crypto
import MumeiLean.Tactics

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

/-! ### Obligation class bridge templates

Reusable templates for each obligation class. The bridge translator
(`scripts/expr_translator.py`) assigns an `obligation_class` to every
escalated atom and references the corresponding entry points below.
-/

theorem quantifier_obligation_forall_bounded (lo hi : Int) (P : Int → Prop)
    (hall : ∀ i : Int, lo ≤ i → i < hi → P i) (t : Int)
    (hlo : lo ≤ t) (hhi : t < hi) :
    P t := hall t hlo hhi

theorem quantifier_obligation_exists_witness (lo hi : Int) (P : Int → Prop)
    (w : Int) (hlo : lo ≤ w) (hhi : w < hi) (hp : P w) :
    ∃ x : Int, lo ≤ x ∧ x < hi ∧ P x :=
  ⟨w, hlo, hhi, hp⟩

theorem quantifier_obligation_forall_implies (P Q : Int → Prop)
    (hpq : ∀ x : Int, P x → Q x) (hall : ∀ x : Int, P x) :
    ∀ x : Int, Q x := by
  intro x; exact hpq x (hall x)

theorem crypto_obligation_hash_determinism (f : Int → Int → Int) (m s : Int) :
    f m s = f m s := rfl

theorem crypto_obligation_roundtrip (enc dec : Int → Int → Int → Int) (p k n : Int)
    (hrt : ∀ p' k' n', dec (enc p' k' n') k' n' = p') :
    dec (enc p k n) k n = p := hrt p k n

theorem finite_field_obligation_closure (op : Int → Int → Int → Int) (a b p : Int)
    (hp : 0 < p)
    (hclosed : ∀ x y : Int, 0 ≤ op x y p ∧ op x y p < p) :
    0 ≤ op a b p ∧ op a b p < p := hclosed a b

theorem group_theory_obligation_assoc_law (op : Int → Int → Int) (a b c : Int)
    (hassoc : ∀ x y z : Int, op (op x y) z = op x (op y z)) :
    op (op a b) c = op a (op b c) := hassoc a b c

theorem arithmetic_obligation_bounded_combination
    (f : Int → Int → Int) (a b lo hi : Int)
    (hbounds : ∀ x y : Int, lo ≤ f x y ∧ f x y ≤ hi) :
    lo ≤ f a b ∧ f a b ≤ hi := hbounds a b

theorem arithmetic_obligation_monotone_step (f : Int → Int) (a b : Int)
    (hmono : ∀ x y : Int, x ≤ y → f x ≤ f y) (hle : a ≤ b) :
    f a ≤ f b := hmono a b hle

theorem smart_contract_obligation_guard_preserved (locked phase : Int)
    (hguard : locked = 1 → phase ≠ 0) :
    sc_reentrancy_guard locked phase := hguard

theorem smart_contract_obligation_balance_preserved (before after : Int)
    (hpreserved : after = before) :
    sc_balance_preserved before after := hpreserved

theorem rtgs_obligation_conservation (before debit credit after : Int)
    (hafter : after = before - debit + credit) :
    rtgs_balance_conserved before debit credit after :=
  rtgs_transfer_conserves_sum_of_amounts before debit credit after hafter

theorem rtgs_obligation_trace_safe (validated settled : Int)
    (htrace : settled = 1 → validated = 1) :
    rtgs_trace_safe validated settled := htrace

theorem unknown_obligation_discharged_by_manual_lemma (P : Prop) (witness : Int)
    (hmanual : P) :
    mumei_unknown_obligation witness ∧ P := ⟨trivial, hmanual⟩

/-! ### `mumei_field` automation patterns

These obligations are stated exactly as the finite-field and group-theory
lowering rules emit them, and are discharged by the `mumei_field` cascade so the
tactic itself stays covered by `lake build`. -/

theorem finite_field_commutativity_pattern (a b p : Int) :
    MumeiLean.Algebra.mumei_ff_eq
      (MumeiLean.Algebra.mumei_ff_mul a b p)
      (MumeiLean.Algebra.mumei_ff_mul b a p) p := by
  mumei_field

theorem group_conjugation_pattern {G : Type} [Group G] (a b : G) :
    (a * b * a⁻¹)⁻¹ = a * b⁻¹ * a⁻¹ := by
  mumei_field

end MumeiLean.AdvancedPatterns
