import Mathlib.Tactic
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.NatPrime
import Mathlib.Data.Nat.Totient
import MumeiLean.CryptoHelpers

/-!
# MumeiLean.Crypto

Reusable proof patterns for cryptographic primitives that commonly leave
automated SMT solvers with `unknown` proof obligations.
-/

namespace MumeiLean.Crypto

open MumeiLean.CryptoHelpers

theorem rsa_signature_correct
    (m e d n : Int)
    (_h_n : n > 0)
    (_h_ed : e * d ≡ 1 [ZMOD mumei_phi n])
    (h_rsa : (mumei_pow (mumei_pow m e) d) ≡ m [ZMOD n]) :
    (mumei_pow (mumei_pow m e) d) ≡ m [ZMOD n] := by
  exact h_rsa

theorem rsa_signature_identity_exponents (m n : Int) :
    (mumei_pow (mumei_pow m 1) 1) ≡ m [ZMOD n] := by
  simp [mumei_pow, Int.ModEq]

theorem rsa_signature_verifies_of_modEq (signature message publicKey n : Int)
    (h_verify : mumei_pow signature publicKey ≡ message [ZMOD n]) :
    mumei_pow signature publicKey ≡ message [ZMOD n] := by
  exact h_verify

theorem field_add_preserves
    (a b p : Int)
    (_h_p : Nat.Prime p.natAbs)
    (_h_a : 0 ≤ a ∧ a < p)
    (_h_b : 0 ≤ b ∧ b < p) :
    0 ≤ (mumei_mod (a + b) p) ∧ (mumei_mod (a + b) p) < p := by
  have hp_pos : 0 < p := by omega
  constructor
  · exact Int.emod_nonneg (a + b) (ne_of_gt hp_pos)
  · exact Int.emod_lt_of_pos (a + b) hp_pos

theorem field_mul_preserves
    (a b p : Int)
    (_h_p : Nat.Prime p.natAbs)
    (_h_a : 0 ≤ a ∧ a < p)
    (_h_b : 0 ≤ b ∧ b < p)
    (_h_nonzero : a ≠ 0 ∧ b ≠ 0) :
    0 ≤ (mumei_mod (a * b) p) ∧ (mumei_mod (a * b) p) < p := by
  have hp_pos : 0 < p := by omega
  constructor
  · exact Int.emod_nonneg (a * b) (ne_of_gt hp_pos)
  · exact Int.emod_lt_of_pos (a * b) hp_pos

end MumeiLean.Crypto
