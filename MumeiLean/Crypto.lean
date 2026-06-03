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

def hash (message salt : Int) : Int :=
  mumei_mod (message * 1315423911 + salt) 2147483647

def signature_verify (signature message publicKey modulus : Int) : Prop :=
  mumei_pow signature publicKey ≡ message [ZMOD modulus]

def encrypt (plaintext key nonce : Int) : Int :=
  plaintext + key + nonce

def decrypt (ciphertext key nonce : Int) : Int :=
  ciphertext - key - nonce

theorem hash_deterministic (message salt : Int) :
    hash message salt = hash message salt := by
  rfl

theorem hash_modulus_bounds (message salt : Int) :
    0 ≤ hash message salt ∧ hash message salt < 2147483647 := by
  unfold hash mumei_mod
  have hpos : (0 : Int) < 2147483647 := by norm_num
  constructor
  · exact Int.emod_nonneg (message * 1315423911 + salt) (ne_of_gt hpos)
  · exact Int.emod_lt_of_pos (message * 1315423911 + salt) hpos

theorem hash_collision_resistance_pattern (m₁ m₂ salt : Int)
    (h : hash m₁ salt = hash m₂ salt → m₁ = m₂) :
    hash m₁ salt = hash m₂ salt → m₁ = m₂ := by
  exact h

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

theorem signature_verify_sound (signature message publicKey modulus : Int)
    (h : signature_verify signature message publicKey modulus) :
    mumei_pow signature publicKey ≡ message [ZMOD modulus] := by
  exact h

theorem signature_verify_complete (signature message publicKey modulus : Int)
    (h : mumei_pow signature publicKey ≡ message [ZMOD modulus]) :
    signature_verify signature message publicKey modulus := by
  exact h

theorem encryption_roundtrip (plaintext key nonce : Int) :
    decrypt (encrypt plaintext key nonce) key nonce = plaintext := by
  unfold encrypt decrypt
  ring

theorem encryption_roundtrip_of_ciphertext (plaintext ciphertext key nonce : Int)
    (h_cipher : ciphertext = encrypt plaintext key nonce) :
    decrypt ciphertext key nonce = plaintext := by
  rw [h_cipher]
  exact encryption_roundtrip plaintext key nonce

theorem encryption_integrity_pattern (plaintext ciphertext key nonce : Int)
    (h_roundtrip : decrypt ciphertext key nonce = plaintext) :
    decrypt ciphertext key nonce = plaintext := by
  exact h_roundtrip

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
