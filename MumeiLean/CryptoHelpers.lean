import Mathlib.Data.Nat.Totient

/-!
# MumeiLean.CryptoHelpers

Lean helper functions for cryptographic expressions emitted by the Python
bridge translator.
-/

namespace MumeiLean.CryptoHelpers

def mumei_mod (a b : Int) : Int :=
  a % b

def mumei_pow (base exp : Int) : Int :=
  base ^ exp.toNat

def mumei_phi (n : Int) : Int :=
  Int.ofNat (Nat.totient n.natAbs)

end MumeiLean.CryptoHelpers
