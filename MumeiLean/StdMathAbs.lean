import MumeiLean.Basic
import Mathlib.Tactic

/-!
# MumeiLean.StdMathAbs

Hand-written Lean witnesses for real mumei standard-library atoms.

These theorems mirror contracts from:

* `std/math/abs.mm::abs_saturating`
* `std/math/fixed_point.mm::fp_abs`
* `std/math/fixed_point.mm::fp_from_int`
* `std/list.mm::list_length`

They are intentionally outside `generated/`: the proof certificates
identify the contract, while this module records the body semantics needed
to discharge the postconditions without `sorry`.
-/

namespace MumeiLean.StdMathAbs

open MumeiLean

def i64Min : Int := -9223372036854775808

def i64Max : Int := 9223372036854775807

def absSaturatingResult (x : Int) : Int :=
  if x = i64Min then i64Max else mumei_abs x

theorem abs_saturating_correct (x result : Int)
    (h_body : result = absSaturatingResult x) :
    result ≥ 0 := by
  rw [h_body]
  unfold absSaturatingResult i64Min i64Max mumei_abs
  split
  · norm_num
  · split <;> omega

def fixedPointAbsResult (fpVal : Int) : Int :=
  if fpVal ≥ 0 then fpVal else -fpVal

theorem fixed_point_abs_correct (fpVal result : Int)
    (h_range : fpVal ≥ -999999999999 ∧ fpVal ≤ 999999999999)
    (h_body : result = fixedPointAbsResult fpVal) :
    result ≥ 0 := by
  rw [h_body]
  rcases h_range with ⟨_, _⟩
  unfold fixedPointAbsResult
  split <;> omega

theorem fixed_point_from_int_correct (n result : Int)
    (_h_range : n ≥ -99999999 ∧ n ≤ 99999999)
    (h_body : result = n * 10000) :
    result = n * 10000 :=
  h_body

def listLengthResult (listTag : Int) : Int :=
  if listTag = 0 then 0 else 1

theorem list_length_correct (listTag result : Int)
    (_h_tag : listTag ≥ 0 ∧ listTag ≤ 1)
    (h_body : result = listLengthResult listTag) :
    result ≥ 0 := by
  rw [h_body]
  unfold listLengthResult
  split <;> norm_num

end MumeiLean.StdMathAbs
