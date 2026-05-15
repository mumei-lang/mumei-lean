import Mathlib.Tactic

/-!
# MumeiLean.MedicalDevice

Reusable medical-device control proofs for insulin-pump dosage safety.
-/

namespace MumeiLean.MedicalDevice

theorem no_overdose_with_hourly_limit
    (glucose requested_dose current_hour_dosage max_dose_per_hour : Int)
    (_h_glucose : glucose ≥ 0)
    (_h_requested : requested_dose > 0)
    (_h_max : max_dose_per_hour > 0)
    (_h_current : current_hour_dosage ≥ 0)
    (h_bound : current_hour_dosage + requested_dose ≤ max_dose_per_hour) :
    requested_dose ≤ max_dose_per_hour - current_hour_dosage := by
  omega

theorem cumulative_dosage_bounded
    (dosages : List Int)
    (max_dose_per_hour : Int)
    (h_nonneg : ∀ d ∈ dosages, d ≥ 0)
    (h_bound : dosages.sum ≤ max_dose_per_hour) :
    ∀ i, (dosages.take i).sum ≤ max_dose_per_hour := by
  intro i
  have h_drop_nonneg : (dosages.drop i).sum ≥ 0 := by
    apply List.sum_nonneg
    intro d hd
    exact h_nonneg d (List.mem_of_mem_drop hd)
  have h_split := List.sum_take_add_sum_drop dosages i
  have h_take_sum : (dosages.take i).sum ≤ dosages.sum := by
    omega
  omega

theorem delivered_amount_nonnegative
    (requested_dose : Int)
    (h_requested : requested_dose > 0) :
    requested_dose ≥ 0 := by
  omega

end MumeiLean.MedicalDevice
