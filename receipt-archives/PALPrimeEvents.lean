import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

open Filter
open scoped Topology

noncomputable section
namespace PALPrimeEvents

def ramp (p x : ℝ) : ℝ := Real.log p * max (x/p-1) 0
def hinge (p t : ℝ) : ℝ := (Real.log p / Real.sqrt p) * max (t-Real.log p) 0

/-- The actual prime-3 exponential ramp dominates prime 5 at every physical scale. -/
theorem ramp_five_le_three (x : ℝ) : ramp 5 x ≤ ramp 3 x := by
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have h53 : 3*Real.log 5 < 5*Real.log 3 := by
    have h := Real.log_lt_log (by norm_num : 0 < (5:ℝ)^3) (by norm_num : (5:ℝ)^3 < 3^5)
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hlog : Real.log 3 < Real.log 5 := Real.log_lt_log (by norm_num) (by norm_num)
  unfold ramp
  by_cases hx : x < 5
  · rw [max_eq_right (by linarith : x / 5 - 1 ≤ 0), mul_zero]
    exact mul_nonneg h3.le (le_max_right _ _)
  · rw [max_eq_left (by linarith : 0 ≤ x/5-1), max_eq_left (by linarith : 0 ≤ x/3-1)]
    nlinarith [mul_nonneg (show 0 ≤ x by linarith) (sub_pos.mpr h53).le]

/-- On the Suzuki/RPL hinge account, those same two events eventually order the other way. -/
theorem hinge_three_lt_five_eventually : ∀ᶠ t : ℝ in atTop, hinge 3 t < hinge 5 t := by
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hl : 4*Real.log 3 < 3*Real.log 5 := by
    have h := Real.log_lt_log (by norm_num : 0 < (3:ℝ)^4) (by norm_num : (3:ℝ)^4 < 5^3)
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hs : 3*Real.sqrt 5 < 4*Real.sqrt 3 := by
    apply (sq_lt_sq₀ (by positivity) (by positivity)).mp
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)]
  let a := Real.log 3 / Real.sqrt 3
  let b := Real.log 5 / Real.sqrt 5
  have hab : a < b := by
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [mul_pos (sub_pos.mpr hs) h3, mul_pos (sub_pos.mpr hl) (show 0 < Real.sqrt 3 by positivity)]
  filter_upwards [eventually_ge_atTop (Real.log 3), eventually_ge_atTop (Real.log 5),
    eventually_gt_atTop ((b*Real.log 5-a*Real.log 3)/(b-a))]
    with t ht3 ht5 ht
  rw [div_lt_iff₀ (sub_pos.mpr hab)] at ht
  change a*max (t-Real.log 3) 0 < b*max (t-Real.log 5) 0
  rw [max_eq_left (sub_nonneg.mpr ht3), max_eq_left (sub_nonneg.mpr ht5)]
  linarith

#print axioms ramp_five_le_three
#print axioms hinge_three_lt_five_eventually
end PALPrimeEvents
