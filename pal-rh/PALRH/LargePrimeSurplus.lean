import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

open Filter
open scoped Topology
noncomputable section
namespace PALRH.LargePrimeSurplus

/-- Euler factors for an ordinary rough label and the same label after one square pass. -/
def powerAt (p : ℕ) (s : ℂ) := Complex.exp (s*(Real.log (p:ℝ):ℝ))
def smooth (p : ℕ) (s : ℂ) := (1-powerAt p (-s))*(1-powerAt p (1-2*s))
def series (s : ℂ) := (riemannZeta s*smooth 2 s*smooth 3 s)⁻¹

private theorem power_neg_one {p : ℕ} (hp : 0<p) : powerAt p (-1)=(p:ℂ)⁻¹ := by
  have h : 0<(p:ℝ) := by exact_mod_cast hp
  rw [powerAt,neg_one_mul,Complex.exp_neg,←Complex.ofReal_exp,Real.exp_log h]
  simp

private theorem smooth_at {p : ℕ} (hp : 0<p) : smooth p 1=(1-(p:ℂ)⁻¹)^2 := by
  rw [smooth,show (1-2*(1:ℂ))= -1 by norm_num,power_neg_one hp]
  ring

/-- The order-one coefficient uses the ordinary zeta residue and both smooth primes. -/
theorem slope_nine :
    Tendsto (fun s : ℂ => series s/(s-1)) (𝓝[≠] 1) (𝓝 9) := by
  have factors (p : ℕ) : Continuous (smooth p) := by
    unfold smooth powerAt
    fun_prop
  have to2 : Tendsto (smooth 2) (𝓝[≠] 1) (𝓝 ((1-(2:ℂ)⁻¹)^2)) := by
    simpa only [ContinuousWithinAt, smooth_at (by decide : 0<2), Nat.cast_ofNat] using
      (factors 2).continuousAt.continuousWithinAt (s:={1}ᶜ) (x:=1)
  have to3 : Tendsto (smooth 3) (𝓝[≠] 1) (𝓝 ((1-(3:ℂ)⁻¹)^2)) := by
    simpa only [ContinuousWithinAt, smooth_at (by decide : 0<3), Nat.cast_ofNat] using
      (factors 3).continuousAt.continuousWithinAt (s:={1}ᶜ) (x:=1)
  have total := ((riemannZeta_residue_one.mul to2).mul to3).inv₀ (by norm_num)
  convert total using 1
  · funext s
    simp only [series,div_eq_mul_inv,mul_inv_rev]
    ring
  · norm_num

theorem reciprocal_expansion (W b : ℝ) (w : W≠0) (sep : W-b≠0) :
    1/(W-b)=1/W+b/W^2+b^2/(W^2*(W-b)) := by
  field_simp
  ring

#print axioms PALRH.LargePrimeSurplus.slope_nine
#print axioms PALRH.LargePrimeSurplus.reciprocal_expansion
end PALRH.LargePrimeSurplus
