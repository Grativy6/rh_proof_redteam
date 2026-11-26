import PALRH.DoubledRuler

open Finset
open scoped BigOperators
noncomputable section
namespace PALRH.DoubledMass

def inkAt (t j : ℝ) : ℝ := (t-j)^5*(7*j-t)

/-- The loss below the leading cubic is a sum of two signed-free remainder terms. -/
theorem cubic_remainder (m : ℕ) (t : ℝ) :
    let a := t-m
    let b := a*(1-a)
    (2/3:ℝ)*t^3 - ((∑ j ∈ Icc 1 m, inkAt t j)-t^6/2+t^5) =
      m*(1/6-b^2/2-b^3) + a^3*(1/6+(1-a)*(1+a-a^2)/2) := by
  dsimp only
  induction m with
  | zero => simp; ring
  | succ m old =>
    rw [sum_Icc_succ_top (by omega : 1 ≤ m+1)]
    unfold inkAt at *
    push_cast
    linear_combination old

theorem cubic_upper {m : ℕ} {t : ℝ} (lo : (m:ℝ) ≤ t) (hi : t ≤ (m:ℝ)+1) :
    (∑ j ∈ Icc 1 m, inkAt t j)-t^6/2+t^5 ≤ (2/3:ℝ)*t^3 := by
  let a : ℝ := t-m
  let b : ℝ := a*(1-a)
  have an : 0 ≤ a := sub_nonneg.mpr lo
  have ao : a ≤ 1 := by dsimp [a];linarith only [hi]
  have back : 0 ≤ 1-a := sub_nonneg.mpr ao
  have bn : 0 ≤ b := mul_nonneg an back
  have quarter : b ≤ 1/4 := by dsimp [b];nlinarith only [sq_nonneg (a-1/2)]
  have sq := pow_le_pow_left₀ bn quarter 2
  have cube := pow_le_pow_left₀ bn quarter 3
  have first : 0 ≤ 1/6-b^2/2-b^3 := by norm_num at sq cube; linarith only [sq,cube]
  have second : 0 ≤ 1+a-a^2 := by nlinarith only [bn,show b=a*(1-a) from rfl]
  have lower : 0 ≤ (m:ℝ)*(1/6-b^2/2-b^3)+a^3*(1/6+(1-a)*(1+a-a^2)/2) := by positivity
  have eqn := cubic_remainder m t
  dsimp only at eqn
  dsimp [a,b] at lower
  linarith only [lower,eqn]

def curvature (t j : ℝ) : ℝ := j^2*(t-j)^3*(7*j-3*t)

theorem curvature_sum (m : ℕ) (t : ℝ) :
    let a := t-m
    6*(∑ j ∈ Icc 1 m, curvature t j) = (m:ℝ)*(m+1)*
      ((m-1)*(1-6*a^2*(1-a)^2) + 3*a^3*(4-3*a)) := by
  dsimp only
  induction m with
  | zero => simp
  | succ m old =>
    rw [sum_Icc_succ_top (by omega : 1 ≤ m+1), mul_add, old]
    unfold curvature
    push_cast
    ring

/-- The stop-loss curve bends upwards on each whole quotient interval. -/
theorem positive_curvature {m : ℕ} {t : ℝ} (mp : 0 < m)
    (left : (m:ℝ) ≤ t) (right : t ≤ (m:ℝ)+1) :
    0 ≤ ∑ j ∈ Icc 1 m, curvature t j := by
  let a : ℝ := t-m
  have an : 0 ≤ a := sub_nonneg.mpr left
  have one : a ≤ 1 := by dsimp [a]; linarith only [right]
  have back : 0 ≤ 1-a := sub_nonneg.mpr one
  have quarter : a*(1-a) ≤ 1/4 := by nlinarith only [sq_nonneg (a-1/2)]
  have product := mul_self_le_mul_self (mul_nonneg an back) quarter
  have core : 0 ≤ 1-6*a^2*(1-a)^2 := by nlinarith only [product]
  have mr : (1:ℝ) ≤ m := by exact_mod_cast mp
  have wide : 0 ≤ 4-3*a := by linarith only [one]
  have rhs : 0 ≤ (m:ℝ)*(m+1)*((m-1)* (1-6*a^2*(1-a)^2) + 3*a^3*(4-3*a)) :=
    mul_nonneg (by positivity) (add_nonneg (mul_nonneg (sub_nonneg.mpr mr) core) (by positivity))
  have sum_eq := curvature_sum m t
  change 6*(∑ j ∈ Icc 1 m, curvature t j) = _ at sum_eq
  dsimp [a] at rhs
  linarith only [sum_eq,rhs]

/-- On the reciprocal cutoff 1/M the exact remaining mass lies in a bracket of width 1/M. -/
theorem boundary_bracket (M : ℕ) :
    (M:ℝ)^7 - 7*(M:ℝ)^6 ≤ 7 * (∑ j ∈ range M, (j:ℝ)^6) ∧
    7 * (∑ j ∈ range M, (j:ℝ)^6) ≤ (M:ℝ)^7 := by
  induction M with
  | zero => simp
  | succ m old =>
    rw [sum_range_succ, mul_add]
    push_cast
    obtain ⟨lo,hi⟩ := old
    have upper : 0 ≤ 21*(m:ℝ)^5+35*m^4+35*m^3+21*m^2+7*m+1 := by positivity
    have lower : 0 ≤ 21*(m:ℝ)^5+70*m^4+105*m^3+84*m^2+35*m+6 := by positivity
    constructor <;> nlinarith only [lo,hi,upper,lower]

#print axioms PALRH.DoubledMass.cubic_upper
#print axioms PALRH.DoubledMass.positive_curvature
#print axioms PALRH.DoubledMass.boundary_bracket

end PALRH.DoubledMass
