import PALRH.OneSidedBoard
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open Finset MeasureTheory
open scoped BigOperators

noncomputable section
namespace PALRH.MovingEndpoint

open LinearPrimeIntegral QuarticBoards

/-- A right supporting slope at an integer head includes the label at the head. -/
def slope (n : ℕ) : ℝ := ∑ d ∈ Icc 1 n, ArithmeticFunction.vonMangoldt d

/-- At an individual mark the excess over that supporting line is precisely the
ramp crossed on the return journey. This also fixes the convention at an endpoint. -/
theorem hinge_remainder (n d y : ℝ) :
    max 0 (y-d) - max 0 (n-d) - (if d ≤ n then y-n else 0) =
      if d ≤ n then max 0 (d-y) else max 0 (y-d) := by
  by_cases before : d ≤ n
  · rw [if_pos before, if_pos before, max_eq_right (sub_nonneg.mpr before)]
    rcases le_total d y with h | h
    · rw [max_eq_right (sub_nonneg.mpr h), max_eq_left (sub_nonpos.mpr h)]
      ring
    · rw [max_eq_left (sub_nonpos.mpr h), max_eq_right (sub_nonneg.mpr h)]
      ring
  · simp [before, max_eq_left (sub_nonpos.mpr (le_of_not_ge before))]

/-- Count exactly the prime-power ramps crossed while moving the endpoint,
including the newly encountered labels above its starting position. -/
def crossed (B n : ℕ) (y : ℝ) : ℝ :=
  ∑ d ∈ Icc 1 B, ArithmeticFunction.vonMangoldt d *
    (if d ≤ n then max 0 ((d:ℝ)-y) else max 0 (y-d))

private theorem slope_through {n B : ℕ} (cap : n ≤ B) :
    (∑ d ∈ Icc 1 B, if d ≤ n then ArithmeticFunction.vonMangoldt d else 0) = slope n := by
  rw [← Finset.sum_filter]
  have eq : (Icc 1 B).filter (fun d => d ≤ n) = Icc 1 n := by
    ext d
    simp only [mem_filter, mem_Icc]
    omega
  rw [eq]
  rfl

/-- Both sides of the old endpoint can carry an actual crossing cost. -/
theorem exact_return {n B : ℕ} (cap : n ≤ B) (y : ℝ) :
    extended B y = fullWalk n + slope n * (y-n) + crossed B n y := by
  rw [← extended_integer cap, ← slope_through cap]
  unfold extended crossed
  rw [Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  have identity := hinge_remainder (n:ℝ) (d:ℝ) y
  by_cases hd : d ≤ n
  · have h : (d:ℝ) ≤ n := by exact_mod_cast hd
    simp only [if_pos h, if_pos hd] at identity ⊢
    linear_combination ArithmeticFunction.vonMangoldt d * identity
  · have h : ¬ (d:ℝ) ≤ n := by exact_mod_cast hd
    simp only [if_neg h, if_neg hd, zero_mul, sub_zero, add_zero] at identity ⊢
    linear_combination ArithmeticFunction.vonMangoldt d * identity

theorem supporting_line {n B : ℕ} (cap : n ≤ B) (y : ℝ) :
    fullWalk n + slope n * (y-n) ≤ extended B y := by
  rw [exact_return cap]
  apply le_add_of_nonneg_right
  apply Finset.sum_nonneg
  intro d _
  apply mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
  split <;> exact le_max_left _ _

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

private theorem supporting_mean (n : ℕ) (X : Ω → ℝ) (hx : Integrable X μ)
    (mean : ∫ w, X w ∂μ = (n:ℝ)) :
    Integrable (fun w => fullWalk n + slope n * (X w - (n:ℝ))) μ ∧
    (∫ w, fullWalk n + slope n * (X w - (n:ℝ)) ∂μ) = fullWalk n := by
  have step : Integrable (fun w => slope n * (X w - (n:ℝ))) μ :=
    (hx.sub (integrable_const (n:ℝ))).const_mul (slope n)
  refine ⟨(integrable_const (μ:=μ) (fullWalk n)).add step, ?_⟩
  have centered : (∫ w, X w - (n:ℝ) ∂μ) = 0 := by
    rw [integral_sub hx (integrable_const _), mean]
    simp
  rw [integral_add (integrable_const (μ:=μ) (fullWalk n)) step,
    integral_const_mul, centered]
  simp

/-- At a fixed mean the original prime-power area lies below the moved reading. -/
theorem at_mean {n B : ℕ} (cap : n ≤ B) (X : Ω → ℝ) (hx : Integrable X μ)
    (mean : ∫ w, X w ∂μ = (n:ℝ))
    (area : Integrable (fun w => extended B (X w)) μ) :
    fullWalk n ≤ ∫ w, extended B (X w) ∂μ := by
  obtain ⟨line, value⟩ := supporting_mean n X hx mean
  exact value ▸ integral_mono line area (fun w => supporting_line cap (X w))

/-- The actual prime crossings recover the difference lost by the averaging. -/
theorem mean_with_return {n B : ℕ} (cap : n ≤ B) (X : Ω → ℝ) (hx : Integrable X μ)
    (mean : ∫ w, X w ∂μ = (n:ℝ))
    (cross : Integrable (fun w => crossed B n (X w)) μ) :
    (∫ w, extended B (X w) ∂μ) = fullWalk n + ∫ w, crossed B n (X w) ∂μ := by
  obtain ⟨line, value⟩ := supporting_mean n X hx mean
  calc
    _ = ∫ w, (fullWalk n + slope n * (X w - n)) + crossed B n (X w) ∂μ :=
      integral_congr_ae (ae_of_all _ fun w => exact_return cap (X w))
    _ = _ := by rw [integral_add line cross, value]

/-- A second mean-preserving observation lower-bounds the actual crossings of the
first. The two observations may keep different upper cutoffs for their labels. -/
theorem refund_by_comparison {n B H : ℕ} (first : n ≤ B) (second : n ≤ H)
    (X Y : Ω → ℝ) (hx : Integrable X μ) (hy : Integrable Y μ)
    (mx : ∫ w, X w ∂μ = (n:ℝ)) (my : ∫ w, Y w ∂μ = (n:ℝ))
    (cross : Integrable (fun w => crossed B n (X w)) μ)
    (area : Integrable (fun w => extended H (Y w)) μ) :
    (∫ w, extended B (X w) ∂μ) - (∫ w, extended H (Y w) ∂μ) ≤
      ∫ w, crossed B n (X w) ∂μ := by
  have paid := at_mean (μ:=μ) second Y hy my area
  have exactValue := mean_with_return (μ:=μ) first X hx mx cross
  linarith only [paid, exactValue]

/-- At fourth powers use the centered moved area and the variance still unpaid
after actual prime crossings. Shrinking the moved variance is unnecessary. -/
theorem rh_of_crossing_credit (K : ℕ) {C D : ℝ} (cn : 0 ≤ C) (dn : 0 ≤ D)
    (B : ℕ → ℕ) (X : ℕ → Ω → ℝ)
    (bounds : ∀ k : ℕ, K ≤ k → 0 < k →
      let n := k^4
      n ≤ B k ∧ Integrable (X k) μ ∧ (∫ w, X k w ∂μ) = (n:ℝ) ∧
      Integrable (fun w => crossed (B k) n (X k w)) μ ∧
      Integrable (fun w => (X k w)^2) μ ∧
      ((∫ w, extended (B k) (X k w) ∂μ) - (∫ w, (X k w)^2 ∂μ)/2) ≤ C*(k:ℝ)^6 ∧
      ((∫ w, (X k w)^2 ∂μ) - (n:ℝ)^2)/2 -
        (∫ w, crossed (B k) n (X k w) ∂μ) ≤ D*(k:ℝ)^6) :
    RiemannHypothesis := by
  apply OneSidedBoard.rh_of_eventual_upper_area K (C:=C+D) (by positivity)
  intro k large positive
  obtain ⟨cap, hx, mean, cross, _, centered, unpaid⟩ := bounds k large positive
  have recovered := mean_with_return (μ:=μ) cap (X k) hx mean cross
  unfold error
  linarith only [recovered, centered, unpaid]

#print axioms PALRH.MovingEndpoint.exact_return
#print axioms PALRH.MovingEndpoint.at_mean
#print axioms PALRH.MovingEndpoint.mean_with_return
#print axioms PALRH.MovingEndpoint.refund_by_comparison
#print axioms PALRH.MovingEndpoint.rh_of_crossing_credit

end PALRH.MovingEndpoint
