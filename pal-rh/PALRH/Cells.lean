import PALRH.Turns
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

open MeasureTheory Set
noncomputable section
namespace PALRH

private def cut (i : ℕ) : ℝ := 1 / ((i : ℝ) + 1)

private lemma cut_pos (i : ℕ) : 0 < cut i := by unfold cut; positivity
private lemma cut_le_one (i : ℕ) : cut i ≤ 1 := by
  unfold cut
  apply (div_le_iff₀ (by positivity)).mpr
  simp
private lemma cut_step (i : ℕ) : cut (i+1) ≤ cut i := by
  unfold cut
  apply one_div_le_one_div_of_le (by positivity)
  push_cast
  linarith

private lemma floor_on_cell {i : ℕ} {x : ℝ} (hx : x ∈ Ioc (cut (i+1)) (cut i)) :
    ⌊x⁻¹⌋₊ = i+1 := by
  have hx0 : 0 < x := lt_trans (cut_pos _) hx.1
  have hlo := (div_lt_iff₀ (by positivity : 0 < (((i+1 : ℕ) : ℝ) + 1))).mp hx.1
  have hhi := (le_div_iff₀ (by positivity : 0 < ((i:ℝ) + 1))).mp hx.2
  apply (Nat.floor_eq_iff (inv_nonneg.mpr hx0.le)).mpr
  rw [← one_div, le_div_iff₀ hx0, div_lt_iff₀ hx0]
  push_cast at *
  constructor <;> nlinarith

private lemma cut_width (i : ℕ) : cut i - cut (i+1) =
    1 / (((i:ℝ)+1)*((i:ℝ)+2)) := by
  unfold cut
  push_cast
  field_simp
  ring

/-- Integrate any bounded, integrable table of reciprocal-cell values, keeping a
rigorous envelope on the interval below the cutoff. Index i represents row i+1. -/
theorem cell_integral_bound (q : ℕ → ℝ) (B : ℝ) (M : ℕ)
    (hg : IntegrableOn (fun x : ℝ => q ⌊x⁻¹⌋₊) (Ioc 0 1))
    (hb : ∀ k, q k ≤ B) :
    (∫ x in Ioc (0:ℝ) 1, q ⌊x⁻¹⌋₊) ≤
      (∑ i ∈ Finset.range M, q (i+1) / (((i:ℝ)+1)*((i:ℝ)+2))) + B/((M:ℝ)+1) := by
  let g := fun x : ℝ => q ⌊x⁻¹⌋₊
  have hint {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb' : b ≤ 1) :
      IntervalIntegrable g volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr (hg.mono_set (Ioc_subset_Ioc ha hb'))
  have single (i : ℕ) : (∫ x in cut (i+1)..cut i, g x) =
      q (i+1) / (((i:ℝ)+1)*((i:ℝ)+2)) := by
    calc
      _ = ∫ _ in cut (i+1)..cut i, q (i+1) := by
        rw [intervalIntegral.integral_of_le (cut_step i), intervalIntegral.integral_of_le (cut_step i)]
        exact setIntegral_congr_fun measurableSet_Ioc fun x hx => congrArg q (floor_on_cell hx)
      _ = _ := by rw [intervalIntegral.integral_const, smul_eq_mul, cut_width]; ring
  have head (n : ℕ) : (∫ x in cut n..1, g x) =
      ∑ i ∈ Finset.range n, q (i+1) / (((i:ℝ)+1)*((i:ℝ)+2)) := by
    induction n with
    | zero => simp [cut]
    | succ n ih =>
      rw [← intervalIntegral.integral_add_adjacent_intervals
        (hint (cut_pos _).le (cut_step n) (cut_le_one n))
        (hint (cut_pos n).le (cut_le_one n) le_rfl),
        single, ih, Finset.sum_range_succ, add_comm]
  have htail : (∫ x in (0:ℝ)..cut M, g x) ≤ B / ((M:ℝ)+1) := by
    calc
      _ ≤ ∫ _ in (0:ℝ)..cut M, B :=
        intervalIntegral.integral_mono_on (cut_pos _).le
          (hint le_rfl (cut_pos _).le (cut_le_one M)) intervalIntegrable_const
          (fun x _ => hb _)
      _ = _ := by simp [intervalIntegral.integral_const, cut, div_eq_mul_inv, mul_comm]
  rw [← intervalIntegral.integral_of_le zero_le_one]
  change (∫ x in (0:ℝ)..1, g x) ≤ _
  rw [← intervalIntegral.integral_add_adjacent_intervals
      (hint le_rfl (cut_pos _).le (cut_le_one M)) (hint (cut_pos M).le (cut_le_one M) le_rfl),
    head]
  linarith

end PALRH
