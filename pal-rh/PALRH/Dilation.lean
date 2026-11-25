import PALRH.Frames

open Filter Finset
open scoped Topology BigOperators
noncomputable section
namespace PALRH

/-- A row at the coarser frame is a consecutive block at the finer frame. -/
theorem dilated_block_weight {p : ℕ} (hp : 0 < p) (q : ℕ) :
    ∑ i ∈ Finset.range p, rowWeight (p*(q+1)-1+i) = rowWeight q / p := by
  rw [rowWeight_block]
  have hpos : 0 < p*(q+1) := Nat.mul_pos hp (by omega)
  have ha : p*(q+1)-1+1 = p*(q+1) := by omega
  have hb : p*(q+1)-1+p+1 = p*(q+2) := by
    rw [show p*(q+1)-1+p+1 = (p*(q+1)-1+1)+p by omega, ha]; ring
  have ha' : ((p*(q+1)-1 : ℕ):ℝ)+1 = (p:ℝ)*((q:ℝ)+1) := by exact_mod_cast ha
  have hb' : ((p*(q+1)-1+p : ℕ):ℝ)+1 = (p:ℝ)*((q:ℝ)+2) := by exact_mod_cast hb
  rw [ha',hb',rowWeight]
  field_simp
  ring

/-- Carry a zero-origin signal to the quotient clock. This exact factor covers every lap;
the initial incomplete block reads the specified zero at the origin. -/
theorem dilated_all_rows {p : ℕ} (hp : 0 < p) (f : ℕ → ℝ) (empty : f 0 = 0)
    {C : ℝ} (bounded : ∀ k, ‖f k‖ ≤ C) :
    (∑' n : ℕ, rowWeight n * f ((n+1)/p)) =
      (∑' n : ℕ, rowWeight n * f (n+1)) / p := by
  let g : ℕ → ℝ := fun n => rowWeight n * f ((n+1)/p)
  let h : ℕ → ℝ := fun n => rowWeight n * f (n+1)
  have summable (address : ℕ → ℕ) : Summable (fun n => rowWeight n * f (address n)) := by
    apply Summable.of_norm_bounded (g := fun n => rowWeight n * C)
      (rowWeight_hasSum.summable.mul_right C)
    intro n
    have hw : 0 ≤ rowWeight n := by unfold rowWeight; positivity
    rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg hw]
    exact mul_le_mul_of_nonneg_left (bounded _) hw
  have hg : Summable g := summable _
  have hh : Summable h := summable _
  have pref (q : ℕ) : (∑ i ∈ Finset.range (p*(q+1)-1), g i) =
      (∑ i ∈ Finset.range q, h i)/p := by
    induction q with
    | zero =>
      simp only [zero_add, mul_one, Finset.range_zero, Finset.sum_empty, zero_div]
      apply Finset.sum_eq_zero
      intro i hi
      have hi' := Finset.mem_range.mp hi
      simp [g, Nat.div_eq_of_lt (by omega : i+1<p), empty]
    | succ q ih =>
      have hpos := Nat.mul_pos hp (show 0 < q+1 by omega)
      have endpt : p*(q+1+1)-1 = (p*(q+1)-1)+p := by
        rw [Nat.mul_succ]; omega
      rw [endpt, Finset.sum_range_add, ih, Finset.sum_range_succ, add_div]
      congr 1
      calc
        _ = ∑ i ∈ Finset.range p, rowWeight (p*(q+1)-1+i) * f (q+1) := by
          apply Finset.sum_congr rfl
          intro i hi
          have hi' := Finset.mem_range.mp hi
          have eq : p*(q+1)-1+i+1 = i+p*(q+1) := by omega
          simp [g, eq, Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hi']
        _ = h q / p := by
          rw [← Finset.sum_mul, dilated_block_weight hp]
          dsimp [h]; ring
  have htop : Tendsto (fun q : ℕ => p*(q+1)-1) atTop atTop := by
    apply tendsto_atTop_mono (f := fun n : ℕ => n) _ tendsto_id
    intro i
    have hle := Nat.mul_le_mul_right (i+1) (show 1 ≤ p by omega)
    omega
  have lhs := hg.hasSum.tendsto_sum_nat.comp htop
  have rhs := hh.hasSum.tendsto_sum_nat.div_const (p:ℝ)
  apply tendsto_nhds_unique lhs
  change Tendsto (fun q : ℕ => ∑ i ∈ Finset.range (p*(q+1)-1), g i) atTop
    (𝓝 ((∑' i, h i)/(p:ℝ)))
  simpa only [pref] using rhs

/-- Admissible linear combinations stay admissible under integer dilation. -/
theorem quotient_signal {p a : ℕ} (hp : 0<p) (ha : 0<a) (k : ℕ) :
    turn a (k/p) = turn (p*a) k - turn p k / a := by
  have he := quotient_turn hp ha k
  change (((k/p)%a : ℕ) : ℚ)/(a:ℚ) = _
  apply (div_eq_iff (by positivity : (a:ℚ) ≠ 0)).mpr
  rw [← he]
  field_simp

end PALRH
