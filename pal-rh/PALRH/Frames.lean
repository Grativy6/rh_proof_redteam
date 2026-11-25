import PALRH.Turns
import Mathlib.Analysis.SumOverResidueClass
import Mathlib.Analysis.SpecificLimits.Basic

open Filter Finset
open scoped Topology BigOperators

namespace PALRH

/-- Row n+1 is cut from (0,1] with its actual length. The table index starts at zero. -/
noncomputable def rowWeight (n : ℕ) : ℝ := 1 / (((n : ℝ) + 1) * ((n : ℝ) + 2))

private theorem weight_drop (i : ℕ) :
    rowWeight i = 1 / ((i : ℝ) + 1) - 1 / (((i+1 : ℕ) : ℝ) + 1) := by
  unfold rowWeight
  push_cast
  field_simp
  ring

theorem rowWeight_hasSum : HasSum rowWeight 1 := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun i => by unfold rowWeight; positivity) 1).2
  simp_rw [weight_drop, Finset.sum_range_sub']
  simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

theorem rowWeight_block (start length : ℕ) :
    ∑ i ∈ Finset.range length, rowWeight (start+i) =
      1/((start:ℝ)+1) - 1/(((start+length:ℕ):ℝ)+1) := by
  simpa only [weight_drop, Nat.add_zero, Nat.add_assoc] using
    Finset.sum_range_sub' (fun i : ℕ => 1/(((start+i:ℕ):ℝ)+1)) length

theorem rowWeight_tail (M : ℕ) : (∑' n, rowWeight (n+M)) = 1/((M:ℝ)+1) := by
  have h := rowWeight_hasSum.summable.sum_add_tsum_nat_add M
  rw [rowWeight_hasSum.tsum_eq] at h
  have finiteHead : ∑ i ∈ Finset.range M, rowWeight i = 1 - 1/((M:ℝ)+1) := by
    simp_rw [weight_drop, Finset.sum_range_sub']
    norm_num
  rw [finiteHead] at h
  linarith

/-- All visits in the class of row i+1 at spacing L, including every later lap. -/
noncomputable def frameMass (L i : ℕ) : ℝ := ∑' n : ℕ, rowWeight (i + L*n)

theorem frameMass_total (L : ℕ) [NeZero L] : ∑ i : ZMod L, frameMass L i.val = 1 :=
  (Nat.sumByResidueClasses rowWeight_hasSum.summable L).symm.trans rowWeight_hasSum.tsum_eq

theorem frameMass_refine (L p i : ℕ) [NeZero L] [NeZero p] :
    frameMass L i = ∑ t : ZMod p, frameMass (L*p) (i + L*t.val) := by
  have hL : 0 < L := Nat.pos_of_neZero L
  have hinj : Function.Injective (fun n : ℕ => i + L*n) := by
    intro a b hab
    exact (Nat.eq_of_mul_eq_mul_left hL) (Nat.add_left_cancel hab)
  have hs : Summable (fun n : ℕ => rowWeight (i + L*n)) :=
    rowWeight_hasSum.summable.comp_injective hinj
  unfold frameMass
  rw [Nat.sumByResidueClasses hs p]
  apply Finset.sum_congr rfl
  intro t _
  apply tsum_congr
  intro n
  congr 1
  ring

/-- The error already assigned to a class is conserved when the prediction is copied. -/
theorem copied_error_refine (L p i : ℕ) [NeZero L] [NeZero p] (residual : ℝ) :
    frameMass L i * residual^2 =
      ∑ t : ZMod p, frameMass (L*p) (i + L*t.val) * residual^2 := by
  rw [frameMass_refine L p, Finset.sum_mul]

/-- Re-opening a joint reading recovers the old residue and the quotient digit. -/
theorem joint_reading (k d p : ℕ) :
    k % (d*p) = k % d + d*((k/d)%p) ∧
      k % (d*p) % d = k % d ∧ k % (d*p) / d = (k/d)%p :=
  ⟨Nat.mod_mul, Nat.mod_mul_right_mod k d p, Nat.mod_mul_right_div_self k d p⟩

/-- The fresh digit is exactly the part of the joint turn left after carrying the old one. -/
theorem quotient_turn {d p : ℕ} (hd : 0 < d) (hp : 0 < p) (k : ℕ) :
    (p : ℚ) * turn (d*p) k - turn d k = (((k/d)%p : ℕ) : ℚ) := by
  unfold turn
  rw [Nat.mod_mul]
  push_cast
  field_simp
  ring

/-- A complete table of the old answers retains its integral over all visits. -/
theorem weighted_frame_sum (L : ℕ) [NeZero L] (answer : ZMod L → ℝ) :
    (∑' n : ℕ, rowWeight n * answer n) =
      ∑ i : ZMod L, frameMass L i.val * answer i := by
  let C := ∑ i : ZMod L, ‖answer i‖
  have hC (i : ZMod L) : ‖answer i‖ ≤ C := Finset.single_le_sum
    (fun j _ => norm_nonneg (answer j)) (Finset.mem_univ i)
  have hs : Summable (fun n : ℕ => rowWeight n * answer n) := by
    apply Summable.of_norm_bounded (g := fun n => rowWeight n * C)
      (rowWeight_hasSum.summable.mul_right C)
    intro n
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ rowWeight n by unfold rowWeight; positivity)]
    exact mul_le_mul_of_nonneg_left (hC _) (by unfold rowWeight; positivity)
  rw [Nat.sumByResidueClasses hs L]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, add_zero,
    ZMod.natCast_zmod_val, frameMass, tsum_mul_right]

/-- An old turn is recoverable from the new row label at every later lap. -/
theorem turn_recover {d L : ℕ} (h : d ∣ L) (k : ℕ) : turn d (k % L) = turn d k := by
  simp only [turn, Nat.mod_mod_of_dvd k h]

/-- The supplied cut admits a genuinely different next mark as soon as two marks exist. -/
theorem first_turn_readable {d : ℕ} (hd : 1 < d) : turn d 0 ≠ turn d 1 := by
  simp only [turn, Nat.zero_mod, Nat.cast_zero, zero_div, Nat.mod_eq_of_lt hd, Nat.cast_one]
  exact ne_of_lt (by positivity)


/-- Reverse the orientation at the same origin. The reset remains visible. -/
theorem opposite_turn {d : ℕ} (hd : 0 < d) (k : ℕ) :
    turn d k + turn d (d - k%d) = if k%d = 0 then 0 else 1 := by
  unfold turn
  by_cases hz : k%d = 0
  · simp [hz]
  · have hm := Nat.mod_lt k hd
    have hs : d-k%d < d := by omega
    have hsum : k%d + (d-k%d) = d := by omega
    rw [if_neg hz, Nat.mod_eq_of_lt hs, ← add_div, ← Nat.cast_add, hsum, div_self]
    positivity

theorem turn_shift_recover {d L : ℕ} (h : d ∣ L) (k a : ℕ) :
    turn d (k % L + a) = turn d (k+a) := by
  unfold turn
  rw [Nat.add_mod, Nat.mod_mod_of_dvd k h, ← Nat.add_mod]

/-- At opposite sides of a half-tick reflection the two digits sum to d-1.
The reflection is around the last row before a common reset. -/
theorem half_tick_mirror {d : ℕ} (hd : 0 < d) (k j : ℕ) (reset : d ∣ k+j+1) :
    turn d k + turn d j = ((d-1 : ℕ) : ℚ)/d := by
  have congruent := ((Nat.mod_modEq k d).add (Nat.mod_modEq j d)).add_right 1
  have divides := Nat.modEq_zero_iff_dvd.mp (congruent.trans (Nat.modEq_zero_iff_dvd.mpr reset))
  have hk := Nat.mod_lt k hd
  have hj := Nat.mod_lt j hd
  have total : k%d + j%d + 1 = d := by
    obtain ⟨q, hq⟩ := divides
    cases q with
    | zero => simp at hq
    | succ q =>
      cases q with
      | zero => simpa using hq
      | succ q =>
        have hlarge : 2*d ≤ d*(q+1+1) := by nlinarith
        omega
  have hsum : k%d + j%d = d-1 := by omega
  unfold turn
  rw [← add_div, ← Nat.cast_add, hsum]

end PALRH
