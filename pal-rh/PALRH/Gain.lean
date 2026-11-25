import PALRH.Frames

open Finset
open scoped BigOperators

noncomputable section
namespace PALRH

private theorem frame_visits_summable (L i : ℕ) [NeZero L] :
    Summable (fun n : ℕ => rowWeight (i + L*n)) := by
  apply rowWeight_hasSum.summable.comp_injective
  intro a b hab
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_neZero L) (Nat.add_left_cancel hab)

theorem frameMass_nonneg (L i : ℕ) : 0 ≤ frameMass L i :=
  tsum_nonneg fun n => by unfold rowWeight; positivity

theorem first_visit_le_mass (L i : ℕ) [NeZero L] : rowWeight i ≤ frameMass L i := by
  simpa only [frameMass, Nat.mul_zero, Nat.add_zero] using
    (frame_visits_summable L i).le_tsum 0 (fun n _ => by unfold rowWeight; positivity)

/-- The squared error on a finite frame includes all its laps. -/
def energy (L : ℕ) [NeZero L] (residual : ZMod L → ℝ) : ℝ :=
  ∑ i, frameMass L i.val * (residual i)^2

def overlap (L : ℕ) [NeZero L] (r g : ZMod L → ℝ) : ℝ :=
  ∑ i, frameMass L i.val * r i * g i

theorem energy_eq_all_rows (L : ℕ) [NeZero L] (f : ZMod L → ℝ) :
    energy L f = ∑' n : ℕ, rowWeight n * (f n)^2 :=
  (weighted_frame_sum L (fun i => (f i)^2)).symm

/-- The signed overlap and the cost of the new reading determine the improvement. -/
theorem energy_step (L : ℕ) [NeZero L] (r g : ZMod L → ℝ) (a : ℝ) :
    energy L (fun i => r i - a*g i) =
      energy L r - 2*a*overlap L r g + a^2*energy L g := by
  unfold energy overlap
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Opening two readings on the same parent retains the signed mixed term. -/
theorem joint_energy_step (L : ℕ) [NeZero L] (r g h : ZMod L → ℝ) (a b : ℝ) :
    energy L (fun i => r i - a*g i - b*h i) =
      energy L (fun i => r i - a*g i) + energy L (fun i => r i - b*h i)
        - energy L r + 2*a*b*overlap L g h := by
  unfold energy overlap
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem energy_best_step (L : ℕ) [NeZero L] (r g : ZMod L → ℝ) (hg : 0 < energy L g) :
    energy L (fun i => r i - (overlap L r g / energy L g)*g i) =
      energy L r - (overlap L r g)^2 / energy L g := by
  rw [energy_step]
  field_simp
  ring

private theorem turn_between_zero_one {d : ℕ} (hd : 0 < d) (k : ℕ) :
    0 ≤ (turn d k : ℝ) ∧ (turn d k : ℝ) ≤ 1 := by
  have hm := Nat.mod_lt k hd
  unfold turn
  push_cast
  constructor
  · positivity
  · rw [div_le_one (by positivity)]
    exact_mod_cast hm.le

private theorem even_residual_nonneg (k : ℕ) : 0 ≤ (1:ℝ) - 2*(turn 2 k : ℝ) := by
  rcases Nat.mod_two_eq_zero_or_one k with h | h <;> norm_num [turn, h]

/-- A concrete update for every p>2. The old fit is exact on odd rows and has
residual one on row two. All other signed cross contributions are nonnegative. -/
theorem first_fresh_gain {p : ℕ} [NeZero p] (hp : 2 < p) :
    let L := 2*p
    let r : ZMod L → ℝ := fun i => 1-2*(turn 2 (i.val+1) : ℝ)
    let g : ZMod L → ℝ := fun i => (turn p (i.val+1) : ℝ)
    let a : ℝ := 1/(3*(p:ℝ))
    energy L (fun i => r i - a*g i) ≤ energy L r - a^2 := by
  let L := 2*p
  let r : ZMod L → ℝ := fun i => 1-2*(turn 2 (i.val+1) : ℝ)
  let g : ZMod L → ℝ := fun i => (turn p (i.val+1) : ℝ)
  let a : ℝ := 1/(3*(p:ℝ))
  change energy L (fun i => r i - a*g i) ≤ energy L r - a^2
  have hp0 : 0 < p := by omega
  have ha : 0 < a := by dsimp [a]; positivity
  have hl : 1 < L := by dsimp [L]; omega
  have h1 : (1 : ZMod L).val = 1 := by
    simpa only [Nat.cast_one] using (ZMod.val_natCast_of_lt (n := L) (a := 1) hl)
  have hr1 : r 1 = 1 := by norm_num [r, h1, turn]
  have hg1 : g 1 = (2 : ℝ)/p := by norm_num [g, h1, turn, Nat.mod_eq_of_lt hp]
  have hb (i : ZMod L) := turn_between_zero_one hp0 (i.val+1)
  have hcross : a ≤ overlap L r g := by
    have single := Finset.single_le_sum (s := (Finset.univ : Finset (ZMod L)))
      (f := fun i : ZMod L => frameMass L i.val * r i * g i)
      (fun i _ => mul_nonneg (mul_nonneg (frameMass_nonneg _ _) (even_residual_nonneg _)) (hb i).1)
      (Finset.mem_univ (1 : ZMod L))
    change _ ≤ ∑ i, frameMass L i.val * r i * g i
    apply le_trans _ single
    rw [h1, hr1, hg1, mul_one]
    calc
      a = rowWeight 1 * (2 / (p:ℝ)) := by dsimp [a, rowWeight]; push_cast; field_simp; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (first_visit_le_mass L 1) (by positivity)
  have henergy : energy L g ≤ 1 := by
    rw [← frameMass_total L]
    apply Finset.sum_le_sum
    intro i _
    have hg0 : 0 ≤ g i := (hb i).1
    have hg' : g i ≤ 1 := (hb i).2
    exact mul_le_of_le_one_right (frameMass_nonneg _ _) (by nlinarith [mul_nonneg hg0 (sub_nonneg.mpr hg')])
  rw [energy_step]
  nlinarith [mul_nonneg ha.le (sub_nonneg.mpr hcross), mul_nonneg (sq_nonneg a) (sub_nonneg.mpr henergy)]

/-- The improvement is measured on the actual integer visits, with no finite row cutoff. -/
theorem first_fresh_gain_all_rows {p : ℕ} [NeZero p] (hp : 2 < p) :
    let a : ℝ := 1/(3*(p:ℝ))
    (∑' n : ℕ, rowWeight n *
      (1 - 2*(turn 2 (n+1) : ℝ) - a*(turn p (n+1) : ℝ))^2) ≤
      (∑' n : ℕ, rowWeight n * (1-2*(turn 2 (n+1) : ℝ))^2) - a^2 := by
  have h := first_fresh_gain hp
  dsimp only at h ⊢
  rw [energy_eq_all_rows, energy_eq_all_rows] at h
  have h2 : 2 ∣ 2*p := dvd_mul_right _ _
  have hpp : p ∣ 2*p := dvd_mul_left _ _
  simpa only [ZMod.val_natCast, turn_shift_recover h2, turn_shift_recover hpp] using h

end PALRH
