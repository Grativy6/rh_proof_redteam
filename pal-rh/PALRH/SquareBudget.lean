import PALRH.Balanced

open Filter Finset
open scoped Topology BigOperators
noncomputable section
namespace PALRH.SquareBudget
open OneTick _root_.PALRH.Balanced HeadGrowth

/-- This number uses only rational arithmetic at the first H squared physical rows. -/
def window (T f : ℕ → ℚ) (H : ℕ) : ℚ :=
  ∑ i ∈ Finset.range (H*H), (T (i+1)-f (i+1))^2/(((i:ℚ)+1)*(i+2))

private lemma close_tail {T f : ℕ → ℚ} {A : ℝ} (H : ℕ)
    (amp : ∀ k : ℕ, |((T k-f k:ℚ):ℝ)|≤A*H) :
    loss T f≤(window T f H:ℝ)+A^2 := by
  let r := fun k : ℕ => ((T k-f k:ℚ):ℝ)
  let cell := fun n : ℕ => rowWeight n*(r (n+1))^2
  have pos (n : ℕ) : 0≤cell n := mul_nonneg (by unfold rowWeight; positivity) (sq_nonneg _)
  have bound (n : ℕ) : cell n≤rowWeight n*(A*H)^2 := by
    apply mul_le_mul_of_nonneg_left _ (by unfold rowWeight; positivity)
    rw [←sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (amp _) _
  have hs : Summable cell := Summable.of_nonneg_of_le pos bound (rowWeight_hasSum.summable.mul_right _)
  let M := H*H
  have first : (∑ i ∈ Finset.range M, cell i)=(window T f H:ℝ) := by
    simp [M,cell,r,rowWeight,window,div_eq_mul_inv,mul_comm]
  have tail := ((summable_nat_add_iff M).mpr hs).tsum_le_tsum (fun n => bound (n+M))
    (((summable_nat_add_iff M).mpr rowWeight_hasSum.summable).mul_right ((A*H)^2))
  rw [tsum_mul_right,rowWeight_tail] at tail
  change (∑' n, cell n) ≤ _
  rw [←hs.sum_add_tsum_nat_add M,first]
  apply add_le_add (le_refl _) (tail.trans ?_)
  dsimp only [M]
  push_cast
  rw [one_div,←div_eq_inv_mul]
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith [sq_nonneg A]

/-- One deterministic rational profile is tested at each head. For every positive
integer exponent the indicated finite integer-power inequality holds arbitrarily late. -/
def Windows (T : ℕ → ℚ) (t : ℚ) : Prop :=
  ∀ j : ℕ, 0<j → ∀ B : ℕ, ∃ H : ℕ, B≤H ∧ 0<H ∧
    (window T (profile (impulse T) H t) H)^j ≤ (H:ℚ)+1

private theorem windows_subpower {T : ℕ → ℚ} (zero : T 0=0) (smallT : ∀ k, |T k|≤1)
    (smallν : ∀ d, 0<d → |impulse T d|≤2) {t : ℚ} (ht : |t|≤1)
    (checks : Windows T t) : SubpowerHeads T := by
  intro α hα K
  obtain ⟨j,hj⟩ := exists_nat_one_div_lt (half_pos hα)
  have jpos : 0<((j+1:ℕ):ℝ) := by positivity
  have exp : 1≤(α/2)*((j+1:ℕ):ℝ) := by
    have h : 1/((j+1:ℕ):ℝ)<α/2 := by simpa using hj
    exact ((div_lt_iff₀ jpos).mp h).le
  have base : Tendsto (fun H : ℕ => (H:ℝ)+1) atTop atTop :=
    tendsto_atTop_mono (fun n : ℕ => show (n:ℝ)≤(n:ℝ)+1 by linarith) tendsto_natCast_atTop_atTop
  obtain ⟨N,hN⟩ := eventually_atTop.mp (((tendsto_rpow_atTop (half_pos hα)).comp base).eventually_gt_atTop (103^2:ℝ))
  obtain ⟨H,large,hH,check⟩ := checks (j+1) (by omega) (max N K)
  let f := profile (impulse T) H t
  have hit := profile_hits T zero hH t
  have residual (k : ℕ) : |((T k-f k:ℚ):ℝ)| ≤ 103*H := by
    have headValue := floor_recovers T zero H H le_rfl
    have form := profile_bound (impulse T) hH t ht (fun d hd => smallν d (Finset.mem_Icc.mp hd).1)
      (headValue ▸ smallT H) k
    have bound := abs_sub (T k) (f k)
    have hh : (1:ℚ)≤H := by exact_mod_cast hH
    change |f k| ≤ _ at form
    exact_mod_cast (show |T k-f k|≤103*(H:ℚ) by linarith [smallT k])
  have total := close_tail (A:=103) H residual
  let P := (window T f H:ℝ)
  let L := ((H:ℝ)+1)^(α/2)
  have one : 1≤(H:ℝ)+1 := by linarith [Nat.cast_nonneg (α:=ℝ) H]
  have hL : 0<L := Real.rpow_pos_of_pos (by positivity) _
  have headP : P^(j+1) ≤ (H:ℝ)+1 := by dsimp only [P,f]; exact_mod_cast check
  have allowed : (H:ℝ)+1 ≤ L^(j+1) := by
    dsimp only [L]
    rw [←Real.rpow_natCast,←Real.rpow_mul (by positivity)]
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le one exp
  have localP : P≤L := by
    by_contra! bad
    exact (not_lt_of_ge (headP.trans allowed)) (pow_lt_pow_left₀ bad hL.le (by omega))
  have room : (103^2:ℝ)<L := by simpa only [Function.comp_apply,L] using hN H ((le_max_left N K).trans large)
  have cap : loss T f ≤ L*L := by
    change loss T f ≤ P+103^2 at total
    nlinarith [mul_nonneg hL.le (show 0≤L-2 by linarith)]
  refine ⟨H,(le_max_right N K).trans large,f,profile_mem _ _ _,fun k _ hk => hit k hk,?_⟩
  have result : L*L=((H:ℝ)+1)^α := by
    rw [←Real.rpow_add (by positivity),show α/2+α/2=α by ring]
  exact cap.trans_eq result

theorem rh_of_occupied_windows (checks : Windows occupied 1) : RiemannHypothesis := by
  apply rh_of_subpower_occupied
  apply windows_subpower (by norm_num [occupied]) (fun k => by by_cases h:k=0 <;> simp [occupied,h]) _ (by norm_num) checks
  intro d hd
  rw [occupied_impulse hd]
  have cap : |mu d|≤1 := by unfold mu; exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n:=d))
  linarith

theorem rh_of_tick_windows (checks : Windows tick 0) : RiemannHypothesis := by
  apply rh_of_subpower_tick
  apply windows_subpower (by norm_num [tick]) (fun k => by by_cases h:k=1 <;> simp [tick,h]) _ (by norm_num) checks
  intro d hd
  rw [tick_impulse hd]
  have bound (n : ℕ) : |mu n|≤1 := by unfold mu; exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n:=n))
  have half : |doubleMu d|≤1 := by
    by_cases h : 2 ∣ d
    · simpa [doubleMu,h] using bound (d/2)
    · simp [doubleMu,h]
  exact (abs_sub _ _).trans (by linarith [bound d])

#print axioms PALRH.SquareBudget.rh_of_occupied_windows
#print axioms PALRH.SquareBudget.rh_of_tick_windows
end PALRH.SquareBudget
