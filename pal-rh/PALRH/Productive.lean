import PALRH.OneTick
import Mathlib.Analysis.Polynomial.Order

open Finset Filter Polynomial
open scoped Topology BigOperators
noncomputable section
namespace PALRH.OneTick

/-- Every finite fit has a period that can be recovered from its coefficient support. -/
theorem fit_period {f : ℕ → ℚ} (hf : f ∈ fits) :
    ∃ L : ℕ, 0<L ∧ ∀ m i : ℕ, f (m*L+i) = f i := by
  obtain ⟨N,c,hc⟩ := as_array hf
  let L := (N+1).factorial
  refine ⟨L,Nat.factorial_pos _,?_⟩
  intro m i
  rw [hc (m*L+i),hc i]
  unfold rowError
  congr 2
  apply Finset.sum_congr rfl
  intro j _
  have h : j.val+2 ∣ L := Nat.dvd_factorial (by omega) (by omega)
  have hz : (m*L)%(j.val+2)=0 := Nat.mod_eq_zero_of_dvd (h.trans (dvd_mul_left L m))
  unfold turn
  rw [Nat.add_mod,hz,zero_add,Nat.mod_mod]

private def kernelFactor (i : ℕ) : ℝ[X] :=
  (X+C (i:ℝ))*(X+C ((i:ℝ)+1))

private def numerator (r : ℕ → ℝ) (L : ℕ) : ℝ[X] :=
  ∑ i ∈ Finset.range L, C (r i) * ∏ j ∈ (Finset.range L).erase i, kernelFactor j

def blockMass (r : ℕ → ℝ) (L : ℕ) (z : ℝ) : ℝ :=
  ∑ i ∈ Finset.range L, r i / ((z+i)*(z+i+1))

private lemma carrier_ne_zero {L : ℕ} (hL : 0<L) (r : ℕ → ℝ) (h0 : r 0≠0) :
    numerator r L ≠ 0 := by
  have one : 0 ∈ Finset.range L := Finset.mem_range.mpr hL
  have hval : (numerator r L).eval 0 ≠ 0 := by
    rw [numerator, Polynomial.eval_finsetSum]
    rw [Finset.sum_eq_single_of_mem 0 one (fun i hi hne => ?_)]
    · simp only [Polynomial.eval_mul, Polynomial.eval_C,Polynomial.eval_prod]
      apply mul_ne_zero h0
      apply ne_of_gt
      apply Finset.prod_pos
      intro j hj
      have hn := (Finset.mem_erase.mp hj).1
      have hj0 : 0 < (j:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
      simp only [kernelFactor,Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_X,
        Polynomial.eval_C,zero_add]
      positivity
    · have hj : 0 ∈ (Finset.range L).erase i := Finset.mem_erase.mpr ⟨Ne.symm hne,one⟩
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod]
      have hz : (∏ j ∈ (Finset.range L).erase i, (kernelFactor j).eval 0)=0 :=
        Finset.prod_eq_zero hj (by simp [kernelFactor])
      rw [hz,mul_zero]
  intro he
  exact hval (by simp [he])

private lemma clear_block (r : ℕ → ℝ) (L : ℕ) {z : ℝ} (hz : 0<z) :
    (numerator r L).eval z =
      blockMass r L z * (∏ j ∈ Finset.range L, (kernelFactor j).eval z) := by
  simp only [numerator, Polynomial.eval_finsetSum,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_prod,blockMass,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.prod_erase_mul _ _ hi]
  have hf : (kernelFactor i).eval z = (z+i)*(z+i+1) := by
    simp only [kernelFactor,Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C]
    ring
  rw [hf]
  field_simp

private lemma positive_at_end {P : ℝ[X]} (hne : P ≠ 0) (hc : 0≤P.leadingCoeff) :
    ∀ᶠ z : ℝ in atTop, 0<P.eval z := by
  filter_upwards [eventually_gt_atTop (∑ y ∈ P.roots.toFinset, |y|)] with z hz
  apply Polynomial.zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg _ hc
  intro y hy
  have hm : y ∈ P.roots.toFinset := Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hne).mpr hy)
  exact ((le_abs_self y).trans (Finset.single_le_sum (fun r _ => abs_nonneg r) hm)).trans_lt hz

private theorem signed_head_mass {L : ℕ} (hL : 0<L) (r : ℕ → ℝ) (h0 : r 0≠0) :
    ∃ sign : ℚ, (sign=1 ∨ sign= -1) ∧ ∃ M : ℕ, ∀ z : ℕ, M≤z →
      0 < (sign:ℝ)*blockMass r L z := by
  let P := numerator r L
  have hne : P ≠ 0 := carrier_ne_zero hL r h0
  have eventual : ∃ sign : ℚ, (sign=1 ∨ sign= -1) ∧
      ∀ᶠ x : ℝ in atTop, 0<(sign:ℝ)*P.eval x := by
    by_cases hc : 0≤P.leadingCoeff
    · exact ⟨1,Or.inl rfl,by simpa using positive_at_end hne hc⟩
    · refine ⟨-1,Or.inr rfl,?_⟩
      simpa using positive_at_end (neg_ne_zero.mpr hne) (show 0≤(-P).leadingCoeff by simpa using (le_of_lt (lt_of_not_ge hc)))
  obtain ⟨a,ha,he⟩ := eventual
  have hn : ∀ᶠ z : ℕ in atTop, 0<(a:ℝ)*P.eval (z:ℝ) := tendsto_natCast_atTop_atTop.eventually he
  obtain ⟨M,hM⟩ := eventually_atTop.mp hn
  refine ⟨a,ha,max 1 M,?_⟩
  intro z hz
  have hz0 : 0 < (z:ℝ) := by exact_mod_cast (show 0<z by omega)
  have h := hM z (le_trans (le_max_right _ _) hz)
  change 0<(a:ℝ)*(numerator r L).eval (z:ℝ) at h
  rw [clear_block r L hz0, ← mul_assoc] at h
  have hp : 0 < ∏ j ∈ Finset.range L, (kernelFactor j).eval (z:ℝ) := by
    apply Finset.prod_pos
    intro j _
    simp only [kernelFactor,Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C]
    positivity
  exact pos_of_mul_pos_left h hp.le


private lemma drop_zero_phase (r : ℕ → ℝ) (L : ℕ) (z : ℝ) (h0 : r 0=0) :
    blockMass r (L+1) z = blockMass (fun i => r (i+1)) L (z+1) := by
  unfold blockMass
  rw [Finset.sum_range_succ',h0,zero_div,add_zero]
  apply Finset.sum_congr rfl
  intro i _
  push_cast
  ring

/-- A nonzero phase in a finite block always leaves a signed trace under sufficiently
remote translates of the actual row weights. Leading zero phases can be removed exactly. -/
theorem block_eventually_signed {L : ℕ} (r : ℕ → ℝ) (phase : ∃ i<L, r i≠0) :
    ∃ s : ℚ, (s=1 ∨ s= -1) ∧ ∃ M : ℕ, ∀ z : ℕ, M≤z →
      0 < (s:ℝ)*blockMass r L z := by
  induction L generalizing r with
  | zero => obtain ⟨i,hi,_⟩ := phase; omega
  | succ L ih =>
    by_cases h0 : r 0=0
    · obtain ⟨i,hi,hri⟩ := phase
      have hp : 1 ≤ i := by
        by_contra! h
        exact hri (by simpa [show i=0 by omega] using h0)
      obtain ⟨s,hs,M,hM⟩ := ih (fun j => r (j+1))
        ⟨i-1,by omega,by simpa only [Nat.sub_add_cancel hp] using hri⟩
      refine ⟨s,hs,M,fun z hz => ?_⟩
      rw [drop_zero_phase r L z h0]
      simpa only [Nat.cast_add,Nat.cast_one] using hM (z+1) (by omega)
    · exact signed_head_mass (by omega) r h0

private def physicalWeight (k : ℕ) : ℝ := 1/((k:ℝ)*((k:ℝ)+1))

private lemma physical_succ (k : ℕ) : physicalWeight (k+1) = rowWeight k := by
  simp only [physicalWeight,rowWeight,Nat.cast_add,Nat.cast_one]; ring

private lemma physical_sum (F : ℕ → ℝ) {C : ℝ} (bound : ∀ k, ‖F k‖ ≤ C) :
    Summable (fun k => physicalWeight k * F k) ∧
    (∑' k : ℕ, physicalWeight k * F k) = ∑' n : ℕ, rowWeight n * F (n+1) := by
  have hs : Summable (fun n : ℕ => rowWeight n * F (n+1)) := by
    apply Summable.of_norm_bounded (g := fun n => rowWeight n*C) (rowWeight_hasSum.summable.mul_right _)
    intro n
    have h : 0 ≤ rowWeight n := by unfold rowWeight; positivity
    rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg h]
    exact mul_le_mul_of_nonneg_left (bound _) h
  have hfull : Summable (fun k => physicalWeight k * F k) := (summable_nat_add_iff 1).mp
    (by simpa only [physical_succ] using hs)
  refine ⟨hfull,?_⟩
  have h := hfull.sum_add_tsum_nat_add 1
  have hz : physicalWeight 0=0 := by norm_num [physicalWeight]
  simpa only [Finset.sum_range_one,hz,zero_mul,zero_add,physical_succ] using h.symm

private lemma sum_in_blocks (L : ℕ) [NeZero L] (F : ℕ → ℝ) (hs : Summable F) :
    Summable (fun j : ℕ => ∑ i ∈ Finset.range L, F (j*L+i)) ∧
    (∑' k : ℕ, F k) = ∑' j, ∑ i ∈ Finset.range L, F (j*L+i) := by
  let e := (Nat.divModEquiv L).symm
  have h : Summable (fun x : ℕ × Fin L => F (e x)) := e.summable_iff.mpr hs
  have eq (j : ℕ) : (∑' i : Fin L, F (e (j,i))) = ∑ i ∈ Finset.range L, F (j*L+i) := by
    rw [tsum_fintype]
    exact Fin.sum_univ_eq_sum_range (fun i => F (j*L+i)) L
  constructor
  · simpa only [eq] using h.prod
  · rw [← e.tsum_eq F,h.tsum_prod]
    simp only [eq]

private def carry (p : ℕ) (k : ℕ) : ℚ := ((k/p)%2 : ℕ)

private lemma carry_mem {p : ℕ} (hp : 2≤p) : carry p ∈ fits := by
  have he : carry p = (2:ℚ) • dilate p (turn 2) := by
    funext k
    simp only [carry,dilate,turn,Pi.smul_apply,smul_eq_mul,Nat.cast_ofNat]
    ring
  rw [he]
  exact fits.smul_mem _ (dilate_mem hp (turn_mem (by decide)))

private lemma carry_cases (p k : ℕ) : carry p k = 0 ∨ carry p k = 1 := by
  rcases Nat.mod_two_eq_zero_or_one (k/p) with h|h <;> simp [carry,h]

/-- The overlap of an oriented, late, legal carry with a periodic residual is strictly
positive once the sign of the whole-period mass has stabilized. -/
private lemma positive_overlap {L m : ℕ} (hL : 0<L) (hm : 0<m) (r : ℕ → ℝ)
    (period : ∀ t i : ℕ, r (t*L+i) = r i) {C : ℝ} (bound : ∀ k, ‖r k‖≤C)
    (s : ℚ) (hsign : s=1 ∨ s= -1)
    (paid : ∀ z : ℕ, m*L ≤ z → 0<(s:ℝ)*blockMass r L z) :
    0 < ∑' n : ℕ, rowWeight n * (r (n+1)*((s*carry (m*L) (n+1) : ℚ):ℝ)) := by
  let p := m*L
  let F := fun k : ℕ => r k * ((s*carry p k : ℚ):ℝ)
  have hcap (k : ℕ) : ‖F k‖ ≤ C := by
    rcases carry_cases p k with h | h
    · simpa [F,h] using (norm_nonneg (r k)).trans (bound k)
    · rcases hsign with hpos | hneg
      · simpa [F,h,hpos] using bound k
      · simpa [F,h,hneg] using bound k
  obtain ⟨hSum,transferred⟩ := physical_sum F hcap
  let _ : NeZero L := ⟨hL.ne'⟩
  obtain ⟨hB,grouped⟩ := sum_in_blocks L (fun k => physicalWeight k * F k) hSum
  let block := fun t : ℕ => ∑ i ∈ Finset.range L, physicalWeight (t*L+i)*F (t*L+i)
  have val (t : ℕ) : block t = (((t/m)%2 : ℕ):ℝ) * ((s:ℝ)*blockMass r L ((t*L:ℕ):ℝ)) := by
    dsimp only [block,blockMass]
    rw [Finset.mul_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hq : (t*L+i)/p = t/m := by
      rw [show p=L*m by dsimp [p];ring, ←Nat.div_div_eq_div_mul]
      rw [show t*L+i=i+L*t by ring,Nat.add_mul_div_left _ _ hL,
        Nat.div_eq_of_lt (Finset.mem_range.mp hi),zero_add]
    simp only [physicalWeight,F,carry,hq,period,Rat.cast_mul,Rat.cast_natCast,
      Nat.cast_add,Nat.cast_mul]
    ring
  have hn (t : ℕ) : 0≤block t := by
    rw [val]
    by_cases ht : t<m
    · simp [Nat.div_eq_of_lt ht]
    · exact mul_nonneg (by positivity) (paid _ (Nat.mul_le_mul_right L (le_of_not_gt ht))).le
  have hfirst : 0<block m := by
    rw [val, Nat.div_self hm]
    simpa using paid (m*L) le_rfl
  change 0 < ∑' n, rowWeight n * F (n+1)
  rw [←transferred,grouped]
  exact hfirst.trans_le (hB.le_tsum m (fun n _ => hn n))

private lemma weighted_bounded_sum (h : ℕ → ℝ) {C : ℝ} (hb : ∀ k, ‖h k‖≤C) :
    Summable (fun n : ℕ => rowWeight n*h (n+1)) := by
  have hs := (physical_sum h hb).1
  simpa only [physical_succ] using (summable_nat_add_iff 1).mpr hs

private lemma square_sum (target f : ℕ → ℚ) (hb : bounded target) (hf : f∈fits) :
    Summable (fun n : ℕ => rowWeight n*((target (n+1):ℝ)-(f (n+1):ℝ))^2) := by
  obtain ⟨C,hC⟩ := (fit_properties hf).2
  obtain ⟨D,hD⟩ := hb
  apply weighted_bounded_sum (h := fun k => ((target k:ℝ)-(f k:ℝ))^2) (C := (D+C)^2)
  intro k
  have he := (norm_sub_le (target k:ℝ) (f k:ℝ)).trans (add_le_add (hD k) (hC k))
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) he _

private theorem signed_step (target : ℕ → ℚ) (hb : bounded target) {f g : ℕ → ℚ}
    (hf : f∈fits) (hg : g∈fits) (unit : ∀ k, ‖(g k:ℝ)‖≤1)
    (positive : 0 < ∑' n : ℕ, rowWeight n*(((target (n+1):ℝ)-(f (n+1):ℝ))*(g (n+1):ℝ))) :
    ∃ a : ℚ, 0<a ∧ loss target (f+a • g) < loss target f := by
  let v := ∑' n : ℕ, rowWeight n*(((target (n+1):ℝ)-(f (n+1):ℝ))*(g (n+1):ℝ))
  obtain ⟨a,ha,ha'⟩ := exists_rat_btwn (show (0:ℝ)<v from positive)
  have hnew := fits.add_mem hf (fits.smul_mem a hg)
  obtain ⟨C,hC⟩ := (fit_properties hf).2
  obtain ⟨D,hD⟩ := hb
  have hb' : bounded target := ⟨D,hD⟩
  have hrv := weighted_bounded_sum (h := fun k => ((target k:ℝ)-(f k:ℝ))*(g k:ℝ)) (C := D+C) (by
    intro k
    rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (unit k)).trans
      ((norm_sub_le (target k:ℝ) (f k:ℝ)).trans (add_le_add (hD k) (hC k))))
  have term (n : ℕ) : rowWeight n*((target (n+1):ℝ)-((f+a • g) (n+1):ℝ))^2 ≤
      rowWeight n*((target (n+1):ℝ)-(f (n+1):ℝ))^2-
          2*(a:ℝ)*(rowWeight n*(((target (n+1):ℝ)-(f (n+1):ℝ))*(g (n+1):ℝ)))+
        (a:ℝ)^2*rowWeight n := by
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,Rat.cast_add,Rat.cast_mul]
    have hu : (g (n+1):ℝ)^2 ≤ 1 := by
      simpa only [Real.norm_eq_abs, sq_abs,one_pow] using
        pow_le_pow_left₀ (norm_nonneg (g (n+1):ℝ)) (unit _) 2
    have hw : 0 ≤ rowWeight n := by unfold rowWeight; positivity
    nlinarith [mul_nonneg (mul_nonneg hw (sq_nonneg (a:ℝ))) (sub_nonneg.mpr hu)]
  have sg := hrv.mul_left (2*(a:ℝ))
  have sw := rowWeight_hasSum.summable.mul_left ((a:ℝ)^2)
  have total := (square_sum _ _ hb' hnew).tsum_le_tsum term (((square_sum _ _ hb' hf).sub sg).add sw)
  rw [((square_sum _ _ hb' hf).sub sg).tsum_add sw,(square_sum _ _ hb' hf).tsum_sub sg,
    hrv.tsum_mul_left,rowWeight_hasSum.summable.tsum_mul_left,rowWeight_hasSum.tsum_eq,mul_one] at total
  have eq (x : ℕ→ℚ) : loss target x = ∑' n : ℕ, rowWeight n*((target (n+1):ℝ)-(x (n+1):ℝ))^2 := by
    simp [loss,cost]
  refine ⟨a,by exact_mod_cast ha,?_⟩
  rw [←eq,←eq] at total
  change _ ≤ _ - 2*(a:ℝ)*v+(a:ℝ)^2 at total
  nlinarith [mul_pos ha (sub_pos.mpr ha'),sq_pos_of_pos ha]

private theorem late_step (target : ℕ → ℚ) (hb : bounded target) {f : ℕ → ℚ}
    (hf : f∈fits) (head : ℕ) {L : ℕ} (hL : 0<L) (r : ℕ → ℝ)
    (per : ∀ t i : ℕ, r (t*L+i)=r i) {C : ℝ} (rb : ∀ k, ‖r k‖≤C)
    (agrees : ∀ k : ℕ, 2≤k → (target k:ℝ)-(f k:ℝ)=r k)
    (ready : ∃ s : ℚ, (s=1 ∨ s= -1) ∧ ∃ M : ℕ, ∀ z : ℕ, M≤z → 0<(s:ℝ)*blockMass r L z) :
    ∃ g ∈ fits, (∀ k ≤ head, g k = f k) ∧ loss target g < loss target f := by
  obtain ⟨s,hs,M,hM⟩ := ready
  let m := max M (head+2)
  have hm2 : head+2≤m := le_max_right _ _
  have hmM : M≤m := le_max_left _ _
  have hm : 0<m := by omega
  let p := m*L
  have hmp : m≤p := by
    have he := Nat.mul_le_mul_left m (show 1≤L by omega)
    simpa [p] using he
  let v := s • carry p
  have hv : v∈fits := fits.smul_mem _ (carry_mem (by omega : 2≤p))
  have hc (k : ℕ) : ‖(v k:ℝ)‖≤1 := by
    rcases carry_cases p k with h|h
    · simp [v,Pi.smul_apply,smul_eq_mul,h]
    · rcases hs with pos|neg
      · simp [v,h,pos]
      · simp [v,h,neg]
  have original := positive_overlap hL hm r per rb s hs (fun z hz => hM z (hmM.trans (hmp.trans hz)))
  have eq : (fun n : ℕ => rowWeight n*(((target (n+1):ℝ)-(f (n+1):ℝ))*(v (n+1):ℝ))) =
      (fun n : ℕ => rowWeight n*(r (n+1)*((s*carry p (n+1):ℚ):ℝ))) := by
    funext n
    by_cases small : n+1<p
    · simp [v,Pi.smul_apply,smul_eq_mul,carry,Nat.div_eq_of_lt small]
    · rw [agrees _ (by omega)]
      rfl
  have pos : 0< ∑' n : ℕ, rowWeight n*(((target (n+1):ℝ)-(f (n+1):ℝ))*(v (n+1):ℝ)) := by rw [eq]; exact original
  obtain ⟨a,_,gain⟩ := signed_step target hb hf hv hc pos
  refine ⟨f+a • v, fits.add_mem hf (fits.smul_mem _ hv), ?_,gain⟩
  intro k hk
  have small : k<p := by omega
  simp [v,carry,Pi.smul_apply,smul_eq_mul,Nat.div_eq_of_lt small]

/-- Every finite rational fit admits a strict true-error improvement entirely beyond
any requested finite head. The theorem makes no all-scale rate assumption. -/
theorem strict_successor {f : ℕ → ℚ} (hf : f∈fits) (head : ℕ) :
    ∃ g ∈ fits, (∀ k ≤ head, g k = f k) ∧ loss occupied g < loss occupied f := by
  obtain ⟨L,hL,per⟩ := fit_period hf
  let r := fun k : ℕ => 1-(f k:ℝ)
  have hr0 : r 0 = 1 := by simp [r,(fit_properties hf).1]
  obtain ⟨C,hC⟩ := (fit_properties hf).2
  have rb (k : ℕ) : ‖r k‖ ≤ 1+C := by
    simpa [r] using (norm_sub_le (1:ℝ) (f k:ℝ)).trans (add_le_add (le_refl _) (hC k))
  have hb : bounded occupied := ⟨1,fun k => by by_cases h:k=0 <;> simp [occupied,h]⟩
  exact late_step occupied hb hf head hL r (fun t i => by simp [r,per]) rb
    (fun k hk => by simp [occupied,r,show k≠0 by omega]) (block_eventually_signed r ⟨0,hL,by simp [hr0]⟩)

/-- A whole family of truly productive moves can still leave half the target load unpaid. -/
theorem stalled_first_row {f : ℕ → ℚ} (hf : f∈fits) (wrong : f 1=0) :
    (1:ℝ)/2 ≤ loss occupied f ∧
    ∃ g ∈ fits, g 1=0 ∧ loss occupied g < loss occupied f := by
  have hl := fit_row_lower hf 0
  have hfloor : (1:ℝ)/2 ≤ loss occupied f := by norm_num [wrong,rowWeight] at hl ⊢; exact hl
  obtain ⟨g,hg,keep,less⟩ := strict_successor hf 1
  exact ⟨hfloor,g,hg,(keep 1 le_rfl).trans wrong,less⟩


/-- On the first-tick target every nonzero finite fit admits the same kind of remote
improvement. The zero fit needs a move that visits row one itself. -/
theorem tick_strict_successor {f : ℕ → ℚ} (hf : f∈fits) (nonzero : f≠0) (head : ℕ) :
    ∃ g ∈ fits, (∀ k ≤ head, g k = f k) ∧ loss tick g < loss tick f := by
  obtain ⟨L,hL,per⟩ := fit_period hf
  have haveRow : ∃ j, f j≠0 := by
    by_contra! h
    exact nonzero (funext h)
  obtain ⟨j,hj⟩ := haveRow
  have decomp : j/L*L+j%L=j := by simpa [Nat.mul_comm,Nat.add_comm] using Nat.mod_add_div j L
  have hper : f j=f (j%L) := by simpa only [decomp] using per (j/L) (j%L)
  let r := fun k : ℕ => -(f k:ℝ)
  have phase : ∃ i<L, r i≠0 := ⟨j%L,Nat.mod_lt _ hL,by simp [r,←hper,hj]⟩
  obtain ⟨C,hC⟩ := (fit_properties hf).2
  have rb (k : ℕ) : ‖r k‖≤C := by simpa [r] using hC k
  have hb : bounded tick := ⟨1,fun k => by by_cases h:k=1 <;> simp [tick,h]⟩
  exact late_step tick hb hf head hL r (fun t i => by simp [r,per]) rb
    (fun k hk => by simp [tick,r,show k≠1 by omega]) (block_eventually_signed r phase)

/-- Even a fit with the correct first tick can improve strictly forever while the
next wrong odd row keeps a fixed amount of squared loss. -/
theorem stalled_third_row {f : ℕ → ℚ} (hf : f∈fits) (first : f 1=1) (third : f 3=1) :
    (1:ℝ)/12 ≤ loss tick f ∧
    ∃ g ∈ fits, g 1=1 ∧ g 3=1 ∧ loss tick g < loss tick f := by
  have hb : bounded tick := ⟨1,fun k => by by_cases h:k=1 <;> simp [tick,h]⟩
  have hl := (square_sum tick f hb hf).le_tsum 2
    (fun k _ => mul_nonneg (by unfold rowWeight; positivity) (sq_nonneg _))
  have floor : (1:ℝ)/12 ≤ loss tick f := by
    norm_num [loss,cost,rowWeight,tick,third] at hl ⊢
    exact hl
  have nz : f≠0 := by intro hz; simp [hz] at first
  obtain ⟨g,hg,keep,less⟩ := tick_strict_successor hf nz 3
  exact ⟨floor,g,hg,(keep 1 (by decide)).trans first,(keep 3 le_rfl).trans third,less⟩

#print axioms PALRH.OneTick.tick_strict_successor
#print axioms PALRH.OneTick.stalled_third_row
#print axioms PALRH.OneTick.strict_successor
#print axioms PALRH.OneTick.stalled_first_row
end PALRH.OneTick
