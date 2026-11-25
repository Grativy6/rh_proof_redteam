import PALRH.CensusTransfer
import Mathlib.NumberTheory.LSeries.Nonvanishing

open Finset Set Filter Complex MeasureTheory
open scoped Topology BigOperators
noncomputable section
namespace PALRH.SignedAreas
open RectangleBalance CensusTransfer

def measured (s : ℂ) (X : ℝ) (f : ℝ → ℝ) : ℂ :=
  (X:ℂ)^s * ∫ x in Set.Ioc 0 X, (x:ℂ)^(-s)*(f x:ℂ)

def wave (s : ℂ) (x : ℝ) : ℂ := (x:ℂ)^(-s)*(edge x:ℂ)

private theorem wave_cont (s : ℂ) (X : ℝ) : ContinuousOn (wave s) (Set.Iic X) := by
  let factor := fun x : ℝ => ((max x (1/4):ℝ):ℂ)^(-s)
  have continuous : Continuous factor := by
    apply continuous_iff_continuousAt.mpr
    intro x
    have inner : ContinuousAt (fun y : ℝ => max y (1/4)) x := (continuous_id.max continuous_const).continuousAt
    change ContinuousAt ((fun t : ℝ => (t:ℂ)^(-s)) ∘ (fun y : ℝ => max y (1/4))) x
    exact (continuousAt_ofReal_cpow_const (max x (1/4)) (-s) (Or.inr
      (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/4) (le_max_right x _)).ne')).comp (f:=fun y : ℝ => max y (1/4)) inner
  apply (continuous.continuousOn.mul (Complex.continuous_ofReal.comp_continuousOn (edge_continuousOn X))).congr
  intro x _
  change (x:ℂ)^(-s)*(edge x:ℂ)=factor x*(edge x:ℂ)
  by_cases hi : 1/4≤x
  · simp only [factor,max_eq_left hi]
  · simp [edge_before (show x≤1/2 by linarith),factor]

private theorem wave_int (s : ℂ) (X : ℝ) : IntegrableOn (wave s) (Set.Ioc 0 X) :=
  (((wave_cont s X).mono (fun _ hx => hx.2)).integrableOn_compact
    (isCompact_Icc (α:=ℝ) (a:=0) (b:=X))).mono_set Set.Ioc_subset_Icc_self

private theorem observation_pad (f : ℕ → ℝ) {x X : ℝ} (before : x≤X) :
    observe f x=∑ n ∈ Finset.Icc 1 ⌊2*X⌋₊, f n/n*edge (x/n) := by
  apply Finset.sum_subset
  · intro n hn
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1,(Finset.mem_Icc.mp hn).2.trans
      (Nat.floor_le_floor (by linarith))⟩
  · intro n hn miss
    have np := (Finset.mem_Icc.mp hn).1
    have out : ⌊2*x⌋₊<n := by by_contra! h;exact miss (Finset.mem_Icc.mpr ⟨np,h⟩)
    have b := Nat.lt_of_floor_lt out
    rw [edge_before ((div_le_iff₀ (by exact_mod_cast (show 0<n from np) : 0<(n:ℝ))).mpr
      (by linarith)),mul_zero]

private def term (s : ℂ) (c : ℝ) (r : ℕ) (x : ℝ) :=
  (x:ℂ)^(-s)*(c:ℂ)/(r:ℂ)*(edge (x/r):ℂ)

private theorem scale_term (s : ℂ) (c : ℝ) {r : ℕ} (hp : 0<r) {x : ℝ} (xp : 0<x) :
    term s c r x=((r:ℂ)^(-s)*(c:ℂ)/(r:ℂ))*wave s (x/r) := by
  have rp : 0<(r:ℝ) := by exact_mod_cast hp
  dsimp only [term,wave]
  rw [Complex.ofReal_div,Complex.div_cpow_ofReal_nonneg xp.le rp.le,Complex.ofReal_natCast]
  have non : (r:ℂ)^(-s)≠0 := by rw [Ne,Complex.cpow_eq_zero_iff,not_and_or];exact Or.inl (by exact_mod_cast hp.ne')
  field_simp

private theorem scaled_int (s : ℂ) (c : ℝ) {r : ℕ} (hp : 0<r) {X : ℝ} (_xp : 0<X) :
    IntegrableOn (term s c r) (Set.Ioc 0 X) := by
  have rp : 0<(r:ℝ) := by exact_mod_cast hp
  apply (integrableOn_congr_fun (fun _ (hx : _∈Set.Ioc 0 X) => scale_term s c hp hx.1) measurableSet_Ioc).mpr
  apply Integrable.const_mul
  have cont : ContinuousOn (fun x : ℝ => wave s (x/r)) (Set.Icc 0 X) :=
    (wave_cont s (X/r)).comp (continuous_id.div_const _).continuousOn
      (fun _ hx => div_le_div_of_nonneg_right hx.2 rp.le)
  exact (cont.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self

private theorem integrate_term (s : ℂ) (c : ℝ) {r : ℕ} (hp : 0<r) {X : ℝ} (xp : 0<X) :
    (∫ x in Set.Ioc 0 X, term s c r x) =
      ((r:ℂ)^(-s)*(c:ℂ))*(∫ y in Set.Ioc 0 (X/r), wave s y) := by
  have rp : 0<(r:ℝ) := by exact_mod_cast hp
  rw [setIntegral_congr_fun measurableSet_Ioc (fun x (hx : x∈Set.Ioc 0 X) => scale_term s c hp hx.1),
    integral_const_mul,←intervalIntegral.integral_of_le xp.le,
    intervalIntegral.integral_comp_div (wave s) rp.ne',zero_div,
    intervalIntegral.integral_of_le (div_nonneg xp.le rp.le),Complex.real_smul,Complex.ofReal_natCast]
  field_simp [show (r:ℂ)≠0 by exact_mod_cast hp.ne']

private theorem coefs (f : ℕ → ℝ) (s : ℂ) {X : ℝ} (xp : 0<X) :
    measured s X (observe f)=(X:ℂ)^s*∑ r ∈ Finset.Icc 1 ⌊2*X⌋₊,
        ((r:ℂ)^(-s)*(f r:ℂ))*(∫ y in Set.Ioc 0 (X/r), wave s y) := by
  have same (x : ℝ) (hx : x∈Set.Ioc 0 X) :
      (x:ℂ)^(-s)*(observe f x:ℂ)=∑ r ∈ Finset.Icc 1 ⌊2*X⌋₊, term s (f r) r x := by
    rw [observation_pad f hx.2,Complex.ofReal_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    dsimp only [term]
    push_cast
    ring
  rw [measured,setIntegral_congr_fun measurableSet_Ioc same,
    integral_finsetSum _ (fun r hr => scaled_int s (f r) (Finset.mem_Icc.mp hr).1 xp)]
  congr 1
  exact Finset.sum_congr rfl (fun r hr => integrate_term s (f r) (Finset.mem_Icc.mp hr).1 xp)



private def cutTerm (s : ℂ) (X : ℝ) (f : ℕ → ℝ) (r : ℕ) (y : ℝ) : ℂ :=
  (Set.Ioc 0 (X/r)).indicator (fun t => ((r:ℂ)^(-s)*(f r:ℂ))*wave s t) y

private theorem cut_int (s : ℂ) (X : ℝ) (f : ℕ → ℝ) (r : ℕ) :
    IntegrableOn (cutTerm s X f r) (Set.Ioc 0 X) :=
  ((wave_int s X).const_mul _).indicator measurableSet_Ioc

private theorem integral_cut (s : ℂ) {X : ℝ} (xp : 0<X) (f : ℕ → ℝ) {r : ℕ} (hp : 0<r) :
    (∫ y in Set.Ioc 0 X, cutTerm s X f r y)=
      ((r:ℂ)^(-s)*(f r:ℂ))*(∫ y in Set.Ioc 0 (X/r), wave s y) := by
  have rp : (1:ℝ)≤r := by exact_mod_cast hp
  have sub : Set.Ioc 0 (X/r)⊆Set.Ioc 0 X := fun _ h => ⟨h.1,h.2.trans (div_le_self xp.le rp)⟩
  unfold cutTerm
  rw [integral_indicator measurableSet_Ioc,Measure.restrict_restrict measurableSet_Ioc,
    Set.inter_eq_left.mpr sub,integral_const_mul]

private theorem regroup (s : ℂ) {X : ℝ} (xp : 0<X) (f : ℕ → ℝ) {y : ℝ} (yp : 0<y) :
    (X:ℂ)^s*(∑ r ∈ Finset.Icc 1 ⌊2*X⌋₊, cutTerm s X f r y) =
      (edge y:ℂ)*read f s (X/y) := by
  by_cases early : y≤1/2
  · simp [cutTerm,Set.indicator,wave,edge_before early]
  have past : 1/2<y := lt_of_not_ge early
  let I := Finset.Icc 1 ⌊2*X⌋₊
  have maxr : X/y≤2*X := (div_le_iff₀ yp).mpr (by nlinarith)
  have eq : I.filter (fun r : ℕ => y≤X/r)=Finset.Icc 1 ⌊X/y⌋₊ := by
    ext r
    simp only [I,Finset.mem_filter,Finset.mem_Icc]
    by_cases non : 0<r
    · have rp : 0<(r:ℝ) := by exact_mod_cast non
      have d : y≤X/r ↔ (r:ℝ)≤X/y := by rw [le_div_iff₀ rp,le_div_iff₀ yp,mul_comm]
      rw [d,←Nat.le_floor_iff (div_nonneg xp.le yp.le)]
      have h := Nat.floor_le_floor maxr
      omega
    · omega
  have pack : (∑ r ∈ I, cutTerm s X f r y)=
      (∑ r ∈ Finset.Icc 1 ⌊X/y⌋₊, (r:ℂ)^(-s)*(f r:ℂ))*wave s y := by
    rw [←eq,Finset.sum_mul,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro r _
    by_cases keep : y≤X/r <;> simp [cutTerm,Set.indicator,Set.mem_Ioc,yp,keep]
  rw [pack]
  unfold CensusTransfer.read wave
  rw [Complex.ofReal_div,Complex.div_cpow_ofReal_nonneg xp.le yp.le,Complex.cpow_neg]
  ring

/-- Multiplicative changes of the physical scale and the finite complex response use the identical cutoff. -/
theorem finite_transfer (f : ℕ → ℝ) (s : ℂ) {X : ℝ} (xp : 0<X) :
    measured s X (observe f)=∫ y in Set.Ioc 0 X, (edge y:ℂ)*read f s (X/y) := by
  rw [coefs f s xp]
  have each (r : ℕ) (hr : r∈Finset.Icc 1 ⌊2*X⌋₊) := (integral_cut s xp f (Finset.mem_Icc.mp hr).1).symm
  rw [Finset.sum_congr rfl each,←integral_finsetSum _ (fun r _ => cut_int s X f r),←integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro y hy
  exact regroup s xp f hy.1

private theorem pulse_early {x : ℝ} (xp : 0<x) (low : x≤1/2) : AlternatingRead.pulse x=0 := by
  have a : 2≤1/x := (le_div_iff₀ xp).mpr (by linarith)
  have b : 2≤2/x := (le_div_iff₀ xp).mpr (by linarith)
  simp only [AlternatingRead.pulse,taper,min_eq_right (by linarith : 2-1/x≤1),
    min_eq_right (by linarith : 2-2/x≤1),max_eq_left (by linarith : 2-1/x≤0),
    max_eq_left (by linarith : 2-2/x≤0),sub_self]

private theorem pulse_late {x : ℝ} (hi : 2≤x) : AlternatingRead.pulse x=0 := by
  have pos : 0<x := by linarith
  have a : 1/x≤1 := (div_le_iff₀ pos).mpr (by linarith)
  have b : 2/x≤1 := (div_le_iff₀ pos).mpr (by linarith)
  simp only [AlternatingRead.pulse,taper,min_eq_left (by linarith : 1≤2-1/x),
    min_eq_left (by linarith : 1≤2-2/x),sub_self]

private theorem measured_pulse (s : ℂ) {X : ℝ} (large : 2≤X) :
    measured s X (observe signed)=(X:ℂ)^s*AlternatingRead.moment s := by
  rw [measured,AlternatingRead.moment,intervalIntegral.integral_of_le (by norm_num : (1/2:ℝ)≤2)]
  congr 1
  have sub : Set.Ioc (1/2:ℝ) 2⊆Set.Ioc 0 X := fun _ h => ⟨by linarith [h.1],h.2.trans large⟩
  rw [setIntegral_congr_fun measurableSet_Ioc (f:=fun x : ℝ => (x:ℂ)^(-s)*(observe signed x:ℂ))
    (g:=fun x : ℝ => (x:ℂ)^(-s)*(AlternatingRead.pulse x:ℂ)) (fun x hx => by dsimp;rw [actual_pulse hx.1])]
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioc sub
  rintro x ⟨hx,out⟩
  by_cases low : x≤1/2
  · simp [pulse_early hx.1 low]
  · have late : 2<x := by by_contra! h;exact out ⟨lt_of_not_ge low,h⟩
    simp [pulse_late late.le]

def gross (X : ℝ) := ∫ y in Set.Ioc 0 X, |edge y|

/-- A hypothetical zero must charge the measured absolute area at every real cutoff at least two. -/
theorem zero_bill {s : ℂ} (sp : 0<s.re) (below : s.re<1) (zero : riemannZeta s=0) {X : ℝ} (large : 2≤X) :
    X^s.re*‖AlternatingRead.moment s‖≤4*(1+‖s‖/s.re)*gross X := by
  have xp : 0<X := by linarith
  have n1 : s≠1 := by rintro rfl;norm_num at below
  have data := finite_transfer signed s xp
  rw [measured_pulse s large] at data
  rw [←Complex.norm_cpow_eq_rpow_re_of_pos xp s,←norm_mul,data,gross,←integral_const_mul]
  apply norm_integral_le_of_norm_le
  · apply Integrable.const_mul
    exact (((edge_continuousOn X).abs.mono (fun _ hx => hx.2)).integrableOn_compact
      (isCompact_Icc (α:=ℝ) (a:=0) (b:=X))).mono_set Set.Ioc_subset_Icc_self
  · filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Ioc] with y hy
    have pay := signed_bound sp n1 zero (div_pos xp hy.1)
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_comm]
    exact mul_le_mul_of_nonneg_right pay (abs_nonneg _)

#print axioms PALRH.SignedAreas.finite_transfer
#print axioms PALRH.SignedAreas.zero_bill


/-- An upper budget for the unweighted true area is required only at arbitrarily late cuts. -/
def SparseGross : Prop := ∀ a : ℝ, 1/2<a → ∀ K : ℕ,
  ∃ H : ℕ, K≤H ∧ gross H≤(H:ℝ)^a

theorem rh_of_sparse_gross (budget : SparseGross) : RiemannHypothesis := by
  apply rh_of_right
  intro s hs except hz
  by_cases right : 1≤s.re
  · exact riemannZeta_ne_zero_of_one_le_re right hz
  have below := lt_of_not_ge right
  have sp : 0<s.re := by linarith
  have non := norm_pos_iff.mpr (AlternatingRead.pulse_ne_zero sp below)
  let a := (1/2+s.re)/2
  let d := s.re-a
  have gap : 0<d := by dsimp [a,d];linarith
  let C := 4*(1+‖s‖/s.re)
  have cpos : 0≤C := by dsimp [C];positivity
  obtain ⟨K,large⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop gap).comp tendsto_natCast_atTop_atTop).eventually_gt_atTop
      (C/‖AlternatingRead.moment s‖))
  obtain ⟨H,late,cost⟩ := budget a (by dsimp [a];linarith) (max K 2)
  have two : 2≤H := (le_max_right K 2).trans late
  have hp : 0<(H:ℝ) := by exact_mod_cast (show 0<H by omega)
  have moved : C/‖AlternatingRead.moment s‖<(H:ℝ)^d := by
    simpa only [Function.comp_apply] using large H ((le_max_left K 2).trans late)
  have strict := mul_lt_mul_of_pos_right ((div_lt_iff₀ non).mp moved) (Real.rpow_pos_of_pos hp a)
  have pay := (zero_bill sp below hz (X:=(H:ℝ)) (by exact_mod_cast two)).trans
    (mul_le_mul_of_nonneg_left cost cpos)
  change (H:ℝ)^s.re*‖AlternatingRead.moment s‖≤C*(H:ℝ)^a at pay
  rw [show s.re=d+a by dsimp [d];ring,Real.rpow_add hp] at pay
  linarith

#print axioms PALRH.SignedAreas.rh_of_sparse_gross


theorem readout_int (s : ℂ) (f : ℕ → ℝ) {X : ℝ} (xp : 0<X) :
    IntegrableOn (fun y : ℝ => (edge y:ℂ)*read f s (X/y)) (Set.Ioc 0 X) := by
  apply (integrableOn_congr_fun (fun y (hy : y∈Set.Ioc 0 X) => (regroup s xp f hy.1).symm) measurableSet_Ioc).mpr
  exact (integrable_finsetSum _ (fun r _ => cut_int s X f r)).const_mul _

theorem observed_cont (f : ℕ → ℝ) (X : ℝ) : ContinuousOn (observe f) (Set.Iic X) := by
  apply ContinuousOn.congr (f:=fun x : ℝ => ∑ r ∈ Finset.Icc 1 ⌊2*X⌋₊, f r/r*edge (x/r))
  · apply continuousOn_finsetSum
    intro r hr
    have rp : 0<(r:ℝ) := by exact_mod_cast (show 0<r from (Finset.mem_Icc.mp hr).1)
    exact continuousOn_const.mul ((edge_continuousOn (X/r)).comp (continuous_id.div_const _).continuousOn
      (fun _ hx => div_le_div_of_nonneg_right hx rp.le))
  · exact fun _ hx => observation_pad f hx

theorem observed_early (f : ℕ → ℝ) {x : ℝ} (small : x≤1/2) : observe f x=0 := by
  apply Finset.sum_eq_zero
  intro r hr
  have rp : 0<(r:ℝ) := by exact_mod_cast (show 0<r from (Finset.mem_Icc.mp hr).1)
  have one : 1≤(r:ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hr).1
  rw [edge_before ((div_le_iff₀ rp).mpr (by linarith)),mul_zero]

end PALRH.SignedAreas
