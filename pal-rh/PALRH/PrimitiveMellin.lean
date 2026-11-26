import PALRH.LinearPrimeIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

open Set Finset Filter MeasureTheory Complex Asymptotics
open scoped Topology BigOperators

noncomputable section
namespace PALRH.PrimitiveMellin

def box : ℝ → ℂ := (Set.Ioc (0:ℝ) 1).indicator (fun _ => (1:ℂ))
def logBox (t : ℝ) : ℂ := Real.log t • box t

def window : ℝ → ℝ := (Set.Ioc (0:ℝ) 1).indicator (fun t => t-1-Real.log t)
def reading := WeightedPrimePulse.reading window
def center : ℝ → ℝ := (Set.Ioc (0:ℝ) 1).indicator (fun t => (1/t-1)/2)
def remainder (t : ℝ) : ℂ := (reading t-center t:ℝ)

private theorem log_transform {s : ℂ} (sp : 0<s.re) : HasMellin logBox s (-1/s^2) := by
  have meas : Measurable box := measurable_const.indicator measurableSet_Ioc
  have bound (t : ℝ) : ‖box t‖≤1 := by
    by_cases ht : t∈Set.Ioc (0:ℝ) 1 <;> simp [box,ht]
  have loc : LocallyIntegrableOn box (Set.Ioi 0) :=
    (locallyIntegrableOn_const (1:ℝ)).mono meas.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun t => by simpa using bound t))
  have top : box =O[atTop] (fun x : ℝ => x^(-(s.re+1))) := by
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [eventually_gt_atTop (1:ℝ)] with t ht
    rw [box,Set.indicator_of_notMem (fun h => (not_le_of_gt ht) h.2),norm_zero]
    positivity
  have bot : box =O[𝓝[>] (0:ℝ)] (fun x : ℝ => x^(-(0:ℝ))) := by
    apply isBigO_of_le _
    intro t
    simpa using bound t
  have dh:=mellin_hasDerivAt_of_isBigO_rpow (a:=s.re+1) (b:=0) loc top (by linarith) bot sp
  have same : mellin box =ᶠ[𝓝 s] fun z : ℂ => 1/z := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds sp] with z hz
    exact (hasMellin_one_Ioc hz).2
  have d1:=dh.2.congr_of_eventuallyEq same.symm
  have nz:=ne_zero_of_re_pos sp
  have d2 : HasDerivAt (fun z : ℂ => 1/z) (-1/s^2) s := by
    simpa [div_eq_mul_inv] using (hasDerivAt_inv nz)
  exact ⟨dh.1,d1.unique d2⟩

theorem window_nonneg (t : ℝ) : 0≤window t := by
  by_cases ht : t∈Set.Ioc (0:ℝ) 1
  · rw [window,Set.indicator_of_mem ht]
    exact sub_nonneg.mpr (Real.log_le_sub_one_of_pos ht.1)
  · simp [window,ht]

theorem kernel {s : ℂ} (sp : 0<s.re) :
    HasMellin (fun t => (window t:ℂ)) s (1/(s^2*(s+1))) := by
  have logT:=log_transform sp
  have minusLog:=hasMellin_const_smul logT.1 (-1:ℂ)
  rw [logT.2] at minusLog
  have linear:=LinearPrimeIntegral.base_transform sp
  have sub:=hasMellin_sub minusLog.1 linear.1
  rw [minusLog.2,linear.2] at sub
  have seen : (fun t : ℝ => (-1:ℂ) • logBox t - LinearPrimeIntegral.pulse t) =
      fun t => (window t:ℂ) := by
    funext t
    by_cases ht : t∈Set.Ioc (0:ℝ) 1
    · simp [window,logBox,box,LinearPrimeIntegral.pulse,LinearPrimeIntegral.pulseR,ht,
        Algebra.smul_def]
      ring
    · simp [window,logBox,box,LinearPrimeIntegral.pulse,LinearPrimeIntegral.pulseR,ht]
  rw [seen] at sub
  have nz:=ne_zero_of_re_pos sp
  have pn : s+1≠0 := ne_zero_of_re_pos (by rw [add_re,one_re];linarith)
  convert sub using 1
  simp only [smul_eq_mul]
  field_simp
  ring

private theorem meas_read : Measurable reading := by
  have wm : Measurable window := ((measurable_id.sub measurable_const).sub Real.measurable_log).indicator measurableSet_Ioc
  unfold reading WeightedPrimePulse.reading
  exact Measurable.tsum (fun n => measurable_const.mul (wm.comp (measurable_const.mul measurable_id)))

private theorem outside {t : ℝ} (ht : t∉Set.Ioc (0:ℝ) 1) : remainder t=0 := by
  have gone n : WeightedPrimePulse.term window n t=0 := by
    by_cases nz : n=0
    · simp [nz,WeightedPrimePulse.term]
    have np : (1:ℝ)≤n := by exact_mod_cast Nat.pos_of_ne_zero nz
    have no : (n:ℝ)*t∉Set.Ioc (0:ℝ) 1 := by
      intro h
      have tp : 0<t := pos_of_mul_pos_right h.1 (Nat.cast_nonneg n)
      exact ht ⟨tp,(le_mul_of_one_le_left tp.le np).trans h.2⟩
    simp [WeightedPrimePulse.term,window,no]
  simp [remainder,reading,WeightedPrimePulse.reading,gone,center,ht]

private theorem center_transform {s : ℂ} (sp : 1<s.re) : HasMellin (fun t => (center t:ℂ)) s
    ((1/2)/(s-1)-(1/2)/s) := by
  have base:=LinearPrimeIntegral.principal_transform sp
  have one:=hasMellin_one_Ioc (by linarith : 0<s.re)
  have half:=hasMellin_const_smul one.1 (1/2:ℂ)
  rw [one.2] at half
  have diff:=hasMellin_sub base.1 half.1
  rw [base.2,half.2] at diff
  have eq : (fun t : ℝ => (LinearPrimeIntegral.mainTerm t:ℂ)-
      (1/2:ℂ) • (Set.Ioc (0:ℝ) 1).indicator (fun _ => (1:ℂ)) t) =
      fun t => (center t:ℂ) := by
    funext t
    by_cases ht : t∈Set.Ioc (0:ℝ) 1
    · simp [center,LinearPrimeIntegral.mainTerm,ht];ring
    · simp [center,LinearPrimeIntegral.mainTerm,ht]
  rw [eq] at diff
  convert diff using 1
  simp only [smul_eq_mul]
  ring

private theorem remainder_meas : Measurable remainder := Complex.measurable_ofReal.comp
    (meas_read.sub (((measurable_const.div measurable_id).sub measurable_const).div_const _ |>.indicator measurableSet_Ioc))

private theorem rh_of_regular_remainder
    (smooth : ∀ {s : ℂ}, 1/2<s.re → DifferentiableAt ℂ (mellin remainder) s ∧ MellinConvergent remainder s) :
    RiemannHypothesis := by
  apply LinearPrimeIntegral.rh_of_regular_linear (fun s => s*mellin remainder s)
    (fun s hs => ((hasDerivAt_id s).differentiableAt.mul (smooth hs).1).differentiableWithinAt)
  intro s sr
  have sp : 0<s.re := by linarith
  have body:=WeightedPrimePulse.arithmetic_transform window (fun z => 1/(z^2*(z+1)))
    window_nonneg (fun h => kernel h) sr
  have cent:=center_transform sr
  have agg:=hasMellin_add (smooth (show 1/2<s.re by linarith)).2 cent.1
  have eq : (fun t => remainder t+(center t:ℂ))=(fun t => (reading t:ℂ)) := by
    funext t;simp [remainder]
  rw [eq,cent.2] at agg
  change mellin (fun t => (reading t:ℂ)) s=_ at body
  have val : mellin remainder s=1/(s^2*(s+1))*DysonOctave.primeSeries s-
      ((1/2)/(s-1)-(1/2)/s) := by rw [←body,agg.2];ring
  rw [val]
  have sn:=ne_zero_of_re_pos sp
  have plus : s+1≠0 := ne_zero_of_re_pos (by rw [add_re,one_re];linarith)
  have un : s≠1 := by rintro rfl;norm_num at sr
  field_simp [sn,plus,sub_ne_zero.mpr un]
  ring

theorem rh_of_primitive_bound {D : ℝ} (dn : 0≤D)
    (price : ∀ {t : ℝ}, t∈Set.Ioc (0:ℝ) 1 → ‖remainder t‖≤D/Real.sqrt t) :
    RiemannHypothesis := by
  apply rh_of_regular_remainder
  exact fun sr => WeightedPrimePulse.sqrt_extension remainder remainder_meas outside dn price sr

theorem rh_of_primitive_powers
    (price : ∀ b : ℝ, 1/2<b → b<1 → ∃ D : ℝ, 0≤D ∧
      ∀ t∈Set.Ioc (0:ℝ) 1, ‖remainder t‖≤D*t^(-b)) : RiemannHypothesis := by
  apply rh_of_regular_remainder
  intro s sr
  obtain ⟨b,bh,bs⟩:=exists_between (lt_min sr (by norm_num : (1/2:ℝ)<1))
  obtain ⟨D,dn,pay⟩:=price b bh (bs.trans_le (min_le_right _ _))
  exact WeightedPrimePulse.power_extension remainder remainder_meas outside dn
    (fun ht => pay _ ht) (bs.trans_le (min_le_left _ _))

#print axioms PALRH.PrimitiveMellin.kernel
#print axioms PALRH.PrimitiveMellin.rh_of_primitive_bound
end PALRH.PrimitiveMellin
