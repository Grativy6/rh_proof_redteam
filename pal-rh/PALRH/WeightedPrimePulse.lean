import PALRH.DysonOctave
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open Set Finset Filter MeasureTheory Complex Asymptotics
open scoped Topology BigOperators

noncomputable section
namespace PALRH.WeightedPrimePulse

def term (w : ℝ → ℝ) (n : ℕ) (t : ℝ) : ℝ := ArithmeticFunction.vonMangoldt n*w (n*t)
def reading (w : ℝ → ℝ) (t : ℝ) : ℝ := ∑' n : ℕ, term w n t

private theorem term_mellin (w : ℝ → ℝ) (K : ℂ → ℂ)
    (base : ∀ {z : ℂ}, 0<z.re → HasMellin (fun t => (w t:ℂ)) z (K z)) (n : ℕ) {s : ℂ} (sp : 0<s.re) :
    HasMellin (fun t => (term w n t:ℂ)) s
      ((K s)*LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k:ℂ)) s n) := by
  by_cases nz : n=0
  · subst n
    simp [term,HasMellin,MellinConvergent,mellin,LSeries.term_def]
  have nr : 0<(n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero nz
  have b:=base sp
  have h:=hasMellin_const_smul ((MellinConvergent.comp_mul_left nr).mpr b.1)
    (ArithmeticFunction.vonMangoldt n:ℂ)
  rw [mellin_comp_mul_left (fun u : ℝ => (w u:ℂ)) s nr,b.2] at h
  have eq : (fun t : ℝ => (ArithmeticFunction.vonMangoldt n:ℂ) • (w ((n:ℝ)*t):ℂ)) =
      fun t => (term w n t:ℂ) := by funext t; simp [term]
  rw [eq] at h
  convert h using 1
  simp only [LSeries.term_def,if_neg nz,smul_eq_mul,Complex.cpow_neg,Complex.ofReal_natCast]
  ring

private theorem norm_identity (w : ℝ → ℝ) (wn : ∀ t, 0≤w t) (n : ℕ) (s : ℂ) :
    (((∫ t in Ioi (0:ℝ), ‖(t:ℂ)^(s-1)*(term w n t:ℂ)‖) : ℝ) : ℂ) =
      mellin (fun t => (term w n t:ℂ)) (s.re:ℂ) := by
  have cast : (((∫ t in Ioi (0:ℝ), ‖(t:ℂ)^(s-1)*(term w n t:ℂ)‖) : ℝ) : ℂ) =
      ∫ t in Ioi (0:ℝ), (‖(t:ℂ)^(s-1)*(term w n t:ℂ)‖:ℂ) :=
    (integral_ofReal (𝕜:=ℂ) (μ:=volume.restrict (Ioi (0:ℝ)))).symm
  rw [cast,mellin]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t (tp : 0<t)
  have plus : 0≤term w n t := mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (wn _)
  change ((‖(t:ℂ)^(s-1)*(term w n t:ℂ)‖:ℝ):ℂ) = (t:ℂ)^((s.re:ℂ)-1) • (term w n t:ℂ)
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg plus,
    Complex.norm_cpow_eq_rpow_re_of_pos tp,Complex.sub_re,Complex.one_re,Complex.ofReal_mul]
  have eq : ((s.re:ℂ)-1)=((s.re-1:ℝ):ℂ) := by push_cast;rfl
  rw [eq,←Complex.ofReal_cpow tp.le,smul_eq_mul]

/-- Sum a nonnegative real pulse over actual prime powers. The absolute convergence at
the real part justifies exchanging the Mellin integral with the infinite sum. -/
theorem arithmetic_transform (w : ℝ → ℝ) (K : ℂ → ℂ) (wn : ∀ t, 0≤w t)
    (base : ∀ {z : ℂ}, 0<z.re → HasMellin (fun t => (w t:ℂ)) z (K z))
    {s : ℂ} (sr : 1<s.re) :
    mellin (fun t => (reading w t:ℂ)) s = K s*DysonOctave.primeSeries s := by
  have sp : 0<s.re := by linarith
  have sumC:=ArithmeticFunction.LSeriesSummable_vonMangoldt (s:=(s.re:ℂ)) (by simpa using sr)
  let z:ℂ := s.re
  have vals : Summable (fun n : ℕ => (K z)*
      LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k:ℂ)) z n) :=
    sumC.mul_left _
  have nsum : Summable (fun n : ℕ => ∫ t in Ioi (0:ℝ), ‖(t:ℂ)^(s-1)*(term w n t:ℂ)‖) := by
    apply Complex.summable_ofReal.mp
    exact vals.congr (fun n => ((term_mellin w K base n (s:=z) (by simpa [z] using sp)).2.symm.trans (norm_identity w wn n s).symm))
  have integ n : IntegrableOn (fun t : ℝ => (t:ℂ)^(s-1)*(term w n t:ℂ)) (Ioi 0) := (term_mellin w K base n sp).1
  have agg:=hasSum_integral_of_summable_integral_norm integ nsum
  have enc n : (∫ t in Ioi (0:ℝ), (t:ℂ)^(s-1)*(term w n t:ℂ)) =
      (K s)*LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k:ℂ)) s n :=
    (term_mellin w K base n sp).2
  have total (t : ℝ) : (∑' n : ℕ, (t:ℂ)^(s-1)*(term w n t:ℂ))=(t:ℂ)^(s-1)*(reading w t:ℂ) := by
    rw [tsum_mul_left,reading,Complex.ofReal_tsum]
  rw [show (fun t : ℝ => ∑' n : ℕ, (t:ℂ)^(s-1)*(term w n t:ℂ)) =
    (fun t : ℝ => (t:ℂ)^(s-1)*(reading w t:ℂ)) from funext total] at agg
  simp_rw [enc] at agg
  change (∫ t in Ioi (0:ℝ), (t:ℂ)^(s-1)*(reading w t:ℂ))=_
  rw [←agg.tsum_eq,tsum_mul_left]
  rfl

/-- A growth bound at some real exponent controls the Mellin integral to its right. -/
theorem power_extension (f : ℝ → ℂ) (meas : Measurable f)
    (outside : ∀ {x : ℝ}, x∉Set.Ioc (0:ℝ) 1 → f x=0)
    {D b : ℝ} (dn : 0≤D) (price : ∀ {x : ℝ}, x∈Set.Ioc (0:ℝ) 1 → ‖f x‖≤D*x^(-b))
    {s : ℂ} (hs : b<s.re) : DifferentiableAt ℂ (mellin f) s ∧ MellinConvergent f s := by
  have cost (x : ℝ) : ‖f x‖≤D*|x^(-b)| := by
    by_cases hx : x∈Set.Ioc (0:ℝ) 1
    · rw [abs_of_pos (Real.rpow_pos_of_pos hx.1 _)]
      exact price hx
    · rw [outside hx,norm_zero];positivity
  have ct : ContinuousOn (fun x : ℝ => D*|x^(-b)|) (Set.Ioi 0) :=
    continuousOn_const.mul (continuousOn_of_forall_continuousAt (fun x hx =>
      (Real.continuousAt_rpow_const x _ (Or.inl (ne_of_gt hx))).abs))
  have loc : LocallyIntegrableOn f (Set.Ioi 0) :=
    (ct.locallyIntegrableOn measurableSet_Ioi).mono meas.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => (cost x).trans (le_abs_self _)))
  have top : f =O[atTop] (fun x : ℝ => x^(-(s.re+1))) := by
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [eventually_gt_atTop (1:ℝ)] with x hx
    rw [outside (fun h => (not_le_of_gt hx) h.2),norm_zero];positivity
  have bot : f =O[𝓝[>] (0:ℝ)] (fun x : ℝ => x^(-b)) := by
    apply Asymptotics.IsBigO.of_bound D
    exact Filter.Eventually.of_forall (fun x => by simpa using cost x)
  exact ⟨mellin_differentiableAt_of_isBigO_rpow loc top (by linarith) bot hs,
    mellinConvergent_of_isBigO_rpow loc top (by linarith) bot hs⟩

/-- A reciprocal pulse with a pointwise square-root budget has a holomorphic Mellin transform
to the right of the critical line. -/
theorem sqrt_extension (f : ℝ → ℂ) (meas : Measurable f)
    (outside : ∀ {x : ℝ}, x∉Set.Ioc (0:ℝ) 1 → f x=0)
    {D : ℝ} (dn : 0≤D) (price : ∀ {x : ℝ}, x∈Set.Ioc (0:ℝ) 1 → ‖f x‖≤D/Real.sqrt x)
    {s : ℂ} (hs : 1/2<s.re) : DifferentiableAt ℂ (mellin f) s ∧ MellinConvergent f s := by
  apply power_extension f meas outside (b:=1/2) dn _ hs
  intro x hx
  rw [Real.rpow_neg hx.1.le,←Real.sqrt_eq_rpow,←div_eq_mul_inv]
  exact price hx

end PALRH.WeightedPrimePulse
