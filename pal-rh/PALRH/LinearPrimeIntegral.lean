import PALRH.DysonOctave
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Complex.RemovableSingularity

open Set Finset Filter MeasureTheory Complex Asymptotics
open scoped Topology BigOperators

noncomputable section
namespace PALRH.LinearPrimeIntegral

def pulseR (t : ℝ) : ℝ := (Ioc (0:ℝ) 1).indicator (fun u => 1-u) t
def pulse (t : ℝ) : ℂ := pulseR t
def term (n : ℕ) (t : ℝ) : ℝ := ArithmeticFunction.vonMangoldt n*pulseR (n*t)
def reading (t : ℝ) : ℝ := ∑' n : ℕ, term n t
def fullWalk (n : ℕ) : ℝ := ∑ k ∈ Icc 1 n, ((n:ℝ)-k)*ArithmeticFunction.vonMangoldt k
def primeWalk (n : ℕ) : ℝ := ∑ p ∈ Icc 1 n, if p.Prime then ((n:ℝ)-p)*Real.log p else 0

private theorem pulse_nonneg (t : ℝ) : 0≤pulseR t := by
  unfold pulseR
  by_cases inside : t∈Ioc (0:ℝ) 1
  · rw [indicator_of_mem inside];exact sub_nonneg.mpr inside.2
  · rw [indicator_of_notMem inside]

private theorem pulse_positive {t : ℝ} (tp : 0<t) : pulseR t=max 0 (1-t) := by
  by_cases near : t≤1
  · simp [pulseR,indicator_of_mem (show t∈Ioc (0:ℝ) 1 from ⟨tp,near⟩),max_eq_right (sub_nonneg.mpr near)]
  · simp [pulseR,not_le.mp near |>.le,near]

theorem base_transform {s : ℂ} (sp : 0<s.re) : HasMellin pulse s (1/(s*(s+1))) := by
  have plus : 0<s.re+(1:ℂ).re := by simp;linarith
  have one:=hasMellin_one_Ioc sp
  have lin:=hasMellin_cpow_Ioc 1 plus
  have h:=hasMellin_sub one.1 lin.1
  rw [one.2,lin.2] at h
  have orig : (fun t : ℝ => ((Ioc (0:ℝ) 1).indicator (fun _ => (1:ℂ)) t)-
      (Ioc (0:ℝ) 1).indicator (fun u => (u:ℂ)^((1:ℂ))) t)=pulse := by
    funext t
    by_cases inside : t∈Ioc (0:ℝ) 1 <;> simp [pulse,pulseR,inside]
  rw [orig] at h
  have a : s≠0 := ne_zero_of_re_pos sp
  have b : s+1≠0 := ne_zero_of_re_pos (by simpa [add_re] using plus)
  have value : 1/s-1/(s+1)=1/(s*(s+1)) := by field_simp; ring
  rwa [value] at h

private theorem term_mellin (n : ℕ) {s : ℂ} (sp : 0<s.re) :
    HasMellin (fun t => (term n t:ℂ)) s
      ((1/(s*(s+1)))*LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k:ℂ)) s n) := by
  by_cases nz : n=0
  · subst n
    simp [term,HasMellin,MellinConvergent,mellin,LSeries.term_def]
  have nr : 0<(n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero nz
  have b:=base_transform sp
  have h:=hasMellin_const_smul ((MellinConvergent.comp_mul_left nr).mpr b.1)
    (ArithmeticFunction.vonMangoldt n:ℂ)
  rw [mellin_comp_mul_left _ _ nr,b.2] at h
  have eq : (fun t : ℝ => (ArithmeticFunction.vonMangoldt n:ℂ) • pulse ((n:ℝ)*t)) =
      fun t => (term n t:ℂ) := by funext t; simp [term,pulse]
  rw [eq] at h
  convert h using 1
  simp only [LSeries.term_def,if_neg nz,smul_eq_mul,Complex.cpow_neg,Complex.ofReal_natCast]
  ring

private theorem norm_identity (n : ℕ) (s : ℂ) :
    (((∫ t in Ioi (0:ℝ), ‖(t:ℂ)^(s-1)*(term n t:ℂ)‖) : ℝ) : ℂ) =
      mellin (fun t => (term n t:ℂ)) (s.re:ℂ) := by
  have cast : (((∫ t in Ioi (0:ℝ), ‖(t:ℂ)^(s-1)*(term n t:ℂ)‖) : ℝ) : ℂ) =
      ∫ t in Ioi (0:ℝ), (‖(t:ℂ)^(s-1)*(term n t:ℂ)‖:ℂ) :=
    (integral_ofReal (𝕜:=ℂ) (μ:=volume.restrict (Ioi (0:ℝ)))).symm
  rw [cast,mellin]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t (tp : 0<t)
  have plus : 0≤term n t := mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (pulse_nonneg _)
  change ((‖(t:ℂ)^(s-1)*(term n t:ℂ)‖:ℝ):ℂ) = (t:ℂ)^((s.re:ℂ)-1) • (term n t:ℂ)
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg plus,
    Complex.norm_cpow_eq_rpow_re_of_pos tp,Complex.sub_re,Complex.one_re,Complex.ofReal_mul]
  have eq : ((s.re:ℂ)-1)=((s.re-1:ℝ):ℂ) := by push_cast;rfl
  rw [eq,←Complex.ofReal_cpow tp.le,smul_eq_mul]

/-- This Mellin identity starts with the actual sum of weighted prime powers, each
of which has finite support in the reciprocal frame. -/
theorem arithmetic_transform {s : ℂ} (sr : 1<s.re) :
    mellin (fun t => (reading t:ℂ)) s = DysonOctave.primeSeries s/(s*(s+1)) := by
  have sp : 0<s.re := by linarith
  have sumC:=ArithmeticFunction.LSeriesSummable_vonMangoldt (s:=(s.re:ℂ)) (by simpa using sr)
  let z:ℂ := s.re
  have vals : Summable (fun n : ℕ => (1/(z*(z+1)))*
      LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k:ℂ)) z n) :=
    sumC.mul_left _
  have nsum : Summable (fun n : ℕ => ∫ t in Ioi (0:ℝ), ‖(t:ℂ)^(s-1)*(term n t:ℂ)‖) := by
    apply Complex.summable_ofReal.mp
    exact vals.congr (fun n => ((term_mellin n (s:=z) (by simpa [z] using sp)).2.symm.trans (norm_identity n s).symm))
  have integ n : IntegrableOn (fun t : ℝ => (t:ℂ)^(s-1)*(term n t:ℂ)) (Ioi 0) := (term_mellin n sp).1
  have agg:=hasSum_integral_of_summable_integral_norm integ nsum
  have enc n : (∫ t in Ioi (0:ℝ), (t:ℂ)^(s-1)*(term n t:ℂ)) =
      (1/(s*(s+1)))*LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k:ℂ)) s n :=
    (term_mellin n sp).2
  have total (t : ℝ) : (∑' n : ℕ, (t:ℂ)^(s-1)*(term n t:ℂ))=(t:ℂ)^(s-1)*(reading t:ℂ) := by
    rw [tsum_mul_left,reading,Complex.ofReal_tsum]
  rw [show (fun t : ℝ => ∑' n : ℕ, (t:ℂ)^(s-1)*(term n t:ℂ)) =
    (fun t : ℝ => (t:ℂ)^(s-1)*(reading t:ℂ)) from funext total] at agg
  simp_rw [enc] at agg
  change (∫ t in Ioi (0:ℝ), (t:ℂ)^(s-1)*(reading t:ℂ))=_
  rw [←agg.tsum_eq,tsum_mul_left]
  unfold DysonOctave.primeSeries LSeries
  ring

private theorem finite_read {t : ℝ} (tp : 0<t) (N : ℕ) (cap : 1≤(N:ℝ)*t) :
    reading t=∑ d ∈ Finset.Icc 1 N, term d t := by
  apply tsum_eq_sum
  intro d out
  by_cases zero : d=0
  · simp [term,zero]
  · have dp : 0<d := Nat.pos_of_ne_zero zero
    have high : N<d := lt_of_not_ge (fun h => out (Finset.mem_Icc.mpr ⟨dp,h⟩))
    have dr : (N:ℝ)≤d := by exact_mod_cast high.le
    have large := cap.trans (mul_le_mul_of_nonneg_right dr tp.le)
    have pos : 0<(d:ℝ)*t := mul_pos (by exact_mod_cast dp) tp
    simp [term,pulse_positive pos,max_eq_left (sub_nonpos.mpr large)]

private theorem decreasing {t u : ℝ} (tp : 0<t) (tu : t≤u) : reading u≤reading t := by
  obtain ⟨N,hn⟩:=exists_nat_ge (1/t)
  have cap : 1≤(N:ℝ)*t := (div_le_iff₀ tp).mp hn
  rw [finite_read (tp.trans_le tu) N (cap.trans (mul_le_mul_of_nonneg_left tu (Nat.cast_nonneg _))),
    finite_read tp N cap]
  apply Finset.sum_le_sum
  intro d hd
  have dr : 0<(d:ℝ) := by exact_mod_cast (show 0<d from (Finset.mem_Icc.mp hd).1)
  unfold term
  rw [pulse_positive (mul_pos dr (tp.trans_le tu)),pulse_positive (mul_pos dr tp)]
  exact mul_le_mul_of_nonneg_left (max_le_max_left _ (sub_le_sub_left
    (mul_le_mul_of_nonneg_left tu dr.le) 1)) ArithmeticFunction.vonMangoldt_nonneg

theorem integer_read {n : ℕ} (np : 0<n) : reading (1/(n:ℝ))=fullWalk n/n := by
  have nr : 0<(n:ℝ) := by exact_mod_cast np
  rw [finite_read (by positivity) n (by field_simp; norm_num),fullWalk,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d hd
  have dr : 0<(d:ℝ) := by exact_mod_cast (show 0<d from (Finset.mem_Icc.mp hd).1)
  have small : (d:ℝ)≤n := by exact_mod_cast (Finset.mem_Icc.mp hd).2
  rw [term,pulse_positive (mul_pos dr (by positivity)),mul_one_div,max_eq_right (sub_nonneg.mpr ((div_le_one nr).mpr small))]
  field_simp

def mainTerm (t : ℝ) : ℝ := (Set.Ioc (0:ℝ) 1).indicator (fun x => 1/(2*x)) t
def residual (t : ℝ) : ℂ := (reading t-mainTerm t:ℝ)

private theorem outside {t : ℝ} (h : t∉Set.Ioc (0:ℝ) 1) : residual t=0 := by
  have allzero (n : ℕ) : term n t=0 := by
    by_cases z : n=0
    · simp [term,z]
    have unit : (1:ℝ)≤n := by exact_mod_cast Nat.pos_of_ne_zero z
    by_cases p : 0<t
    · have far : 1<t := lt_of_not_ge (fun a => h ⟨p,a⟩)
      have a : 1≤(n:ℝ)*t := far.le.trans (le_mul_of_one_le_left p.le unit)
      simp [term,pulse_positive (mul_pos (zero_lt_one.trans_le unit) p),max_eq_left (sub_nonpos.mpr a)]
    · have neg : (n:ℝ)*t≤0 := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (le_of_not_gt p)
      have no : (n:ℝ)*t∉Set.Ioc (0:ℝ) 1 := fun hi => (not_lt_of_ge neg) hi.1
      simp [term,pulseR,no]
  simp [residual,reading,allzero,mainTerm,h]

private theorem residual_meas : Measurable residual := by
  have term_meas (n : ℕ) : Measurable (term n) := by
    unfold term pulseR
    exact measurable_const.mul (((measurable_const.sub measurable_id).indicator measurableSet_Ioc).comp
      (measurable_const.mul measurable_id))
  have m : Measurable reading := Measurable.tsum term_meas
  unfold residual mainTerm
  exact Complex.measurable_ofReal.comp (m.sub ((measurable_const.div (measurable_const.mul measurable_id)).indicator measurableSet_Ioc))

/-- The only interpolation gap between consecutive integer heads is absorbed by the square-root price. -/
theorem interpolation {C : ℝ} (cn : 0≤C) (cap : ∀ n : ℕ, 0<n →
    |fullWalk n-(n:ℝ)^2/2| ≤ C*n*Real.sqrt n) {t : ℝ} (ht : t∈Set.Ioc (0:ℝ) 1) :
    ‖residual t‖ ≤ (2*C+1)/Real.sqrt t := by
  let x:=1/t
  let n:=⌊x⌋₊
  have tp:=ht.1
  have xp : 0<x := by dsimp [x];positivity
  have xone : 1≤x := (one_le_div tp).mpr ht.2
  have np : 0<n := Nat.floor_pos.mpr xone
  have nr : 0<(n:ℝ) := by exact_mod_cast np
  have lower : (n:ℝ)≤x:=Nat.floor_le xp.le
  have upper : x<(n:ℝ)+1:=Nat.lt_floor_add_one _
  have xn : 1/x=t := by dsimp [x];simp
  have floorprice (k : ℕ) (kp : 0<k) : |reading (1/(k:ℝ))-(k:ℝ)/2| ≤ C*Real.sqrt k := by
    have kr : 0<(k:ℝ) := by exact_mod_cast kp
    rw [integer_read kp,show fullWalk k/k-(k:ℝ)/2=(fullWalk k-(k:ℝ)^2/2)/k by field_simp,
      abs_div,abs_of_pos kr]
    apply (div_le_iff₀ kr).mpr
    simpa [mul_assoc,mul_left_comm,mul_comm] using cap k kp
  have ll := decreasing (t:=1/x) (u:=1/(n:ℝ)) (by positivity) (one_div_le_one_div_of_le nr lower)
  have uu := decreasing (t:=1/((n:ℝ)+1)) (u:=1/x) (by positivity)
    (one_div_le_one_div_of_le xp upper.le)
  rw [xn] at ll uu
  have l := (abs_le.mp (floorprice n np)).1
  have u := (abs_le.mp (floorprice (n+1) (by omega))).2
  push_cast at u
  have loRoot:=Real.sqrt_le_sqrt lower
  have hiRoot : Real.sqrt ((n:ℝ)+1)≤2*Real.sqrt x := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    rw [mul_pow,Real.sq_sqrt xp.le]
    linarith
  have oneRoot:=Real.one_le_sqrt.mpr xone
  have root : Real.sqrt x=1/Real.sqrt t := by simp [x,one_div,Real.sqrt_inv]
  rw [residual,Complex.norm_real,Real.norm_eq_abs,mainTerm,Set.indicator_of_mem ht]
  have eqx : 1/(2*t)=x/2 := by dsimp [x];ring
  rw [eqx,show (2*C+1)/Real.sqrt t=(2*C+1)*Real.sqrt x by rw [root,mul_one_div]]
  apply abs_le.mpr
  constructor <;> nlinarith only [ll,uu,l,u,lower,upper.le,oneRoot,mul_le_mul_of_nonneg_left loRoot cn,
    mul_le_mul_of_nonneg_left hiRoot cn, mul_nonneg cn (Real.sqrt_nonneg x)]

private theorem analytic_residual {C : ℝ} (cn : 0≤C) (cap : ∀ n : ℕ, 0<n →
    |fullWalk n-(n:ℝ)^2/2| ≤ C*n*Real.sqrt n) {s : ℂ} (hs : 1/2<s.re) :
    DifferentiableAt ℂ (mellin residual) s ∧ MellinConvergent residual s := by
  let D:=2*C+1
  have dn : 0≤D := by dsimp [D];linarith
  have cost (x : ℝ) : ‖residual x‖≤D/Real.sqrt x := by
    by_cases h : x∈Set.Ioc (0:ℝ) 1
    · exact interpolation cn cap h
    · rw [outside h,norm_zero];positivity
  have ct : ContinuousOn (fun x : ℝ => D/Real.sqrt x) (Set.Ioi 0) :=
    continuousOn_const.div Real.continuous_sqrt.continuousOn (fun x hx => (Real.sqrt_pos_of_pos hx).ne')
  have loc : LocallyIntegrableOn residual (Set.Ioi 0) :=
    (ct.locallyIntegrableOn measurableSet_Ioi).mono residual_meas.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => (cost x).trans (le_abs_self _)))
  have top : residual =O[atTop] (fun x : ℝ => x^(-(s.re+1))) := by
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [eventually_gt_atTop (1:ℝ)] with x hx
    rw [outside (fun h => (not_le_of_gt hx) h.2),norm_zero];positivity
  have bot : residual =O[𝓝[>] (0:ℝ)] (fun x : ℝ => x^(-(1/2:ℝ))) := by
    apply Asymptotics.IsBigO.of_bound D
    filter_upwards [self_mem_nhdsWithin] with x (xp : 0<x)
    rw [Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos xp _),Real.rpow_neg xp.le,←Real.sqrt_eq_rpow]
    exact cost x
  exact ⟨mellin_differentiableAt_of_isBigO_rpow loc top (by linarith) bot hs,
    mellinConvergent_of_isBigO_rpow loc top (by linarith) bot hs⟩

private theorem principal {s : ℂ} (sr : 1<s.re) :
    HasMellin (fun t => (mainTerm t:ℂ)) s ((1/2)/(s-1)) := by
  have h:=hasMellin_cpow_Ioc (-1) (s:=s) (by simp;linarith)
  have a:=hasMellin_const_smul h.1 (1/2:ℂ)
  rw [h.2] at a
  have eq : (fun t => (1/2:ℂ) • (Set.Ioc (0:ℝ) 1).indicator (fun x => (x:ℂ)^(-1:ℂ)) t)=
      (fun t => (mainTerm t:ℂ)) := by
    funext t
    by_cases inside : t∈Set.Ioc (0:ℝ) 1 <;>
      simp [mainTerm,inside,Complex.cpow_neg,smul_eq_mul,div_eq_mul_inv,mul_inv_rev,mul_comm]
  rw [eq] at a
  have val : (1/2:ℂ) • (1/(s+(-1))) = (1/2)/(s-1) := by rw [smul_eq_mul];ring
  rwa [val] at a

/-- An arithmetic corridor on the actual finite prime-power sums supplies the analytic continuation. -/
theorem rh_of_full_walk {C : ℝ} (cn : 0≤C) (cap : ∀ n : ℕ, 0<n →
    |fullWalk n-(n:ℝ)^2/2| ≤ C*n*Real.sqrt n) : RiemannHypothesis := by
  let U:= {s : ℂ | 1/2<s.re}
  have op : IsOpen U := isOpen_lt continuous_const continuous_re
  let F:=mellin residual
  have fr : DifferentiableOn ℂ F U := fun s hs => (analytic_residual cn cap hs).1.differentiableWithinAt
  let Q:=fun s : ℂ => (s*(s+1))*DysonOctave.kernel (s-1/2)
  have qr : DifferentiableOn ℂ Q U := by
    intro s hs
    have pp : 0<(s-1/2).re := by change 1/2<s.re at hs;rw [sub_re];norm_num;linarith
    have nn : s-1/2≠0 := ne_zero_of_re_pos pp
    unfold Q DysonOctave.kernel DysonOctave.octave
    fun_prop (disch := first | exact nn | exact mul_ne_zero (Complex.exp_ne_zero _) (pow_ne_zero _ nn))
  have qu : U∈𝓝 (1:ℂ) := op.mem_nhds (by norm_num [U])
  have slopes : DifferentiableOn ℂ (fun z => (1/2:ℂ)*dslope Q 1 z) U :=
    ((Complex.differentiableOn_dslope qu).mpr qr).const_mul _
  apply DysonOctave.rh_of_centered_response (fun s => Q s*F s+(1/2)*dslope Q 1 s) ((qr.mul fr).add slopes)
  intro s (sr : 1<s.re)
  have hn : s≠1 := by rintro rfl;norm_num at sr
  have sn : s≠0 := ne_zero_of_re_pos (by linarith)
  have pn : s+1≠0 := ne_zero_of_re_pos (by rw [add_re,one_re];linarith)
  have fc:= (analytic_residual cn cap (show 1/2<s.re by linarith)).2
  have p:=principal sr
  have sum:=hasMellin_add fc p.1
  have eq : (fun t => residual t+(mainTerm t:ℂ))=(fun t => (reading t:ℂ)) := by
    funext t; simp [residual]
  rw [eq,p.2] at sum
  have value : F s=DysonOctave.primeSeries s/(s*(s+1))-(1/2)/(s-1) := by
    have q:=sum.2
    rw [arithmetic_transform sr] at q
    dsimp only [F]
    linear_combination -q
  rw [value,dslope_of_ne Q hn,slope_def_field]
  dsimp only [Q]
  rw [show (1:ℂ)-1/2=1/2 by norm_num]
  field_simp [sn,pn,sub_ne_zero.mpr hn]
  ring

#print axioms PALRH.LinearPrimeIntegral.arithmetic_transform
#print axioms PALRH.LinearPrimeIntegral.interpolation
#print axioms PALRH.LinearPrimeIntegral.rh_of_full_walk
end PALRH.LinearPrimeIntegral
