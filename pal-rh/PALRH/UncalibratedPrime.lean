import PALRH.WeightedPrimePulse
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.RemovableSingularity

open Set Finset Filter MeasureTheory Complex
open scoped Topology BigOperators

noncomputable section
namespace PALRH.UncalibratedPrime
open DysonOctave

private def unitWindow : ℝ → ℝ := (Set.Ioc (0:ℝ) 1).indicator (fun _ => 1)
private def read := WeightedPrimePulse.reading unitWindow
private def center (c : ℝ) := (Set.Ioc (0:ℝ) 1).indicator (fun t => c/t)
private def rem (c t : ℝ) : ℂ := (read t-center c t:ℝ)

private theorem window_nonneg (t : ℝ) : 0≤unitWindow t := by
  by_cases ht : t∈Set.Ioc (0:ℝ) 1 <;> simp [unitWindow,ht]

private theorem unit_transform {s : ℂ} (sp : 0<s.re) :
    HasMellin (fun t => (unitWindow t:ℂ)) s (1/s) := by
  have eq : (fun t => (unitWindow t:ℂ))=(Set.Ioc (0:ℝ) 1).indicator (fun _ => (1:ℂ)) := by
    funext t
    by_cases ht : t∈Set.Ioc (0:ℝ) 1 <;> simp [unitWindow,ht]
  rw [eq]
  exact hasMellin_one_Ioc sp

private theorem read_exact {t : ℝ} (tp : 0<t) : read t=Chebyshev.psi (1/t) := by
  let x:=1/t
  have xp : 0<x := one_div_pos.mpr tp
  have xt : x*t=1 := by dsimp [x];simp [one_div,tp.ne']
  have finite : read t=∑ d ∈ Finset.Ioc 0 ⌊x⌋₊, WeightedPrimePulse.term unitWindow d t := by
    unfold read WeightedPrimePulse.reading
    apply tsum_eq_sum
    intro d out
    by_cases zero : d=0
    · simp [zero,WeightedPrimePulse.term]
    have dp:=Nat.pos_of_ne_zero zero
    have late : x<(d:ℝ) := (Nat.floor_lt xp.le).mp (lt_of_not_ge (fun q => out (Finset.mem_Ioc.mpr ⟨dp,q⟩)))
    have high:=mul_lt_mul_of_pos_right late tp
    rw [xt] at high
    have no : (d:ℝ)*t∉Set.Ioc (0:ℝ) 1 := fun h => (not_le_of_gt high) h.2
    simp [WeightedPrimePulse.term,unitWindow,no]
  rw [finite,Chebyshev.psi]
  apply Finset.sum_congr rfl
  intro d hd
  have dp : 0<(d:ℝ) := by exact_mod_cast (Finset.mem_Ioc.mp hd).1
  have low := (Nat.le_floor_iff xp.le).mp (Finset.mem_Ioc.mp hd).2
  have stop:=mul_le_mul_of_nonneg_right low tp.le
  rw [xt] at stop
  simp [WeightedPrimePulse.term,unitWindow,Set.indicator_of_mem
    (show (d:ℝ)*t∈Set.Ioc (0:ℝ) 1 from ⟨mul_pos dp tp,stop⟩)]

private theorem rem_meas (c : ℝ) : Measurable (rem c) := by
  have w : Measurable unitWindow := measurable_const.indicator measurableSet_Ioc
  have r : Measurable read := Measurable.tsum (fun n => measurable_const.mul
    (w.comp (measurable_const.mul measurable_id)))
  exact Complex.measurable_ofReal.comp (r.sub ((measurable_const.div measurable_id).indicator measurableSet_Ioc))

private theorem rem_outside (c : ℝ) {t : ℝ} (ht : t∉Set.Ioc (0:ℝ) 1) : rem c t=0 := by
  have empty (n : ℕ) : WeightedPrimePulse.term unitWindow n t=0 := by
    by_cases nz : n=0
    · simp [nz,WeightedPrimePulse.term]
    have one : (1:ℝ)≤n := by exact_mod_cast Nat.pos_of_ne_zero nz
    have no : (n:ℝ)*t∉Set.Ioc (0:ℝ) 1 := by
      intro h
      have tp:=pos_of_mul_pos_right h.1 (Nat.cast_nonneg n)
      exact ht ⟨tp,(le_mul_of_one_le_left tp.le one).trans h.2⟩
    simp [WeightedPrimePulse.term,unitWindow,no]
  simp [rem,read,WeightedPrimePulse.reading,empty,center,ht]

private theorem center_transform (c : ℝ) {s : ℂ} (sr : 1<s.re) :
    HasMellin (fun t => (center c t:ℂ)) s (c/(s-1)) := by
  have p:=hasMellin_cpow_Ioc (-1) (s:=s) (by simp;linarith)
  have m:=hasMellin_const_smul p.1 (c:ℂ)
  rw [p.2] at m
  have eq : (fun t : ℝ => (c:ℂ) • (Set.Ioc (0:ℝ) 1).indicator (fun u => (u:ℂ)^(-1:ℂ)) t) =
      fun t => (center c t:ℂ) := by
    funext t
    by_cases ht : t∈Set.Ioc (0:ℝ) 1 <;> simp [center,ht,Complex.cpow_neg,div_eq_mul_inv]
  rw [eq] at m
  rw [show (s+(-1):ℂ)=s-1 by ring] at m
  simpa [smul_eq_mul,div_eq_mul_inv] using m

/-- The reference slope is supplied as an unknown real number. Continuation fixes it to one
and excludes off-line zeros from ordinary prime-power shape data. -/
theorem from_unknown_slope (c : ℝ)
    (close : ∀ b : ℝ, 1/2<b → ∃ D : ℝ, 0≤D ∧ ∀ y : ℝ, 1≤y → |Chebyshev.psi y-c*y|≤D*y^b) :
    c=1 ∧ RiemannHypothesis := by
  let U:={s : ℂ | 1/2<s.re}
  have op : IsOpen U := isOpen_lt continuous_const continuous_re
  let F:=mellin (rem c)
  have smooth {s : ℂ} (hs : 1/2<s.re) :
      DifferentiableAt ℂ F s ∧ MellinConvergent (rem c) s := by
    obtain ⟨b,bh,bs⟩:=exists_between hs
    obtain ⟨D,dn,pay⟩:=close b bh
    apply WeightedPrimePulse.power_extension (rem c) (rem_meas c) (rem_outside c) (b:=b) dn _ bs
    intro t ht
    have a:=pay (1/t) ((one_le_div ht.1).mpr ht.2)
    rw [one_div,Real.inv_rpow ht.1.le,←Real.rpow_neg ht.1.le] at a
    rw [rem,Complex.norm_real,Real.norm_eq_abs,read_exact ht.1,center,Set.indicator_of_mem ht]
    simpa only [one_div,div_eq_mul_inv,one_mul] using a
  let Q:=fun s : ℂ => s*kernel (s-1/2)
  have qr : DifferentiableOn ℂ Q U := by
    intro s hs
    have pp : 0<(s-1/2).re := by change 1/2<s.re at hs;rw [sub_re];norm_num;linarith
    have nz:=ne_zero_of_re_pos pp
    unfold Q kernel octave
    fun_prop (disch := first | exact nz | exact mul_ne_zero (Complex.exp_ne_zero _) (pow_ne_zero _ nz))
  have fr : DifferentiableOn ℂ F U := fun s hs => (smooth hs).1.differentiableWithinAt
  have slope:= (Complex.differentiableOn_dslope
    (op.mem_nhds (show (1:ℂ)∈U by norm_num [U]))).mpr qr
  have both:=calibrate_response ((c:ℂ)*kernel (1/2))
    (fun s => Q s*F s+(c:ℂ)*dslope Q 1 s) ((qr.mul fr).add (slope.const_mul _)) (by
      intro s sr
      have sn:=ne_zero_of_re_pos (show 0<s.re by linarith)
      have un : s≠1 := by rintro rfl;norm_num at sr
      have body:=WeightedPrimePulse.arithmetic_transform unitWindow (fun z => 1/z)
        window_nonneg (fun h => unit_transform h) sr
      have centerM:=center_transform c sr
      have agg:=hasMellin_add (smooth (show 1/2<s.re by linarith)).2 centerM.1
      have eq : (fun t => rem c t+(center c t:ℂ))=(fun t => (read t:ℂ)) := by funext t;simp [rem]
      rw [eq,centerM.2] at agg
      have val : F s=1/s*primeSeries s-c/(s-1) := by
        change mellin (fun t => (read t:ℂ)) s=_ at body
        rw [←body,agg.2];ring
      rw [val,dslope_of_ne Q un,slope_def_field]
      dsimp only [Q]
      rw [show (1:ℂ)-1/2=1/2 by norm_num]
      field_simp [sn,sub_ne_zero.mpr un]
      ring)
  have nz : kernel (1/2) ≠ 0 := kernel_ne_zero (by norm_num)
  have cc : (c:ℂ)=1 := mul_right_cancel₀ nz (both.1.trans (one_mul _).symm)
  exact ⟨by exact_mod_cast cc,both.2⟩

theorem from_unknown_theta (c : ℝ)
    (close : ∀ b : ℝ, 1/2<b → ∃ D : ℝ, 0≤D ∧ ∀ y : ℝ, 1≤y → |Chebyshev.theta y-c*y|≤D*y^b) :
    c=1 ∧ RiemannHypothesis := by
  apply from_unknown_slope c
  obtain ⟨K,rep⟩:=Chebyshev.psi_sub_theta_le_mul_sqrt
  intro b bh
  obtain ⟨D,dn,priced⟩:=close b bh
  refine ⟨D+max 0 K,by positivity,?_⟩
  intro y large
  have err:=rep y
  have root : Real.sqrt y≤y^b := by
    rw [Real.sqrt_eq_rpow];exact Real.rpow_le_rpow_of_exponent_le large bh.le
  have pos:=(Chebyshev.theta_le_psi y)
  have k:=mul_le_mul (le_max_right (0:ℝ) K) root (Real.sqrt_nonneg _) (le_max_left _ _)
  calc
    _ = |(Chebyshev.psi y-Chebyshev.theta y)+(Chebyshev.theta y-c*y)| := by ring_nf
    _ ≤ _ := abs_add_le _ _
    _ ≤ _ := by rw [abs_of_nonneg (sub_nonneg.mpr pos)];nlinarith only [err,k,priced y large]

#print axioms PALRH.UncalibratedPrime.from_unknown_theta
end PALRH.UncalibratedPrime
