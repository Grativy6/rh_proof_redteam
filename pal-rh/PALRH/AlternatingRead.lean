import PALRH.RectangleBalance
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open Finset Filter Set MeasureTheory Complex
open scoped Topology BigOperators
noncomputable section
namespace PALRH.AlternatingRead

def digit (n : ℕ) : ℂ := (n%2:ℕ)
def jump (n : ℕ) : ℂ := digit n-digit (n-1)
def parity (x : ℝ) : ℂ := digit ⌊x⌋₊

private theorem digit_sum (n : ℕ) : ∑ k ∈ Finset.Icc 0 n, jump k=digit n := by
  induction n with
  | zero => simp [jump,digit]
  | succ n old =>
    rw [Finset.sum_Icc_succ_top (by omega),old,jump,Nat.add_sub_cancel]
    ring

private theorem digit_cap (n : ℕ) : ‖digit n‖≤1 := by
  rw [digit,Complex.norm_natCast]
  exact_mod_cast (show n%2≤1 by omega)

private theorem parity_meas : Measurable parity :=
  (measurable_of_countable digit).comp Nat.measurable_floor

def density (s : ℂ) (x : ℝ) := (x:ℂ)^(-s-1)*parity x

private theorem density_bound (s : ℂ) {x : ℝ} (xp : 0<x) :
    ‖density s x‖≤x^(-s.re-1) := by
  rw [density,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos xp]
  simp only [sub_re,neg_re,one_re]
  exact (mul_le_mul_of_nonneg_left (digit_cap _) (Real.rpow_nonneg xp.le _)).trans_eq (mul_one _)

private theorem density_int {s : ℂ} (sp : 0<s.re) {a : ℝ} (ap : 0<a) :
    IntegrableOn (density s) (Ioi a) := by
  apply (integrableOn_Ioi_rpow_of_lt (a:=-s.re-1) (by linarith) ap).mono'
  · apply AEStronglyMeasurable.mul _ parity_meas.aestronglyMeasurable
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    exact continuousOn_of_forall_continuousAt (fun t ht =>
      Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr (ap.trans ht).ne'))
  · filter_upwards [ae_restrict_mem (μ:=volume) (measurableSet_Ioi (a:=a))] with x hx
    exact density_bound _ (ap.trans hx)

private theorem whole_zero {s : ℂ} (sp : 0<s.re) (except : s≠1) (zero : riemannZeta s=0) :
    (∫ x in Ioi (1:ℝ), density s x)=0 := by
  have f : (fun x : ℝ => parity x⁻¹) = fun x => (2:ℂ) • sensor 2 x := by
    funext x
    dsimp [parity,digit,sensor,smul_eq_mul]
    ring
  have m : mellin parity (-s)=0 := by
    rw [←mellin_comp_inv,f,mellin_const_smul,mellin_sensor_zero sp except zero (by decide : 0<2),smul_zero]
  change (∫ x in Ioi (0:ℝ), density s x)=0 at m
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (Ici_subset_Ioi.mpr (zero_lt_one : (0:ℝ)<1)) (f:=density s) (by
      intro x hx
      have lt : x<1 := lt_of_not_ge hx.2
      simp [density,parity,digit,Nat.floor_eq_zero.mpr lt]),integral_Ici_eq_integral_Ioi] at m
  exact m

private theorem tail_bound {s : ℂ} (sp : 0<s.re) {v : ℝ} (vp : 0<v) :
    ‖∫ x in Ioi v, density s x‖≤v^(-s.re)/s.re := by
  apply (norm_integral_le_integral_norm _).trans
  have b := setIntegral_mono_on (density_int sp vp).norm
    (integrableOn_Ioi_rpow_of_lt (a:=-s.re-1) (by linarith) vp) measurableSet_Ioi
    (fun x hx => density_bound _ (vp.trans hx))
  apply b.trans_eq
  rw [integral_Ioi_rpow_of_lt (by linarith : -s.re-1 < -1) vp]
  rw [show -s.re-1+1= -s.re by ring]
  ring

def alternating (s : ℂ) (v : ℝ) :=
  ∑ n ∈ Finset.Icc 0 ⌊v⌋₊, (n:ℂ)^(-s)*jump n

private theorem abel {s : ℂ} (sp : 0<s.re) {v : ℝ} (_hv : 1≤v) :
    alternating s v=(v:ℂ)^(-s)*parity v+s*(∫ x in Set.Ioc 1 v, density s x) := by
  let f := fun t : ℝ => (t:ℂ)^(-s)
  have derivs {t : ℝ} (pos : 0<t) : HasDerivAt f ((-s)*(t:ℂ)^(-s-1)) t :=
    hasDerivAt_ofReal_cpow_const pos.ne' (neg_ne_zero.mpr (ne_zero_of_re_pos sp))
  have continuous : ContinuousOn (fun t : ℝ => (-s)*(t:ℂ)^(-s-1)) (Set.Icc 1 v) := by
    apply continuousOn_const.mul
    exact continuousOn_of_forall_continuousAt (fun x hx => continuousAt_ofReal_cpow_const _ _
      (Or.inr (zero_lt_one.trans_le hx.1).ne'))
  have int : IntegrableOn (deriv f) (Set.Icc 1 v) := by
    exact (integrableOn_congr_fun (fun x hx => (derivs (zero_lt_one.trans_le hx.1)).deriv) measurableSet_Icc).mpr
      (continuous.integrableOn_compact isCompact_Icc)
  have a := sum_mul_eq_sub_integral_mul₀ jump (show jump 0=0 by simp [jump,digit]) v
    (f:=f) (fun t ht => (derivs (zero_lt_one.trans_le ht.1)).differentiableAt) int
  simp only [digit_sum] at a
  have eq : (∫ t in Set.Ioc 1 v, deriv f t*digit ⌊t⌋₊) =
      (-s)*(∫ t in Set.Ioc 1 v, density s t) := by
    rw [←integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    change deriv f t*digit ⌊t⌋₊=(-s)*density s t
    rw [(derivs (zero_lt_one.trans ht.1)).deriv,density,parity,mul_assoc]
  rw [eq] at a
  change _=(v:ℂ)^(-s)*digit ⌊v⌋₊+_
  exact a.trans (by dsimp [f];ring)

def response (s : ℂ) (v : ℝ) := (v:ℂ)^s*alternating s v

/-- At an actual zeta zero this finite reader is bounded independently of its cutoff. -/
theorem bounded_at_zero {s : ℂ} (sp : 0<s.re) (except : s≠1) (zero : riemannZeta s=0)
    {v : ℝ} (hv : 1≤v) : ‖response s v‖≤1+‖s‖/s.re := by
  have vp := zero_lt_one.trans_le hv
  have split : (∫ x in Set.Ioc 1 v, density s x)= -(∫ x in Ioi v, density s x) := by
    have sum := setIntegral_union (f:=density s) (μ:=volume)
      (Set.disjoint_left.mpr (fun x (hx : x∈Set.Ioc 1 v) (hy : x∈Set.Ioi v) => (not_lt_of_ge hx.2) hy))
      measurableSet_Ioi ((density_int sp zero_lt_one).mono_set (fun _ hx => hx.1)) (density_int sp vp)
    rw [Set.Ioc_union_Ioi_eq_Ioi hv,whole_zero sp except zero] at sum
    exact eq_neg_of_add_eq_zero_left sum.symm
  have id : response s v=parity v-(v:ℂ)^s*s*(∫ x in Ioi v, density s x) := by
    rw [response,abel sp hv,split,Complex.cpow_neg]
    have non : (v:ℂ)^s≠0 := by
      rw [Ne,Complex.cpow_eq_zero_iff,not_and_or]
      exact Or.inl (ofReal_ne_zero.mpr vp.ne')
    field_simp
    ring
  rw [id]
  apply (norm_sub_le _ _).trans
  apply add_le_add (digit_cap _) _
  rw [norm_mul,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos vp]
  have c := mul_le_mul_of_nonneg_left (tail_bound sp vp)
    (mul_nonneg (Real.rpow_nonneg vp.le s.re) (norm_nonneg s))
  apply c.trans_eq
  rw [Real.rpow_neg vp.le]
  field_simp [(Real.rpow_pos_of_pos vp s.re).ne',sp.ne']

#print axioms PALRH.AlternatingRead.bounded_at_zero

/-- The positive dyadic pulse obtained by evaluating the true rough census at two scales. -/
def pulse (x : ℝ) : ℝ := RectangleBalance.taper (1/x)-RectangleBalance.taper (2/x)

theorem pulse_first {x : ℝ} (lo : 1/2≤x) (hi : x≤1) : pulse x=2-1/x := by
  have pos : 0<x := by linarith
  have a : 1≤1/x := (le_div_iff₀ pos).mpr (by linarith)
  have b : 1/x≤2 := (div_le_iff₀ pos).mpr (by linarith)
  have c : 2≤2/x := (le_div_iff₀ pos).mpr (by linarith)
  simp only [pulse,RectangleBalance.taper,min_eq_right (by linarith : 2-1/x≤1),
    min_eq_right (by linarith : 2-2/x≤1),max_eq_right (by linarith : 0≤2-1/x),
    max_eq_left (by linarith : 2-2/x≤0),sub_zero]

theorem pulse_last {x : ℝ} (lo : 1≤x) (hi : x≤2) : pulse x=2/x-1 := by
  have pos : 0<x := by linarith
  have a : 1/x≤1 := (div_le_iff₀ pos).mpr (by linarith)
  have b : 2/x≤2 := (div_le_iff₀ pos).mpr (by linarith)
  have c : 1≤2/x := (le_div_iff₀ pos).mpr (by linarith)
  simp only [pulse,RectangleBalance.taper,min_eq_left (by linarith : 1≤2-1/x),
    max_eq_right (by norm_num : (0:ℝ)≤1),min_eq_right (by linarith : 2-2/x≤1),
    max_eq_right (by linarith : 0≤2-2/x)]
  ring

def moment (s : ℂ) := ∫ x : ℝ in (1/2:ℝ)..2, (x:ℂ)^(-s)*(pulse x:ℂ)

private lemma power_int {a b : ℝ} (ap : 0<a) (ab : a≤b) (s : ℂ) :
    IntervalIntegrable (fun x : ℝ => (x:ℂ)^s) volume a b :=
  (continuousOn_of_forall_continuousAt (fun _ (hx : _∈Set.Icc a b) => continuousAt_ofReal_cpow_const _ _
    (Or.inr (ap.trans_le hx.1).ne'))).intervalIntegrable_of_Icc ab

private lemma pulse_int {a b : ℝ} (ap : 0<a) (ab : a≤b) (s : ℂ) :
    IntervalIntegrable (fun x : ℝ => (x:ℂ)^(-s)*(pulse x:ℂ)) volume a b := by
  apply ContinuousOn.intervalIntegrable_of_Icc ab
  apply ContinuousOn.mul
  · exact continuousOn_of_forall_continuousAt (fun _ hx => continuousAt_ofReal_cpow_const _ _
      (Or.inr (ap.trans_le hx.1).ne'))
  apply continuous_ofReal.comp_continuousOn
  unfold pulse
  apply ContinuousOn.sub
  all_goals
    apply RectangleBalance.taper_continuous.comp_continuousOn
    exact continuousOn_const.div continuousOn_id (fun _ hx => (ap.trans_le hx.1).ne')

private lemma power_value {a b : ℝ} (ap : 0<a) (ab : a≤b) {s : ℂ} (except : s≠ -1) :
    (∫ x : ℝ in a..b, (x:ℂ)^s)=((b:ℂ)^(s+1)-(a:ℂ)^(s+1))/(s+1) := by
  apply integral_cpow (Or.inr ⟨except,?_⟩)
  rw [Set.uIcc_of_le ab]
  exact fun h => (not_le_of_gt ap) h.1

theorem pulse_value {s : ℂ} (sp : 0<s.re) (below : s.re<1) :
    moment s = ((2:ℂ)^s-1)*(2/(2:ℂ)^s-1)/(s*(1-s)) := by
  let f := fun x : ℝ => (x:ℂ)^(-s)
  let g := fun x : ℝ => (x:ℂ)^(-s-1)
  have hs : s≠0 := ne_zero_of_re_pos sp
  have h1 : s≠1 := by rintro rfl;norm_num at below
  have e (x : ℝ) (xp : 0<x) : g x=f x/(x:ℂ) := by
    dsimp only [f,g];rw [Complex.cpow_sub _ _ (ofReal_ne_zero.mpr xp.ne'),Complex.cpow_one]
  have first : (∫ x : ℝ in (1/2:ℝ)..1, (x:ℂ)^(-s)*(pulse x:ℂ))=
      2*(∫ x : ℝ in (1/2:ℝ)..1, f x)-(∫ x : ℝ in (1/2:ℝ)..1, g x) := by
    rw [←intervalIntegral.integral_const_mul,←intervalIntegral.integral_sub
      ((power_int (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)≤1) (-s)).const_mul _)
      (power_int (by norm_num) (by norm_num) _)]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (1/2:ℝ)≤1)] at hx
    change f x*(pulse x:ℂ)=2*f x-g x
    rw [pulse_first hx.1 hx.2,e x (by linarith [hx.1])]
    push_cast;ring
  have last : (∫ x : ℝ in (1:ℝ)..2, (x:ℂ)^(-s)*(pulse x:ℂ))=
      2*(∫ x : ℝ in (1:ℝ)..2, g x)-(∫ x : ℝ in (1:ℝ)..2, f x) := by
    rw [←intervalIntegral.integral_const_mul,←intervalIntegral.integral_sub
      ((power_int (by norm_num : (0:ℝ)<1) (by norm_num : (1:ℝ)≤2) (-s-1)).const_mul _)
      (power_int (by norm_num) (by norm_num) _)]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (1:ℝ)≤2)] at hx
    change f x*(pulse x:ℂ)=2*g x-f x
    rw [pulse_last hx.1 hx.2,e x (by linarith [hx.1])]
    push_cast;ring
  rw [moment,←intervalIntegral.integral_add_adjacent_intervals (b:=1)
    (pulse_int (by norm_num) (by norm_num) s) (pulse_int (by norm_num) (by norm_num) s),first,last]
  dsimp only [f,g]
  have ex1 : -s≠ -1 := fun h => h1 (neg_inj.mp h)
  have ex0 : -s-1≠ -1 := by intro h;apply hs;linear_combination -h
  rw [power_value (by norm_num) (by norm_num) ex1,power_value (by norm_num) (by norm_num) ex0,
    power_value (by norm_num) (by norm_num) ex0,power_value (by norm_num) (by norm_num) ex1]
  have inv (z : ℂ) : ((1/2:ℝ):ℂ)^z=((2:ℂ)^z)⁻¹ := by
    have h := Complex.inv_cpow_ofReal_nonneg (by norm_num : (0:ℝ)≤2) z
    norm_num at h ⊢
    exact h
  simp only [inv,show -s-1+1= -s by ring,show -s+1=1-s by ring,
    Complex.ofReal_one,Complex.ofReal_ofNat,Complex.one_cpow,Complex.cpow_neg,
    Complex.cpow_sub 1 s (by norm_num : (2:ℂ)≠0),Complex.cpow_one]
  have nn : (2:ℂ)^s≠0 := by rw [Ne,Complex.cpow_eq_zero_iff];norm_num
  field_simp [nn,hs,sub_ne_zero.mpr h1.symm]
  ring

theorem pulse_ne_zero {s : ℂ} (sp : 0<s.re) (below : s.re<1) : moment s≠0 := by
  have norm : ‖(2:ℂ)^s‖=(2:ℝ)^s.re := Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0:ℝ)<2) s
  have lo : 1<(2:ℝ)^s.re := Real.one_lt_rpow (by norm_num) sp
  have hi : (2:ℝ)^s.re<2 := by
    simpa using Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ)<2) below
  have one : (2:ℂ)^s≠1 := by intro h;rw [h,norm_one] at norm;linarith
  have two : (2:ℂ)^s≠2 := by intro h;rw [h] at norm;norm_num at norm;linarith
  have nz : (2:ℂ)^s≠0 := by intro h;rw [h,norm_zero] at norm;linarith
  rw [pulse_value sp below]
  apply div_ne_zero (mul_ne_zero (sub_ne_zero.mpr one) _) (mul_ne_zero (ne_zero_of_re_pos sp) _)
  · apply sub_ne_zero.mpr
    intro h
    exact two (by rw [div_eq_iff nz,one_mul] at h;exact h.symm)
  · apply sub_ne_zero.mpr;intro h;rw [←h] at below;norm_num at below

#print axioms PALRH.AlternatingRead.pulse_ne_zero

end PALRH.AlternatingRead
