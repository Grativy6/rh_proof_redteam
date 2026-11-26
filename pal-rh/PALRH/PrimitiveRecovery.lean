import PALRH.LogPrimitive
import PALRH.PrimitiveMellin

open Finset MeasureTheory
open scoped BigOperators Interval

noncomputable section
namespace PALRH.PrimitiveRecovery
open LogPrimitive PositivePrimitive PrimeDivisorPrimitive

private theorem root_integrable {a b : ℝ} (an : 0≤a) (ab : a≤b) :
    IntervalIntegrable (fun t : ℝ => 1/Real.sqrt t) volume a b := by
  apply IntervalIntegrable.congr _ (intervalIntegral.intervalIntegrable_rpow' (a:=a) (b:=b)
    (r:=-(1/2:ℝ)) (by norm_num))
  intro t ht
  rw [Set.uIoc_of_le ab] at ht
  change t^(-(1/2:ℝ))=1/Real.sqrt t
  rw [Real.rpow_neg (an.trans ht.1.le),←Real.sqrt_eq_rpow,one_div]

private theorem root_integral {a b : ℝ} (an : 0≤a) (ab : a≤b) :
    (∫ t in a..b,1/Real.sqrt t)=2*(Real.sqrt b-Real.sqrt a) := by
  calc
    _ = ∫ t in a..b,t^(-(1/2:ℝ)) := intervalIntegral.integral_congr (fun t ht => by
      rw [Set.uIcc_of_le ab] at ht
      rw [Real.rpow_neg (an.trans ht.1),←Real.sqrt_eq_rpow,one_div])
    _ = _ := by
      rw [integral_rpow (Or.inl (by norm_num : (-1:ℝ)< -(1/2:ℝ))),
        show -(1/2:ℝ)+1=1/2 by norm_num,←Real.sqrt_eq_rpow,←Real.sqrt_eq_rpow]
      ring

private theorem root_div {t : ℝ} (tp : 0<t) : Real.sqrt t/t=1/Real.sqrt t := by
  apply (div_eq_div_iff tp.ne' (Real.sqrt_pos_of_pos tp).ne').mpr
  simpa [pow_two] using Real.sq_sqrt tp.le

theorem primitive_early {x : ℝ} (xp : 0≤x) (small : x<1) : primitive x=0 := by
  unfold primitive
  calc
    _ = ∫ _ in (0:ℝ)..x,(0:ℝ) := intervalIntegral.integral_congr (fun t ht => by
      rw [Set.uIcc_of_le xp] at ht
      simp [density,value_early (ht.2.trans_lt small)])
    _ = _ := by simp

private theorem primitive_increment {C : ℝ} (cn : 0≤C) (upper : ∀ x : ℝ, 1≤x → value x≤C*Real.sqrt x)
    {x y : ℝ} (yp : 0≤y) (xy : y≤x) :
    primitive x-primitive y≤(2*C)*(Real.sqrt x-Real.sqrt y) := by
  have a:=density_int yp xy
  have z:=density_int (a:=0) le_rfl yp
  unfold primitive
  rw [←intervalIntegral.integral_add_adjacent_intervals z a]
  have b:=(root_integrable yp xy).const_mul C
  have bound:=intervalIntegral.integral_mono_on xy a b (fun t ht => by
    have tn:=yp.trans ht.1
    by_cases tz : t=0
    · simp [density,tz]
    have tp:=lt_of_le_of_ne tn (Ne.symm tz)
    have paid : value t≤C*Real.sqrt t := by
      by_cases large : 1≤t
      · exact upper t large
      · rw [value_early (lt_of_not_ge large)];positivity
    unfold density
    calc
      _ ≤ (C*Real.sqrt t)/t := div_le_div_of_nonneg_right paid tn
      _ = _ := by rw [mul_div_assoc,root_div tp])
  rw [intervalIntegral.integral_const_mul,root_integral yp xy] at bound
  linarith only [bound]

private def scale (r t : ℝ) := (1/r)*density (t/r)

private theorem scale_eq (t : ℝ) {r : ℝ} (rp : 0<r) : scale r t=value (t/r)/t := by
  unfold scale density
  by_cases z : t=0
  · simp [z]
  · field_simp

private theorem scale_int {r x : ℝ} (rp : 0<r) (xp : 0≤x) :
    IntervalIntegrable (scale r) volume 0 x := by
  have h:= (density_int (a:=0) le_rfl (div_nonneg xp rp.le)).comp_mul_right (c:=r⁻¹)
  have inv : (x/r)/r⁻¹=x := by field_simp
  rw [zero_div,inv] at h
  change IntervalIntegrable (fun t : ℝ => (1/r)*density (t/r)) volume 0 x
  simpa only [div_eq_mul_inv] using h.const_mul (1/r)

private theorem scale_value {r : ℝ} (rp : 0<r) (x : ℝ) :
    (∫ t in (0:ℝ)..x,scale r t)=primitive (x/r) := by
  unfold scale primitive
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_comp_div density rp.ne',zero_div,
    smul_eq_mul]
  field_simp

private def pair (j : ℕ) (t : ℝ) := scale (2*j+1) t-scale (2*j+2) t

private theorem pair_int (j : ℕ) {x : ℝ} (xp : 0≤x) : IntervalIntegrable (pair j) volume 0 x :=
  (scale_int (r:=2*j+1) (by positivity) xp).sub (scale_int (r:=2*j+2) (by positivity) xp)

private theorem pair_sum (N : ℕ) (t : ℝ) :
    (∑ j ∈ range N,pair j t)=alternating value N t/t := by
  unfold alternating
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  rw [pair,scale_eq _ (by positivity),scale_eq _ (by positivity),sub_div]

private theorem pair_value (N : ℕ) {x : ℝ} (xp : 0≤x) :
    (∫ t in (0:ℝ)..x,∑ j ∈ range N,pair j t)=alternating primitive N x := by
  rw [intervalIntegral.integral_finsetSum (fun j (_ : j∈range N) => pair_int j xp)]
  unfold alternating
  apply Finset.sum_congr rfl
  intro j _
  unfold pair
  rw [intervalIntegral.integral_sub (scale_int (by positivity) xp) (scale_int (by positivity) xp),
    scale_value (by positivity),scale_value (by positivity)]

private theorem all_early {t : ℝ} (tn : 0≤t) (small : t<1) (N : ℕ) : alternating value N t=0 := by
  unfold alternating
  apply Finset.sum_eq_zero
  intro j _
  have a := (div_le_self tn (by have := Nat.cast_nonneg (α:=ℝ) j;linarith : 1≤2*(j:ℝ)+1)).trans_lt small
  have b := (div_le_self tn (by have := Nat.cast_nonneg (α:=ℝ) j;linarith : 1≤2*(j:ℝ)+2)).trans_lt small
  simp [value_early a,value_early b]

theorem observed_primitive {x : ℝ} (xp : 0≤x) {N : ℕ} (paid : ⌊x⌋₊≤2*N) :
    -(24*Real.sqrt x)≤alternating primitive N x := by
  have sum_int:=IntervalIntegrable.sum (range N) (fun j _ => pair_int j xp)
  have point : (∑ j ∈ range N,pair j)=(fun t => ∑ j ∈ range N,pair j t) := by funext t;simp
  rw [point] at sum_int
  have root_int:=(root_integrable (a:=0) le_rfl xp).const_mul (-12)
  have bound:=intervalIntegral.integral_mono_on xp root_int
    sum_int
    (fun t ht => by
      rw [pair_sum]
      by_cases zero : t=0
      · simp [zero]
      have tp : 0<t := lt_of_le_of_ne ht.1 (Ne.symm zero)
      have h : -(12*Real.sqrt t)≤alternating value N t := by
        by_cases large : 1≤t
        · exact arithmetic_lower large ((Nat.floor_mono ht.2).trans paid)
        · rw [all_early tp.le (lt_of_not_ge large)];linarith only [Real.sqrt_nonneg t]
      calc
        _ = -(12*Real.sqrt t)/t := by rw [neg_div,mul_div_assoc,root_div tp];ring
        _ ≤ _ := div_le_div_of_nonneg_right h tp.le)
  rw [pair_value N xp,intervalIntegral.integral_const_mul,root_integral le_rfl xp,Real.sqrt_zero,sub_zero] at bound
  linarith only [bound]

/-- On the same dilation list the upper orientation has the same elementary log cost. -/
theorem observed_primitive_upper {x : ℝ} (xp : 0≤x) {N : ℕ} (paid : ⌊x⌋₊≤2*N) :
    alternating primitive N x≤24*Real.sqrt x := by
  have sum_int:=IntervalIntegrable.sum (range N) (fun j _ => pair_int j xp)
  have point : (∑ j ∈ range N,pair j)=(fun t => ∑ j ∈ range N,pair j t) := by funext t;simp
  rw [point] at sum_int
  have root_int:=(root_integrable (a:=0) le_rfl xp).const_mul 12
  have bound:=intervalIntegral.integral_mono_on xp sum_int root_int (fun t ht => by
    rw [pair_sum]
    by_cases zero : t=0
    · simp [zero]
    have tp : 0<t := lt_of_le_of_ne ht.1 (Ne.symm zero)
    have h : alternating value N t≤12*Real.sqrt t := by
      by_cases large : 1≤t
      · exact arithmetic_upper large ((Nat.floor_mono ht.2).trans paid)
      · rw [all_early tp.le (lt_of_not_ge large)];positivity
    calc
      _ ≤ (12*Real.sqrt t)/t := div_le_div_of_nonneg_right h tp.le
      _ = _ := by rw [mul_div_assoc,root_div tp])
  rw [pair_value N xp,intervalIntegral.integral_const_mul,root_integral le_rfl xp,Real.sqrt_zero,sub_zero] at bound
  linarith only [bound]

theorem primitive_bound {C : ℝ} (cn : 0≤C) (upper : ∀ x : ℝ, 1≤x → value x≤C*Real.sqrt x)
    {x : ℝ} (xp : 0≤x) : |primitive x|≤4*(2*C+24)*Real.sqrt x := by
  apply signed_recovery (D:=2*C) (K:=24) (by positivity) (by norm_num)
    (fun _ => primitive_early) (fun _ _ => primitive_increment cn upper) _ xp
  intro t large
  exact ⟨⌊t⌋₊+1,by omega,observed_primitive (zero_le_one.trans large) (by omega)⟩

end PALRH.PrimitiveRecovery
