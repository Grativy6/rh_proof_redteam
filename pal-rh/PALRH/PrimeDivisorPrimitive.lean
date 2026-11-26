import PALRH.PositivePrimitive
import PALRH.FactorialReturn
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.NumberTheory.Harmonic.Bounds

open Finset
open scoped BigOperators

noncomputable section
namespace PALRH.PrimeDivisorPrimitive
open PositivePrimitive

/-- The finite centered prime-power reading at a physical head. -/
def value (x : ℝ) : ℝ :=
  (∑ d ∈ Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt d*(1-d/x)) -
    if 1≤x then x/2 else 0

def allLogs (x : ℝ) : ℝ := ∑ d ∈ Icc 1 ⌊x⌋₊, (1-d/x)*Real.log d

def harmonicRow (m : ℕ) : ℝ := ∑ d ∈ Icc 1 m, 1/(d:ℝ)

def dilation (f : ℝ → ℝ) (M : ℕ) (x : ℝ) : ℝ := ∑ r ∈ Icc 1 M, f (x/r)

theorem value_early {x : ℝ} (early : x<1) : value x=0 := by
  simp [value,Nat.floor_eq_zero.mpr early,not_le.mpr early]

theorem divisor_read {x : ℝ} (xp : 0<x) :
    dilation value ⌊x⌋₊ x=allLogs x-x/2*harmonicRow ⌊x⌋₊ := by
  let N:=⌊x⌋₊
  have src:=(FactorialReturn.products N (fun _ => 1) (fun d => ArithmeticFunction.vonMangoldt d)
    (fun m => 1-(m:ℝ)/x))
  simp only [one_mul,mul_one,ArithmeticFunction.vonMangoldt_sum] at src
  have pieces {r : ℕ} (hr : r∈Icc 1 N) :
      value (x/r)= (∑ d ∈ Icc 1 (N/r), ArithmeticFunction.vonMangoldt d*(1-((r*d:ℕ):ℝ)/x))-
        (x/2)*(1/(r:ℝ)) := by
    have rp : 0<(r:ℝ) := by exact_mod_cast (mem_Icc.mp hr).1
    have within : (r:ℝ)≤x := (Nat.le_floor_iff xp.le).mp (mem_Icc.mp hr).2
    rw [value,if_pos ((one_le_div rp).mpr within),Nat.floor_div_natCast]
    have hsum : (∑ d ∈ Icc 1 (N/r),ArithmeticFunction.vonMangoldt d*(1-d/(x/r)))=
        ∑ d ∈ Icc 1 (N/r),ArithmeticFunction.vonMangoldt d*(1-((r*d:ℕ):ℝ)/x) := by
      apply Finset.sum_congr rfl
      intro d _
      rw [Nat.cast_mul]
      field_simp
    change _ - _ = _ - _
    rw [show ⌊x⌋₊=N from rfl,hsum]
    ring
  unfold dilation
  change (∑ r ∈ Icc 1 N,value (x/r))=_
  rw [Finset.sum_congr rfl (fun r hr => pieces hr),Finset.sum_sub_distrib,←Finset.mul_sum,src]
  unfold allLogs harmonicRow
  congr 1
  apply Finset.sum_congr rfl
  intro d _
  ring

private theorem pad {f : ℝ → ℝ} (early : ∀ t, t<1 → f t=0) {x : ℝ} (xp : 0≤x)
    {M : ℕ} (covered : ⌊x⌋₊≤M) : dilation f M x=dilation f ⌊x⌋₊ x := by
  unfold dilation
  symm
  apply Finset.sum_subset (fun r hr => mem_Icc.mpr ⟨(mem_Icc.mp hr).1,(mem_Icc.mp hr).2.trans covered⟩)
  intro r hr outside
  have positive : 0<r := (mem_Icc.mp hr).1
  have above : ⌊x⌋₊<r := lt_of_not_ge (fun h => outside (mem_Icc.mpr ⟨positive,h⟩))
  have real_above := (Nat.floor_lt xp).mp above
  exact early _ ((div_lt_one (by exact_mod_cast positive)).mpr real_above)

private theorem even_split (f : ℝ → ℝ) (N : ℕ) (x : ℝ) :
    alternating f N x=dilation f (2*N) x-2*dilation f N (x/2) := by
  induction N with
  | zero => simp [alternating,dilation]
  | succ k ih =>
    unfold alternating dilation at *
    rw [sum_range_succ,show 2*(k+1)=(2*k+1)+1 by ring,
      sum_Icc_succ_top (by omega : 1≤2*k+1+1),sum_Icc_succ_top (by omega : 1≤2*k+1),
      sum_Icc_succ_top (by omega : 1≤k+1),ih]
    push_cast
    have eq : (x/2)/((k:ℝ)+1)=x/(2*(k:ℝ)+2) := by field_simp
    rw [eq]
    ring

theorem alternated_divisors {x : ℝ} (xp : 0<x) {N : ℕ} (cover : ⌊x⌋₊≤2*N) :
    alternating value N x=allLogs x-2*allLogs (x/2)-
      (x/2)*(harmonicRow ⌊x⌋₊-harmonicRow (⌊x⌋₊/2)) := by
  have hxp : 0<x/2 := by positivity
  have half : ⌊x/2⌋₊=⌊x⌋₊/2 := Nat.floor_div_ofNat x 2
  rw [even_split,pad (fun _ => value_early) xp.le cover,
    pad (fun _ => value_early) hxp.le (by rw [half];omega),divisor_read xp,divisor_read hxp,half]
  ring

private def logHead (x : ℝ) (N : ℕ) := ∑ d ∈ Icc 1 N,(1-d/x)*Real.log d
private def ramp (x : ℝ) (M : ℕ) := ∑ j ∈ Icc 1 M,(1-2*(j:ℝ)/x)

private theorem ramp_exact {x : ℝ} (xp : 0<x) (M : ℕ) :
    ramp x M=(M:ℝ)-M*(M+1)/x := by
  induction M with
  | zero => simp [ramp]
  | succ k ih =>
    unfold ramp at *
    rw [sum_Icc_succ_top (by omega : 1≤k+1),ih]
    push_cast
    field_simp
    ring

private theorem ramp_lower {x : ℝ} (large : 1≤x) :
    x/4-2≤ramp x ⌊x/2⌋₊ := by
  have xp : 0<x := by linarith
  let m:ℝ:=⌊x/2⌋₊
  have mn : 0≤m := Nat.cast_nonneg _
  have ml : m≤x/2 := Nat.floor_le (by positivity)
  have mh : x/2<m+1 := Nat.lt_floor_add_one _
  rw [ramp_exact xp]
  change x/4-2≤m-m*(m+1)/x
  have width:=mul_nonneg (by linarith : 0≤x/2-m) (by linarith : 0≤1-(x/2-m))
  apply (le_sub_iff_add_le).mpr
  apply le_of_mul_le_mul_right (a:=x) _ xp
  rw [add_mul,div_mul_cancel₀ _ xp.ne']
  nlinarith only [width,ml,large]

private theorem paired_logs {x : ℝ} (xp : 0<x) (M : ℕ) (inside : 2*(M:ℝ)≤x) :
    2*Real.log 2*ramp x M-Real.log (2*(M:ℝ)+1)≤logHead x (2*M)-2*logHead (x/2) M := by
  induction M with
  | zero => simp [logHead,ramp]
  | succ k ih =>
    have kr : 0≤(k:ℝ) := Nat.cast_nonneg _
    push_cast at inside
    have old:=ih (by linarith)
    unfold logHead ramp at *
    rw [show 2*(k+1)=(2*k+1)+1 by ring,sum_Icc_succ_top (by omega : 1≤k+1),
      sum_Icc_succ_top (by omega : 1≤2*k+1+1),sum_Icc_succ_top (by omega : 1≤2*k+1),
      sum_Icc_succ_top (by omega : 1≤k+1)]
    push_cast
    let a:ℝ:=2*k+1
    let b:ℝ:=2*k+2
    let c:ℝ:=2*k+3
    have ap : 0<a := by dsimp [a];positivity
    have bp : 0<b := by dsimp [b];positivity
    have la : 0≤Real.log a := Real.log_nonneg (by dsimp [a];linarith)
    have ab : Real.log a≤Real.log b := Real.log_le_log ap (by dsimp [a,b];linarith)
    have bc : Real.log b≤Real.log c := Real.log_le_log bp (by dsimp [b,c];linarith)
    have idb : Real.log b=Real.log 2+Real.log ((k:ℝ)+1) := by
      rw [show b=2*((k:ℝ)+1) by dsimp [b];ring,Real.log_mul (by norm_num) (by positivity)]
    have diff:=mul_nonneg (by dsimp [a,b];apply div_nonneg _ xp.le;linarith : 0≤(b-a)/x) la
    have rest:=mul_nonneg (div_nonneg bp.le xp.le) (sub_nonneg.mpr ab)
    have dv : ((k:ℝ)+1)/(x/2)=b/x := by dsimp [b];ring
    rw [dv]
    have eb : 2*((k:ℝ)+1)=b := by dsimp [b];ring
    have ec : 2*((k:ℝ)+1)+1=c := by dsimp [c];ring
    rw [ec,eb]
    change 2*Real.log 2*( _ + (1-b/x))-Real.log c ≤
      (_+(1-a/x)*Real.log a+(1-((2:ℝ)*k+1+1)/x)*Real.log (2*(k:ℝ)+1+1))-2*(_+(1-b/x)*Real.log ((k:ℝ)+1))
    rw [show 2*(k:ℝ)+1+1=b by dsimp [b];ring]
    change 2*Real.log 2*_ - Real.log a≤_ at old
    rw [sub_div] at diff
    rw [←sub_eq_of_eq_add' idb]
    nlinarith only [old,diff,rest,bc]

private theorem harmonic_gap (M N : ℕ) (mp : 0<M) (mn : M≤N) :
    harmonicRow N-harmonicRow M≤Real.log N-Real.log M := by
  induction N,mn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    have nr : 0<(n:ℝ) := by exact_mod_cast mp.trans_le hn
    have upper:=Real.one_sub_inv_le_log_of_pos (show 0<((n:ℝ)+1)/n by positivity)
    have e : 1-(((n:ℝ)+1)/n)⁻¹=1/((n:ℝ)+1) := by field_simp;ring
    rw [e,Real.log_div (by positivity) nr.ne'] at upper
    unfold harmonicRow at *
    rw [sum_Icc_succ_top (by omega : 1≤n+1)]
    push_cast
    linarith only [ih,upper]

private theorem harmonic_upper {x : ℝ} (large : 2≤x) :
    (x/2)*(harmonicRow ⌊x⌋₊-harmonicRow (⌊x⌋₊/2))≤(x/2)*Real.log 2+1 := by
  let N:=⌊x⌋₊
  let M:=N/2
  have xp : 0<x := by linarith
  have two : 2≤N := (Nat.le_floor_iff xp.le).mpr (by exact_mod_cast large)
  have mp : 0<M := by dsimp [M];omega
  have mr : 0<(M:ℝ) := by exact_mod_cast mp
  have nr : 0<(N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have harmonic:=harmonic_gap M N mp (Nat.div_le_self _ _)
  have right : N≤2*M+1 := by dsimp [M];omega
  have rightR : (N:ℝ)≤2*(M:ℝ)+1 := by exact_mod_cast right
  let z:ℝ:=1+1/(2*(M:ℝ))
  have zp : 0<z := by dsimp [z];positivity
  have separate : 2*(M:ℝ)+1=(M:ℝ)*2*z := by dsimp [z];field_simp
  have pay:=Real.log_le_log nr rightR
  rw [separate,Real.log_mul (by positivity) zp.ne',Real.log_mul mr.ne' (by norm_num)] at pay
  have rem:=Real.log_le_sub_one_of_pos zp
  dsimp [z] at rem
  have gap : harmonicRow N-harmonicRow M≤Real.log 2+1/(2*(M:ℝ)) := by linarith
  have floor_upper := Nat.lt_floor_add_one (x/2)
  rw [Nat.floor_div_ofNat x 2] at floor_upper
  change x/2<(M:ℝ)+1 at floor_upper
  have unit : (1:ℝ)≤M := by exact_mod_cast mp
  have charge : (x/2)*(1/(2*(M:ℝ)))≤1 := by
    rw [mul_one_div]
    apply (div_le_iff₀ (by positivity)).mpr
    linarith only [unit,floor_upper]
  change (x/2)*(harmonicRow N-harmonicRow M)≤_
  nlinarith only [mul_le_mul_of_nonneg_left gap (by positivity : 0≤x/2),charge]

private theorem log_lower {x : ℝ} (large : 1≤x) :
    (x/2)*Real.log 2-4*Real.log 2-Real.log (x+1) ≤ allLogs x-2*allLogs (x/2) := by
  let M:=⌊x/2⌋₊
  have xp : 0<x := by linarith
  have ml : (M:ℝ)≤x/2 := Nat.floor_le (by positivity)
  have bound : 2*(M:ℝ)≤x := by linarith
  have fit : 2*M≤⌊x⌋₊ := (Nat.le_floor_iff xp.le).mpr (by exact_mod_cast bound)
  have grow : logHead x (2*M)≤allLogs x := by
    unfold logHead allLogs
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact fun i hi => mem_Icc.mpr ⟨(mem_Icc.mp hi).1,(mem_Icc.mp hi).2.trans fit⟩
    · intro i hi _
      have iu : (i:ℝ)≤x := (Nat.le_floor_iff xp.le).mp (mem_Icc.mp hi).2
      exact mul_nonneg (sub_nonneg.mpr ((div_le_one xp).mpr iu)) (Real.log_nonneg (by exact_mod_cast (mem_Icc.mp hi).1))
  have lower:=paired_logs xp M bound
  have bump:=mul_le_mul_of_nonneg_left (ramp_lower large) (show 0≤2*Real.log 2 by positivity)
  have logb:=Real.log_le_log (show 0<2*(M:ℝ)+1 by positivity) (show 2*(M:ℝ)+1≤x+1 by linarith)
  change _≤allLogs x-2*logHead (x/2) M
  change _≤2*Real.log 2*ramp x M at bump
  linarith only [lower,grow,bump,logb]

/-- The genuine arithmetic alternate reading has an unconditional one-sided square-root price. -/
theorem arithmetic_lower {x : ℝ} (large : 1≤x) {N : ℕ} (cover : ⌊x⌋₊≤2*N) :
    -(12*Real.sqrt x)≤alternating value N x := by
  have xp : 0<x := by linarith
  rw [alternated_divisors xp cover]
  have rr:=Real.one_le_sqrt.mpr large
  by_cases two : 2≤x
  · have harm:=harmonic_upper two
    have logs:=log_lower large
    have small:=Real.log_le_sub_one_of_pos (Real.sqrt_pos_of_pos xp)
    rw [Real.log_sqrt xp.le] at small
    have lg:=Real.log_le_log (show 0<x+1 by positivity) (show x+1≤2*x by linarith)
    rw [Real.log_mul (by norm_num) xp.ne'] at lg
    have lt2:=Real.log_le_sub_one_of_pos (by norm_num : 0<(2:ℝ))
    linarith only [harm,logs,rr,small,lg,lt2]
  · have n : ⌊x⌋₊=1 := by
      have l:=Nat.floor_pos.mpr large
      have h:⌊x⌋₊<2 := (Nat.floor_lt xp.le).mpr (by push_cast;linarith)
      omega
    have m : ⌊x/2⌋₊=0 := Nat.floor_eq_zero.mpr (by linarith)
    simp [allLogs,harmonicRow,n,m]
    linarith only [rr,two]

#print axioms PALRH.PrimeDivisorPrimitive.alternated_divisors
#print axioms PALRH.PrimeDivisorPrimitive.arithmetic_lower

end PALRH.PrimeDivisorPrimitive
