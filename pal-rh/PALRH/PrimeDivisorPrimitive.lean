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

private theorem paired_upper {x : ℝ} (xp : 0<x) (M : ℕ) (inside : 2*(M:ℝ)≤x) :
    logHead x (2*M)-2*logHead (x/2) M≤2*Real.log 2*ramp x M+(M:ℝ)/x*Real.log (x+1) := by
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
    let e:ℝ:=2*k+2
    have ap : 0<a := by dsimp [a];positivity
    have ep : 0<e := by dsimp [e];positivity
    have high : e≤x := by dsimp [e];linarith only [inside]
    have same : Real.log e=Real.log 2+Real.log ((k:ℝ)+1) := by
      rw [show e=2*((k:ℝ)+1) by dsimp [e];ring,Real.log_mul (by norm_num) (by positivity)]
    have ab : Real.log a≤Real.log e := Real.log_le_log ap (by dsimp [a,e];linarith)
    have tip : Real.log a≤Real.log (x+1) := Real.log_le_log ap (by dsimp [a];linarith only [inside])
    have r0 : 0≤1-e/x := sub_nonneg.mpr ((div_le_one xp).mpr high)
    have diff : e/x-a/x=1/x := by dsimp [e,a];ring
    have rec1:=mul_le_mul_of_nonneg_left ab r0
    have rec2:=mul_le_mul_of_nonneg_left tip (one_div_nonneg.mpr xp.le)
    rw [←diff] at rec2
    rw [show ((k:ℝ)+1)/(x/2)=e/x by dsimp [e];ring,
      show 2*((k:ℝ)+1)=e by dsimp [e];ring,
      show 2*(k:ℝ)+1+1=e by dsimp [e];ring]
    change (_+(1-a/x)*Real.log a+(1-e/x)*Real.log e)-2*(_+(1-e/x)*Real.log ((k:ℝ)+1))≤_
    rw [add_div (k:ℝ) 1 x]
    have bump : (e/x-a/x)*Real.log (x+1)=(1/x)*Real.log (x+1) := by rw [diff]
    rw [bump] at rec2
    rw [same] at rec1 ⊢
    nlinarith only [old,rec1,rec2]

private theorem harmonic_floor (m n : ℕ) (mn : m≤n) :
    Real.log ((n:ℝ)+1)-Real.log ((m:ℝ)+1)≤harmonicRow n-harmonicRow m := by
  induction n,mn using Nat.le_induction with
  | base => simp
  | succ n _ ih =>
    have nr : 0<(n:ℝ)+1 := by positivity
    have z : 0<((n:ℝ)+2)/((n:ℝ)+1) := by positivity
    have up:=Real.log_le_sub_one_of_pos z
    have id : ((n:ℝ)+2)/((n:ℝ)+1)-1=1/((n:ℝ)+1) := by field_simp;ring
    rw [Real.log_div (by positivity) nr.ne',id] at up
    unfold harmonicRow at *;rw [sum_Icc_succ_top (by omega : 1≤n+1)]
    push_cast
    rw [show (n:ℝ)+1+1=n+2 by ring]
    linarith only [up,ih]

private theorem harmonic_lower {x : ℝ} (large : 1≤x) :
    (x/2)*Real.log 2-1≤(x/2)*(harmonicRow ⌊x⌋₊-harmonicRow (⌊x⌋₊/2)) := by
  let n:=⌊x⌋₊
  let m:=n/2
  have xp:=zero_lt_one.trans_le large
  have mpos : 0<(m:ℝ)+1 := by positivity
  have npos : 0<(n:ℝ)+1 := by positivity
  have h:=harmonic_floor m n (Nat.div_le_self _ _)
  have ceil : x≤(n:ℝ)+1 := (Nat.lt_floor_add_one x).le
  have root : (m:ℝ)≤x/2 := by
    rw [show m=⌊x/2⌋₊ from (Nat.floor_div_ofNat x 2).symm];exact Nat.floor_le (by positivity)
  have w:=Real.log_le_sub_one_of_pos (show 0<1+2/x by positivity)
  rw [show 1+2/x-1=2/x by ring] at w
  have cmp : 2*((m:ℝ)+1)≤((n:ℝ)+1)*(1+2/x) := by
    have temp:=mul_le_mul_of_nonneg_right ceil (show 0≤1+2/x by positivity)
    have base : x*(1+2/x)=x+2 := by field_simp
    rw [base] at temp
    linarith only [root,temp]
  have logs:=Real.log_le_log (show 0<(2:ℝ)*((m:ℝ)+1) by positivity) cmp
  rw [Real.log_mul (by norm_num) mpos.ne',Real.log_mul npos.ne' (by positivity)] at logs
  have pay:=mul_le_mul_of_nonneg_left (show Real.log 2-2/x≤harmonicRow n-harmonicRow m by linarith only [h,w,logs])
    (show 0≤x/2 by positivity)
  have one : (x/2)*(2/x)=1 := by field_simp
  rw [mul_sub,one] at pay;exact pay

/-- The opposite orientation of the same divisor read is paid by pairing consecutive
logarithms. No estimate of the locations of primes is needed in either orientation. -/
theorem arithmetic_upper {x : ℝ} (large : 1≤x) {N : ℕ} (cover : ⌊x⌋₊≤2*N) :
    alternating value N x≤12*Real.sqrt x := by
  have xp:=zero_lt_one.trans_le large
  let m:=⌊x/2⌋₊
  have ml : (m:ℝ)≤x/2 := Nat.floor_le (by positivity)
  have hi : 2*(m:ℝ)≤x := by linarith
  have upper:=paired_upper xp m hi
  have rampTop : ramp x m≤x/4 := by
    rw [ramp_exact xp]
    apply (sub_le_iff_le_add).mpr
    apply le_of_mul_le_mul_right (a:=x) _ xp
    rw [add_mul,div_mul_cancel₀ _ xp.ne']
    nlinarith only [sq_nonneg ((m:ℝ)-x/2),Nat.cast_nonneg (α:=ℝ) m]
  have two : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  have logp : 0≤Real.log (x+1) := Real.log_nonneg (by linarith)
  have nx : 2*m≤⌊x⌋₊ := (Nat.le_floor_iff xp.le).mpr (by exact_mod_cast hi)
  have hfn : m=⌊x⌋₊/2 := Nat.floor_div_ofNat x 2
  have parity : ⌊x⌋₊=2*m ∨ ⌊x⌋₊=2*m+1 := by omega
  have rest : allLogs x≤logHead x (2*m)+Real.log (x+1) := by
    unfold allLogs logHead
    rcases parity with eq|eq
    · rw [eq];linarith only [logp]
    · rw [eq,sum_Icc_succ_top (by omega : 1≤2*m+1)]
      have tp : 0<((2*m+1:ℕ):ℝ) := by positivity
      have small : ((2*m+1:ℕ):ℝ)≤x+1 := by rw [←eq];linarith only [Nat.floor_le xp.le]
      have ln : 0≤Real.log ((2*m+1:ℕ):ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1≤2*m+1))
      have top:=Real.log_le_log tp small
      nlinarith only [top,mul_nonneg (div_nonneg tp.le xp.le) ln]
  have topRamp:=mul_le_mul_of_nonneg_left rampTop (mul_nonneg (by norm_num : 0≤(2:ℝ)) two)
  have part:=mul_le_mul_of_nonneg_right ((div_le_one xp).mpr (show (m:ℝ)≤x by linarith)) logp
  have harm:=harmonic_lower large
  rw [alternated_divisors xp cover]
  change allLogs x-2*logHead (x/2) m-_≤_
  have rr:=Real.one_le_sqrt.mpr large
  have small:=Real.log_le_sub_one_of_pos (Real.sqrt_pos_of_pos xp)
  rw [Real.log_sqrt xp.le] at small
  have lg:=Real.log_le_log (by positivity : 0<x+1) (show x+1≤2*x by linarith)
  rw [Real.log_mul (by norm_num) xp.ne'] at lg
  have l2:=Real.log_le_sub_one_of_pos (by norm_num : 0<(2:ℝ))
  linarith only [upper,rest,topRamp,part,harm,small,lg,l2,rr]

#print axioms PALRH.PrimeDivisorPrimitive.alternated_divisors
#print axioms PALRH.PrimeDivisorPrimitive.arithmetic_lower

end PALRH.PrimeDivisorPrimitive
