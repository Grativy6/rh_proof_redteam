import PALRH.DoubledMass
import PALRH.DoubledPrice

open Finset
open scoped BigOperators
noncomputable section
namespace PALRH.RulerOmissions
open DoubledRuler DoubledMass LinearPrimeIntegral

/-- The common fifth-power denominator is used for both the price and the measured prime return. -/
def outlay (n : ℕ) : ℝ := ordinary (2*n) / ((2*n:ℕ):ℝ)^5
def earned (n : ℕ) : ℝ := Real.log (primeSettings n:ℝ) / ((2*n:ℕ):ℝ)^5

/-- The true early return has cubic size in its own label. -/
theorem extra_cubic {n d : ℕ} (dp : 0<d) (early : d≤n) :
    (extra n d:ℝ) ≤ (2/3:ℝ)*(d:ℝ)^3*((2*n:ℕ):ℝ)^3 := by
  let N := 2*n
  have dr : 0<(d:ℝ) := by exact_mod_cast dp
  let m := N/d
  let t : ℝ := (N:ℝ)/d
  have ml : (m:ℝ) ≤ t := (le_div_iff₀ dr).mpr (by exact_mod_cast Nat.div_mul_le_self N d)
  have below : N < (m+1)*d := by
    have h := Nat.mod_add_div N d
    have r := Nat.mod_lt N dp
    dsimp [m]
    rw [Nat.add_mul,Nat.one_mul,Nat.mul_comm (N/d) d]
    omega
  have mh : t ≤ (m:ℝ)+1 := (div_le_iff₀ dr).mpr (by exact_mod_cast below.le)
  have scale (j : ℕ) : (ink N (d*j):ℝ) = (d:ℝ)^6*inkAt t j := by
    unfold ink inkAt
    push_cast
    dsimp [t]
    field_simp
  have identity : (extra n d:ℝ)=(d:ℝ)^6*((∑ j ∈ Icc 1 m,inkAt t j)-t^6/2+t^5) := by
    unfold extra
    simp only [Int.cast_sub,Int.cast_sum,Int.cast_mul,Int.cast_pow,Int.cast_natCast,
               Nat.cast_sub early]
    change (∑ j ∈ Icc 1 m,(ink N (d*j):ℝ))-(N:ℝ)^5*((n:ℝ)-d)=_
    simp_rw [scale]
    rw [←mul_sum]
    dsimp [t,N]
    push_cast
    field_simp
    ring
  have estimate := mul_le_mul_of_nonneg_left (cubic_upper ml mh) (by positivity : 0 ≤ (d:ℝ)^6)
  rw [identity]
  apply estimate.trans
  have eqn : (d:ℝ)^6*((2/3:ℝ)*t^3)=(2/3:ℝ)*(d:ℝ)^3*(N:ℝ)^3 := by
    dsimp [t];field_simp
  exact eqn.le

theorem extra_cap {n d : ℕ} (dp : 0<d) (dn : d≤2*n) :
    (extra n d:ℝ) ≤ 7*((2*n:ℕ):ℝ)^6 := by
  let N := 2*n
  have dr : 0<(d:ℝ) := by exact_mod_cast dp
  have cover : (d:ℝ) ≤ N := by exact_mod_cast dn
  by_cases early : d ≤ n
  · have tight:=extra_cubic dp early
    have bound := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ dr.le cover 3) (by positivity : 0≤(N:ℝ)^3)
    change (extra n d:ℝ) ≤ (2/3:ℝ)*(d:ℝ)^3*(N:ℝ)^3 at tight
    change _ ≤ 7*(N:ℝ)^6
    nlinarith only [tight,bound,pow_nonneg (Nat.cast_nonneg (α:=ℝ) N) 6]
  · have cnt : 2*n/d=1 := by
      have pos:=Nat.div_pos dn dp
      have cap:=(Nat.div_lt_iff_lt_mul dp).mpr (show 2*n<2*d by omega)
      omega
    unfold extra
    simp only [cnt, Icc_self, sum_singleton, mul_one, Nat.sub_eq_zero_of_le (by omega : n≤d),
                Nat.cast_zero, mul_zero, sub_zero, ink, Int.cast_mul, Int.cast_pow, Int.cast_sub,
                Int.cast_natCast, Int.cast_ofNat, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
    have nN : (N:ℝ)=2*(n:ℝ) := by dsimp [N];push_cast;rfl
    rw [←nN]
    change ((N:ℝ)-d)^5*(7*d-N) ≤ 7*(N:ℝ)^6
    have base := pow_le_pow_left₀ (sub_nonneg.mpr cover) (sub_le_self (N:ℝ) dr.le) 5
    have cap : 7*(d:ℝ)-N ≤ 7*N := by linarith only [cover,Nat.cast_nonneg (α:=ℝ) N]
    have h := mul_le_mul base cap (by dsimp [N] at *;push_cast at *; linarith only [dr,show (n:ℝ)<d by exact_mod_cast (Nat.lt_of_not_ge early)]) (by positivity)
    nlinarith only [h]

theorem setting_log (n : ℕ) :
    Real.log (primeSettings n:ℝ) =
      ∑ d ∈ Icc 1 (2*n), if d.Prime ∧ n^7<d^8 then ArithmeticFunction.vonMangoldt d*(extra n d:ℝ) else 0 := by
  unfold primeSettings
  push_cast
  rw [Real.log_prod]
  · apply sum_congr rfl
    intro d hd
    by_cases yes : d.Prime ∧ n^7<d^8
    · rw [if_pos yes,if_pos yes,Real.log_pow,ArithmeticFunction.vonMangoldt_apply_prime yes.1]
      have ok : ((extra n d).toNat:ℝ)=(extra n d:ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg (extra_nonneg (mem_Icc.mp hd).1 (mem_Icc.mp hd).2)
      rw [ok,mul_comm]
    · simp [yes]
  · intro d hd
    by_cases yes : d.Prime ∧ n^7<d^8
    · rw [if_pos yes]
      exact_mod_cast (pow_pos yes.1.pos (extra n d).toNat).ne'
    · simp [yes]

theorem earned_upper {n : ℕ} (np : 0<n) : earned n ≤ outlay n-fullWalk n := by
  have pos : 0 < (((2*n:ℕ):ℝ)^5) := by positivity
  have mulEq:=original_and_return n
  have pay:=DoubledPrice.prime_log_le_all n
  unfold earned outlay
  apply (le_sub_iff_add_le).mpr
  apply (le_div_iff₀ pos).mpr
  rw [add_mul,div_mul_cancel₀ _ pos.ne']
  nlinarith only [mulEq,pay]

/-- First powers removed at the initial cutoff and repeated powers may have distinct prices. -/
theorem loss_with_prices {n D : ℕ} (cap : D≤2*n)
    (small : ∀ d : ℕ, d^8≤n^7 → d≤D) {fee shortFee : ℝ} (fpos : 0≤fee) (spos : 0≤shortFee)
    (fullPrice : ∀ {d : ℕ}, 0<d → d≤2*n → (extra n d:ℝ)≤fee)
    (smallPrice : ∀ {d : ℕ}, 0<d → d≤D → (extra n d:ℝ)≤shortFee) :
    (∑ d ∈ Icc 1 (2*n),ArithmeticFunction.vonMangoldt d*(extra n d:ℝ)) -
       Real.log (primeSettings n:ℝ) ≤
       fee*(Chebyshev.psi (↑(2*n:ℕ):ℝ)-Chebyshev.theta (↑(2*n:ℕ):ℝ))+shortFee*Chebyshev.psi D := by
  let N:=2*n
  let A:=ArithmeticFunction.vonMangoldt
  have bad : (∑ d ∈ Icc 1 N, if ¬ d.Prime then A d else 0)=Chebyshev.psi N-Chebyshev.theta N := by
    rw [Chebyshev.psi_sub_theta_eq_sum_not_prime]
    simp only [Nat.floor_natCast,←Finset.Icc_add_one_left_eq_Ioc,Nat.zero_add,sum_filter]
    rfl
  have low : (∑ d ∈ Icc 1 N, if d≤D then A d else 0)=Chebyshev.psi D := by
    rw [←sum_filter]
    have eqn : (Icc 1 N).filter (fun d => d ≤ D) = Icc 1 D := by
      ext d
      simp only [mem_filter,mem_Icc]
      dsimp [N] at *
      omega
    rw [eqn]
    simp only [Chebyshev.psi,Nat.floor_natCast,←Finset.Icc_add_one_left_eq_Ioc,Nat.zero_add]
    rfl
  change (∑ d ∈ Icc 1 N,A d*(extra n d:ℝ)) - Real.log (primeSettings n:ℝ) ≤
      fee*(Chebyshev.psi N-Chebyshev.theta N)+shortFee*Chebyshev.psi D
  rw [setting_log,←sum_sub_distrib,←bad,←low,mul_sum,mul_sum,←sum_add_distrib]
  apply sum_le_sum
  intro d hd
  have dp := (mem_Icc.mp hd).1
  have av : 0 ≤ A d := ArithmeticFunction.vonMangoldt_nonneg
  have main:=mul_le_mul_of_nonneg_left (fullPrice dp (mem_Icc.mp hd).2) av
  change A d*(extra n d:ℝ) - (if d.Prime ∧ n^7<d^8 then A d*(extra n d:ℝ) else 0) ≤
    fee*(if ¬d.Prime then A d else 0)+shortFee*(if d≤D then A d else 0)
  by_cases keep : d.Prime ∧ n^7<d^8
  · rw [if_pos keep,sub_self]
    apply add_nonneg
    · apply mul_nonneg fpos; split <;> first | exact av | exact le_rfl
    · apply mul_nonneg spos; split <;> first | exact av | exact le_rfl
  · rw [if_neg keep,sub_zero]
    by_cases prim : d.Prime
    · have short := small d (le_of_not_gt (fun h => keep ⟨prim,h⟩))
      rw [if_neg (not_not_intro prim),if_pos short,mul_zero,zero_add]
      exact (mul_le_mul_of_nonneg_left (smallPrice dp short) av).trans_eq (mul_comm _ _)
    · rw [if_pos prim]
      by_cases short : d≤D
      · rw [if_pos short];nlinarith only [main,mul_nonneg spos av]
      · rw [if_neg short,mul_zero,add_zero];nlinarith only [main]

theorem earned_lower {n D : ℕ} (np : 0<n) (cap : D≤2*n)
    (small : ∀ d : ℕ, d^8≤n^7 → d≤D) :
    outlay n-fullWalk n - 14*n*(Chebyshev.psi (2*n)-Chebyshev.theta (2*n)+Chebyshev.psi D) ≤ earned n := by
  let N:=2*n
  let A:=ArithmeticFunction.vonMangoldt
  let fee : ℝ:=7*(N:ℝ)^6
  have fn : 0≤fee := by dsimp [fee];positivity
  have loss:=loss_with_prices cap small (fee:=fee) (shortFee:=fee) fn fn
    (fun h late => extra_cap h late) (fun h within => extra_cap h (within.trans cap))
  rw [←mul_add] at loss
  change (∑ d ∈ Icc 1 N,A d*(extra n d:ℝ))-Real.log (primeSettings n:ℝ) ≤
    fee*(Chebyshev.psi N-Chebyshev.theta N+Chebyshev.psi D) at loss
  have divPos : 0 < (N:ℝ)^5 := by dsimp [N];positivity
  have carrier := original_and_return n
  change ordinary N=(N:ℝ)^5*fullWalk n + ∑ d ∈ Icc 1 N,A d*(extra n d:ℝ) at carrier
  unfold earned outlay
  change ordinary N / (N:ℝ)^5-fullWalk n-14*n*(_+_) ≤ Real.log (primeSettings n:ℝ)/(N:ℝ)^5
  apply (le_div_iff₀ divPos).mpr
  rw [sub_mul,sub_mul,div_mul_cancel₀ _ divPos.ne']
  have normalization : 14*(n:ℝ)*(N:ℝ)^5=fee := by dsimp [N,fee];push_cast;ring
  rw [←normalization] at loss
  have nN : (N:ℝ)=2*(n:ℝ) := by dsimp [N];push_cast;rfl
  rw [←nN]
  nlinarith only [loss,carrier]

end PALRH.RulerOmissions
