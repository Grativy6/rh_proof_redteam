import PALRH.PrimeRenewal
import Mathlib.Analysis.PSeries

open Finset Set Filter
open scoped BigOperators Topology
noncomputable section
namespace PALRH.RepeatAllowance
open PrimeRenewal RectangleBalance

def repeated (n : ℕ) : ℝ := if n.Prime then 0 else ArithmeticFunction.vonMangoldt n
def highConstant : ℝ := 16*∑' n : ℕ, (n:ℝ)^(-(5/4:ℝ))

private theorem sqrt_pow {x : ℝ} (hp : 0≤x) (k : ℕ) : Real.sqrt (x^k)=(Real.sqrt x)^k := by
  induction k with
  | zero => simp
  | succ k old => rw [pow_succ,Real.sqrt_mul (pow_nonneg hp k),old,pow_succ]

private theorem geometric {z : ℝ} (nz : 0≤z) (cap : z≤3/4) (N : ℕ) :
    (∑ k ∈ Finset.range N, z^k)≤4 := by
  have eq (n : ℕ) : (∑ k ∈ Finset.range n, (3/4:ℝ)^k)+4*(3/4:ℝ)^n=4 := by
    induction n with
    | zero => norm_num
    | succ n old => rw [Finset.sum_range_succ,pow_succ];linarith
  have sum := Finset.sum_le_sum (s:=Finset.range N) (fun k _ => pow_le_pow_left₀ nz cap k)
  linarith [eq N,show 0≤(3/4:ℝ)^N by positivity]

private theorem cube_weight {p : ℕ} (pos : 2≤p) :
    Real.log p*(1/Real.sqrt p)^3≤4*(p:ℝ)^(-(5/4:ℝ)) := by
  have pp : 0<(p:ℝ) := by exact_mod_cast (show 0<p by omega)
  have cap := Real.log_le_rpow_div pp.le (by norm_num : (0:ℝ)<1/4)
  have root : (1/Real.sqrt p)^3=(p:ℝ)^(-(3/2:ℝ)) := by
    rw [Real.sqrt_eq_rpow,one_div,←Real.rpow_neg pp.le,←Real.rpow_natCast,←Real.rpow_mul pp.le]
    norm_num
  rw [root]
  have scale := mul_le_mul_of_nonneg_right cap (Real.rpow_nonneg pp.le (-(3/2:ℝ)))
  apply scale.trans_eq
  calc
    _=4*((p:ℝ)^(1/4:ℝ)*(p:ℝ)^(-(3/2:ℝ))) := by ring
    _=_ := by rw [←Real.rpow_add pp];norm_num

private def price (t : ℕ×ℕ) := Real.log t.1*(1/Real.sqrt t.1)^(t.2+3)

private theorem large_powers (N : ℕ) :
    (∑ t ∈ (Finset.Icc 2 N) ×ˢ Finset.range (N+1), price t)≤highConstant := by
  let I := Finset.Icc 2 N
  let K := Finset.range (N+1)
  rw [Finset.sum_product]
  have each (p : ℕ) (hp : p∈I) : (∑ k ∈ K, price (p,k))≤16*(p:ℝ)^(-(5/4:ℝ)) := by
    have two := (Finset.mem_Icc.mp hp).1
    have pos : 0<(p:ℝ) := by exact_mod_cast (show 0<p by omega)
    have unit : (1:ℝ)≤p := by exact_mod_cast (show 1≤p by omega)
    let z := 1/Real.sqrt p
    have root : 4/3≤Real.sqrt p := by
      apply le_of_sq_le_sq _ (Real.sqrt_nonneg _)
      rw [Real.sq_sqrt pos.le];have two' : (2:ℝ)≤p := by exact_mod_cast two
      linarith
    have cap : z≤3/4 := (div_le_iff₀ (Real.sqrt_pos.mpr pos)).mpr (by linarith)
    have zn : 0≤z := by dsimp [z];positivity
    have h := geometric zn cap (N+1)
    have move (k : ℕ) : price (p,k)=Real.log p*z^3*z^k := by dsimp [price,z];rw [pow_add];ring
    simp_rw [move]
    rw [←Finset.mul_sum]
    apply (mul_le_mul_of_nonneg_left h (mul_nonneg (Real.log_nonneg unit) (pow_nonneg zn 3))).trans
    have cube := cube_weight two
    change Real.log p*z^3≤_ at cube
    linarith
  apply (Finset.sum_le_sum each).trans
  rw [←Finset.mul_sum,highConstant]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact (Real.summable_nat_rpow.mpr (by norm_num : -(5/4:ℝ)< -1)).sum_le_tsum _ (fun n _ => Real.rpow_nonneg (by positivity) _)

theorem repeated_budget {N : ℕ} (np : 0<N) :
    (∑ n ∈ Finset.Icc 1 N, repeated n/Real.sqrt n)≤Real.log N/2+(Real.log 4+4)+highConstant := by
  let I := Finset.Icc 1 N
  let primes := (Finset.Icc 1 (Nat.sqrt N)).filter Nat.Prime
  let pairs := ((Finset.Icc 2 N) ×ˢ Finset.range (N+1)).filter (fun t : ℕ×ℕ => t.1^(t.2+3)≤N)
  let small := fun p : ℕ => Real.log p/p
  have pm (p : ℕ) (hp : p∈primes) : p^2∈I := by
    have rr := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1)
    exact Finset.mem_Icc.mpr ⟨show 0<p^2 by exact pow_pos rr.1 _,by simpa [sq] using (Nat.le_sqrt.mp rr.2)⟩
  have hm (t : ℕ×ℕ) (ht : t∈pairs) : t.1^(t.2+3)∈I := by
    have h := (Finset.mem_Icc.mp (Finset.mem_product.mp (Finset.mem_filter.mp ht).1).1).1
    exact Finset.mem_Icc.mpr ⟨show 0<t.1^(t.2+3) from pow_pos (show 0<t.1 by omega) _,(Finset.mem_filter.mp ht).2⟩
  have sn (p : ℕ) (hp : p∈primes) : 0≤small p :=
    div_nonneg (Real.log_nonneg (by exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1)) (by positivity)
  have hn (t : ℕ×ℕ) (ht : t∈(Finset.Icc 2 N) ×ˢ Finset.range (N+1)) : 0≤price t := by
    have h := (Finset.mem_Icc.mp (Finset.mem_product.mp ht).1).1
    exact mul_nonneg (Real.log_nonneg (by exact_mod_cast (show 1≤t.1 by omega))) (by positivity)
  have point (n : ℕ) (hi : n∈I) : repeated n/Real.sqrt n≤
      (∑ p ∈ primes with p^2=n, small p)+∑ t ∈ pairs with t.1^(t.2+3)=n, price t := by
    have sp : 0≤∑ p ∈ primes with p^2=n, small p := Finset.sum_nonneg (fun p h => sn p (Finset.mem_filter.mp h).1)
    have ht : 0≤∑ t ∈ pairs with t.1^(t.2+3)=n, price t :=
      Finset.sum_nonneg (fun t h => hn t (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).1)
    by_cases is : n.Prime
    · simpa [repeated,is] using add_nonneg sp ht
    by_cases zero : ArithmeticFunction.vonMangoldt n=0
    · simpa [repeated,is,zero] using add_nonneg sp ht
    obtain ⟨p,hpn,k,hkn,prime,kp,eq⟩ := (isPrimePow_nat_iff_bounded n).mp (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp zero)
    have two : 2≤k := by by_contra! bad;rw [show k=1 by omega,pow_one] at eq;exact is (eq ▸ prime)
    have val : repeated n=Real.log p := by
      rw [repeated,if_neg is,←eq,ArithmeticFunction.vonMangoldt_apply_pow kp.ne',ArithmeticFunction.vonMangoldt_apply_prime prime]
    rw [val]
    by_cases sqr : k=2
    · rw [sqr] at eq
      have member : p∈primes.filter (fun p => p^2=n) := Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨prime.pos,Nat.le_sqrt.mpr (by
          simpa only [←sq,eq] using (Finset.mem_Icc.mp hi).2)⟩,prime⟩,eq⟩
      have one := Finset.single_le_sum (fun p h => sn p (Finset.mem_filter.mp h).1) member
      have right : Real.sqrt n=p := by rw [←eq,Nat.cast_pow,Real.sqrt_sq (by positivity)]
      rw [right]
      exact one.trans (le_add_of_nonneg_right ht)
    · let b:=k-3
      have exponent : b+3=k := by dsimp [b];omega
      have cutoff : p≤N := hpn.trans (Finset.mem_Icc.mp hi).2
      have smallk : k≤N := hkn.trans (Finset.mem_Icc.mp hi).2
      have km : b<N+1 := by dsimp [b];omega
      have member : (p,b)∈pairs.filter (fun t => t.1^(t.2+3)=n) := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨prime.two_le,cutoff⟩,
          Finset.mem_range.mpr km⟩,?_⟩,?_⟩
        · change p^(b+3)≤N;rw [exponent,eq];exact (Finset.mem_Icc.mp hi).2
        · change p^(b+3)=n;rw [exponent,eq]
      have one := Finset.single_le_sum (fun t h => hn t (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).1) member
      have value : Real.log p/Real.sqrt n=price (p,b) := by
        rw [←eq,Nat.cast_pow,sqrt_pow (by positivity)]
        dsimp only [price]
        rw [exponent,one_div,inv_pow,div_eq_mul_inv]
      exact value.le.trans (one.trans (le_add_of_nonneg_left sp))
  have total := Finset.sum_le_sum point
  rw [Finset.sum_add_distrib,Finset.sum_fiberwise_of_maps_to pm small,Finset.sum_fiberwise_of_maps_to hm price] at total
  apply total.trans
  apply add_le_add _ ((Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun t ht _ => hn t ht)).trans
    (large_powers N))
  have identity : (∑ p ∈ primes, small p)=∑ p ∈ Finset.Icc 1 (Nat.sqrt N), primeMass p/p := by
    dsimp only [primes,small]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl;intro p _
    by_cases prime : p.Prime <;> simp [primeMass,prime]
  rw [identity]
  have root : 0<Nat.sqrt N := Nat.le_sqrt.mpr (by simpa using (show 1≤N by omega))
  have cap := prime_harmonic_budget root
  have rn : (Nat.sqrt N:ℝ)≤Real.sqrt N := by
    apply le_of_sq_le_sq _ (Real.sqrt_nonneg _)
    rw [Real.sq_sqrt (by positivity)]
    exact_mod_cast Nat.sqrt_le' N
  have limit := Real.log_le_log (by exact_mod_cast root : 0<(Nat.sqrt N:ℝ)) rn
  rw [Real.log_sqrt (by positivity)] at limit
  linarith

#print axioms PALRH.RepeatAllowance.repeated_budget
end PALRH.RepeatAllowance
