import PALRH.LinearPrimeIntegral
import Mathlib.NumberTheory.Chebyshev

open Finset
open scoped BigOperators Classical

noncomputable section
namespace PALRH.PrimeBoard
open LinearPrimeIntegral

def primes (n : ℕ) := (Icc 1 n).filter Nat.Prime
def dials (n : ℕ) := ∏ p ∈ primes n, p^(2*(n-p))
def demand (n : ℕ) := n.factorial^n*dials n
def capacity (n : ℕ) := n^(n^2)
def allowance (n : ℕ) := 2^(4*n*(n.sqrt+1))
def pairLeft (n : ℕ) := ∏ p ∈ primes n, (n^2/p)^(2*(n-p))
def pairWhole (n : ℕ) := ∏ p ∈ primes n, (n^2)^(2*(n-p))

private theorem dial_pos (n : ℕ) : 0<dials n := by
  apply Finset.prod_pos
  intro p hp
  exact pow_pos (mem_filter.mp hp).2.pos _

theorem pair_return (n : ℕ) (np : 0<n)
    (fit : n.factorial^n*pairWhole n≤capacity n*pairLeft n) : demand n≤capacity n := by
  have pos : 0<pairWhole n := Finset.prod_pos (fun p _ => pow_pos (pow_pos np 2) _)
  have charge : dials n*pairLeft n≤pairWhole n := by
    unfold dials pairLeft pairWhole
    rw [←Finset.prod_mul_distrib]
    apply Finset.prod_le_prod'
    intro p _
    rw [←mul_pow]
    exact Nat.pow_le_pow_left (Nat.mul_div_le _ _) _
  apply le_of_mul_le_mul_right (a:=pairWhole n) _ pos
  calc
    demand n*pairWhole n = (n.factorial^n*pairWhole n)*dials n := by unfold demand;ring
    _ ≤ (capacity n*pairLeft n)*dials n := Nat.mul_le_mul_right _ fit
    _ = capacity n*(dials n*pairLeft n) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ charge

private theorem dial_log (n : ℕ) : Real.log (dials n:ℝ)=2*primeWalk n := by
  unfold dials primeWalk
  push_cast
  rw [Real.log_prod]
  · rw [Finset.mul_sum]
    unfold primes
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases prime : p.Prime
    · simp only [prime,if_true,Real.log_pow,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_sub (mem_Icc.mp hp).2]
      ring
    · simp [prime]
  · intro p hp
    have pp : 0<(p:ℝ) := by exact_mod_cast (mem_filter.mp hp).2.pos
    positivity

def factorialError (n : ℕ) := Real.log (n.factorial:ℝ)-(n:ℝ)*Real.log n+n

private theorem factorial_price (n : ℕ) : 0≤factorialError n ∧ factorialError n≤2*Real.sqrt n := by
  induction n with
  | zero => norm_num [factorialError]
  | succ k ih =>
    by_cases kz : k=0
    · subst k;norm_num [factorialError]
    have kr : 0<(k:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero kz
    let v:=((k:ℝ)+1)/k
    have vp : 0<v := by dsimp [v];positivity
    have step : factorialError (k+1)-factorialError k = 1-(k:ℝ)*Real.log v := by
      unfold factorialError
      push_cast
      rw [Nat.factorial_succ,Nat.cast_mul,Real.log_mul (by positivity) (by positivity)]
      push_cast
      rw [show Real.log v=Real.log ((k:ℝ)+1)-Real.log k from Real.log_div (by positivity) kr.ne']
      ring
    have upper:=mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos vp) kr.le
    have lower:=mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos vp) kr.le
    have e1 : (k:ℝ)*(v-1)=1 := by dsimp [v];field_simp;ring
    have e2 : (k:ℝ)*(1-v⁻¹)=1-1/((k:ℝ)+1) := by dsimp [v];field_simp;ring
    rw [e1] at upper
    rw [e2] at lower
    have nr : 1≤Real.sqrt ((k:ℝ)+1) := Real.one_le_sqrt.mpr (by linarith only [kr])
    have inv : 1/((k:ℝ)+1)≤1/Real.sqrt ((k:ℝ)+1) := by
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith only [Real.sq_sqrt (by positivity : 0≤(k:ℝ)+1),
        mul_nonneg (sub_nonneg.mpr nr) (Real.sqrt_nonneg ((k:ℝ)+1))]
    have jump : 1/Real.sqrt ((k:ℝ)+1)≤2*(Real.sqrt ((k:ℝ)+1)-Real.sqrt k) := by
      apply (div_le_iff₀ (by positivity)).mpr
      nlinarith only [Real.sq_sqrt (by positivity : 0≤(k:ℝ)+1),
        Real.sq_sqrt (Nat.cast_nonneg k),sq_nonneg (Real.sqrt ((k:ℝ)+1)-Real.sqrt k)]
    push_cast
    constructor <;> linarith only [ih.1,ih.2,step,upper,lower,inv,jump]

theorem log_margin {n : ℕ} (_np : 0<n) :
    Real.log (capacity n:ℝ)-Real.log (demand n:ℝ)=
      (n:ℝ)^2-2*primeWalk n-(n:ℝ)*factorialError n := by
  have dp : (dials n:ℝ)≠0 := by exact_mod_cast (dial_pos n).ne'
  unfold demand capacity factorialError
  push_cast
  rw [Real.log_mul (by positivity) dp,Real.log_pow,Real.log_pow,dial_log]
  push_cast
  ring

private theorem repeated (n : ℕ) : 0≤fullWalk n-primeWalk n ∧
    fullWalk n-primeWalk n≤(n:ℝ)*(Chebyshev.psi n-Chebyshev.theta n) := by
  let weight:=fun k : ℕ => ArithmeticFunction.vonMangoldt k - (if k.Prime then Real.log (k:ℝ) else 0)
  have pos (k : ℕ) : 0≤weight k := by
    by_cases p : k.Prime
    · simp [weight,p,ArithmeticFunction.vonMangoldt_apply_prime p]
    · simp [weight,p,ArithmeticFunction.vonMangoldt_nonneg]
  have eq : fullWalk n-primeWalk n=∑ k ∈ Icc 1 n, ((n:ℝ)-k)*weight k := by
    rw [fullWalk,primeWalk,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    by_cases p : k.Prime <;> simp [weight,p,mul_sub]
  have total : (∑ k ∈ Icc 1 n, weight k)=Chebyshev.psi n-Chebyshev.theta n := by
    simp only [Chebyshev.psi,Chebyshev.theta,Nat.floor_natCast,←Finset.Icc_add_one_left_eq_Ioc,
      Nat.zero_add,Finset.sum_filter,←Finset.sum_sub_distrib,weight]
  rw [eq]
  constructor
  · exact Finset.sum_nonneg (fun k hk => mul_nonneg (sub_nonneg.mpr (by exact_mod_cast (mem_Icc.mp hk).2)) (pos k))
  · rw [←total,Finset.mul_sum]
    exact Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_right (sub_le_self _ (Nat.cast_nonneg k)) (pos k))

/-- The hypotheses compare only natural numbers. The second inequality permits a specified number of binary digits. -/
theorem rh_of_integer_board
    (fit : ∀ n : ℕ, 0<n → demand n≤capacity n ∧ capacity n≤demand n*allowance n) : RiemannHypothesis := by
  obtain ⟨D,reps⟩:=Chebyshev.psi_sub_theta_le_mul_sqrt
  let C:=max 0 D+6
  apply rh_of_full_walk (C:=C) (by dsimp [C];positivity)
  intro n np
  have nr : 0<(n:ℝ) := by exact_mod_cast np
  have root : 1≤Real.sqrt (n:ℝ) := Real.one_le_sqrt.mpr (by exact_mod_cast np)
  have dc : 0<demand n := Nat.mul_pos (pow_pos (Nat.factorial_pos _) _) (dial_pos _)
  have cc : 0<capacity n := pow_pos np _
  have ld : 0<(demand n:ℝ) := by exact_mod_cast dc
  have lc : 0<(capacity n:ℝ) := by exact_mod_cast cc
  have low:=Real.log_le_log ld (by exact_mod_cast (fit n np).1 : (demand n:ℝ)≤capacity n)
  have high:=Real.log_le_log lc (by exact_mod_cast (fit n np).2 : (capacity n:ℝ)≤(demand n:ℝ)*(allowance n:ℝ))
  have pa : 0<(allowance n:ℝ) := by unfold allowance;positivity
  rw [Real.log_mul ld.ne' pa.ne'] at high
  have digits : (n.sqrt:ℝ)≤Real.sqrt n :=
    (Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)).mpr (by exact_mod_cast (by simpa [pow_two] using Nat.sqrt_le n : n.sqrt^2≤n))
  have logtwo:=Real.log_le_sub_one_of_pos (by norm_num : 0<(2:ℝ))
  have spare : Real.log (allowance n:ℝ)≤8*n*Real.sqrt n := by
    unfold allowance
    push_cast
    rw [Real.log_pow]
    push_cast
    have scale := mul_le_mul_of_nonneg_left (by linarith only [digits,root] : (n.sqrt:ℝ)+1≤2*Real.sqrt n)
      (show 0≤4*(n:ℝ) by positivity)
    have cost:=mul_le_mul_of_nonneg_left (by linarith only [logtwo] : Real.log 2≤1)
      (show 0≤4*(n:ℝ)*((n.sqrt:ℝ)+1) by positivity)
    nlinarith only [scale,cost]
  have pe:=factorial_price n
  have rep:=repeated n
  have extra:=mul_le_mul_of_nonneg_left (reps n) nr.le
  have allowanceC : D≤max 0 D := le_max_right _ _
  have gain:=mul_le_mul_of_nonneg_right allowanceC (show 0≤(n:ℝ)*Real.sqrt n by positivity)
  have price:=log_margin np
  dsimp only [C]
  apply abs_le.mpr
  constructor <;> nlinarith only [low,high,spare,price,rep.1,rep.2,extra,gain,
    mul_nonneg nr.le pe.1,mul_le_mul_of_nonneg_left pe.2 nr.le,
    mul_nonneg (le_max_left (0:ℝ) D) (mul_nonneg nr.le (Real.sqrt_nonneg (n:ℝ))),
    mul_nonneg nr.le (Real.sqrt_nonneg (n:ℝ))]

theorem rh_of_paired_board
    (fit : ∀ n : ℕ, 0<n → n.factorial^n*pairWhole n≤capacity n*pairLeft n ∧
      capacity n≤demand n*allowance n) : RiemannHypothesis :=
  rh_of_integer_board (fun n np => ⟨pair_return n np (fit n np).1,(fit n np).2⟩)

/-- A dial and a residual digit pack into two cells, each carrying a base-n digit. -/
theorem two_cell_roundtrip {n p r d : ℕ} (np : 0<n) (pp : 0<p)
    (rr : r<n^2/p) (dd : d<p) :
    let v:=r*p+d
    v/n<n ∧ v%n<n ∧ ((v/n*n+v%n)/p=r) ∧ ((v/n*n+v%n)%p=d) := by
  dsimp only
  have fit : r*p+d<n^2 := by
    have upper:=Nat.mul_le_mul_right p (by omega : r+1≤n^2/p)
    rw [Nat.add_mul,Nat.one_mul] at upper
    have total:=Nat.div_mul_le_self (n^2) p
    omega
  have head : (r*p+d)/n<n := (Nat.div_lt_iff_lt_mul np).mpr (by simpa [pow_two] using fit)
  have back : (r*p+d)/n*n+(r*p+d)%n=r*p+d := by
    simpa [Nat.mul_comm,Nat.add_comm] using Nat.mod_add_div (r*p+d) n
  rw [back]
  exact ⟨head,Nat.mod_lt _ np,by simp [Nat.add_comm,Nat.add_mul_div_right _ _ pp,Nat.div_eq_of_lt dd],
    by simp [Nat.add_comm,Nat.mod_eq_of_lt dd]⟩

#print axioms PALRH.PrimeBoard.two_cell_roundtrip
#print axioms PALRH.PrimeBoard.log_margin
#print axioms PALRH.PrimeBoard.rh_of_integer_board
#print axioms PALRH.PrimeBoard.rh_of_paired_board
end PALRH.PrimeBoard
