import PALRH.Octaves
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Squarefree

open Finset
open scoped BigOperators
noncomputable section
namespace PALRH.RoughSquares
open Octaves

def mu (n : ℕ) : ℝ := ArithmeticFunction.moebius n
def remove (p : ℕ) (a : ℕ → ℝ) (n : ℕ) : ℝ := if p ∣ n then 0 else a n
def core := remove 3 (remove 2 mu)
def partialSum (a : ℕ → ℝ) (N : ℕ) : ℝ := ∑ i ∈ Finset.range N, a (i+1)
def coreWalk := partialSum core

theorem mu_prime_mul {p : ℕ} (hp : p.Prime) (n : ℕ) :
    mu (p*n) = if p ∣ n then 0 else -mu n := by
  by_cases h : p ∣ n
  · have div : p*p ∣ p*n := Nat.mul_dvd_mul_left p h
    have no : ¬Squarefree (p*n) := fun free => Nat.squarefree_iff_prime_squarefree.mp free p hp div
    simp [mu,ArithmeticFunction.moebius_eq_zero_of_not_squarefree no,h]
  · rw [if_neg h,mu,ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
      (hp.coprime_iff_not_dvd.mpr h),ArithmeticFunction.moebius_apply_prime hp]
    simp [mu]

theorem remove_split {p : ℕ} (_hp : 0<p) (a : ℕ → ℝ)
    (rule : ∀ d, a (p*d)=if p ∣ d then 0 else -a d) (N : ℕ) :
    partialSum a N=partialSum (remove p a) N-partialSum (remove p a) (N/p) := by
  induction N with
  | zero => simp [partialSum]
  | succ n ih =>
    by_cases hit : p ∣ n+1
    · have dn := Nat.div_mul_cancel hit
      have equal : n+1=p*(n/p+1) := by rw [Nat.succ_div_of_dvd hit] at dn; simpa [Nat.mul_comm] using dn.symm
      have entry : a (n+1) = -remove p a (n/p+1) := by
        rw [equal,rule]
        by_cases twice : p ∣ n/p+1 <;> simp [remove,twice]
      simp only [partialSum,Finset.sum_range_succ,Nat.succ_div_of_dvd hit] at ih ⊢
      have z : remove p a (n+1)=0 := by simp [remove,hit]
      rw [z,add_zero]
      linarith
    · simp only [partialSum,Finset.sum_range_succ,Nat.succ_div_of_not_dvd hit] at ih ⊢
      simp only [remove,if_neg hit] at ih ⊢
      linarith

private lemma as_walk (N : ℕ) : walk N=partialSum mu N := by
  unfold walk partialSum
  apply Finset.sum_bij' (fun d _ => d-1) (fun i _ => i+1)
  · intro d hd
    have := (Finset.mem_Icc.mp hd).1
    omega
  · intro i _; omega
  · intro d hd
    simp [mu,Nat.sub_add_cancel (Finset.mem_Icc.mp hd).1]
  · intro d hd
    have h := Finset.mem_Icc.mp hd
    apply Finset.mem_range.mpr; omega
  · intro i hi
    have h := Finset.mem_range.mp hi
    exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩

/-- Undoing the two small-prime cuts reconstructs the full signed primitive from four core readings. -/
theorem four_cores (n : ℕ) : walk n=coreWalk n-coreWalk (n/3)-coreWalk (n/2)+coreWalk (n/6) := by
  let a := remove 2 mu
  have rule (k : ℕ) : a (3*k)=if 3 ∣ k then 0 else -a k := by
    dsimp [a,remove]
    have two : 2 ∣ 3*k ↔ 2 ∣ k := by omega
    simp only [two,mu_prime_mul Nat.prime_three]
    by_cases h : 2 ∣ k <;> by_cases j : 3 ∣ k <;> simp [h,j]
  rw [as_walk,remove_split (by decide : 0<2) mu (mu_prime_mul Nat.prime_two)]
  change partialSum a n-partialSum a (n/2)=_
  rw [remove_split (by decide : 0<3) a rule n,remove_split (by decide : 0<3) a rule (n/2)]
  simp only [Nat.div_div_eq_div_mul]
  change coreWalk n-coreWalk (n/3)-(coreWalk (n/2)-coreWalk (n/6))=_
  ring

private lemma core_bound (n : ℕ) : |core n|≤1 := by
  have b : |mu n|≤1 := by unfold mu; exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n:=n))
  by_cases a : 2 ∣ n <;> by_cases c : 3 ∣ n <;> simp [core,remove,a,c,b]

/-- Only signs supported on squarefree integers coprime to six enter these sums. -/
def roughSum (X : ℕ) : ℝ := ∑ n ∈ Finset.Icc 1 X, core n

theorem rough_agrees (X : ℕ) : roughSum X=coreWalk X := by
  unfold roughSum coreWalk partialSum
  apply Finset.sum_bij' (fun d _ => d-1) (fun i _ => i+1)
  · intro d hd; exact Nat.sub_add_cancel (Finset.mem_Icc.mp hd).1
  · intro i _; omega
  · intro d hd; rw [Nat.sub_add_cancel (Finset.mem_Icc.mp hd).1]
  · intro d hd; have h := Finset.mem_Icc.mp hd; apply Finset.mem_range.mpr; omega
  · intro i hi; have h := Finset.mem_range.mp hi; apply Finset.mem_Icc.mpr; omega

def pool (X : ℕ) : Finset ℕ := (Finset.range (X+1)).filter (fun p => p.Prime ∧ p≠2 ∧ p≠3)

def tupleCap (X d : ℕ) : ℕ := ∑ A ∈ (pool X).powersetCard d, X/(∏ p ∈ A,p)

def omitted (X d : ℕ) := (Finset.Icc 1 X).filter (fun n => ¬2 ∣ n ∧ ¬3 ∣ n ∧ d≤n.primeFactors.card)

/-- Count every omitted integer by at least one set of d distinct rough prime divisors. -/
theorem omitted_bound (X d : ℕ) : (omitted X d).card≤tupleCap X d := by
  classical
  let atoms := (pool X).powersetCard d
  let multiples := fun A : Finset ℕ => (Finset.range (X+1)).filter (fun n => n≠0 ∧ (∏ p ∈ A,p) ∣ n)
  have subset : omitted X d ⊆ atoms.biUnion multiples := by
    intro n hn
    obtain ⟨range,no2,no3,depth⟩ := Finset.mem_filter.mp hn
    obtain ⟨npos,nX⟩ := Finset.mem_Icc.mp range
    obtain ⟨A,sub,size⟩ := Finset.exists_subset_card_eq depth
    refine Finset.mem_biUnion.mpr ⟨A,Finset.mem_powersetCard.mpr ⟨?_,size⟩,?_⟩
    · intro p hp
      have h := Nat.mem_primeFactors.mp (sub hp)
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have := (Nat.le_of_dvd npos h.2.1).trans nX; omega),
        h.1,fun eq => no2 (eq ▸ h.2.1),fun eq => no3 (eq ▸ h.2.1)⟩
    · have div := (Finset.prod_dvd_prod_of_subset A n.primeFactors id sub).trans (Nat.prod_primeFactors_dvd n)
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),by omega,div⟩
  calc
    _ ≤ (atoms.biUnion multiples).card := Finset.card_le_card subset
    _ ≤ ∑ A ∈ atoms, (multiples A).card := Finset.card_biUnion_le
    _ = _ := by simp only [multiples,atoms,tupleCap,Nat.card_multiples']

private theorem affordable (j : ℕ) : ∃ d : ℕ, 0<d ∧ tupleCap (j*j) d≤j := by
  refine ⟨(pool (j*j)).card+1,by omega,?_⟩
  simp [tupleCap,Finset.powersetCard_eq_empty.mpr (by omega : (pool (j*j)).card<(pool (j*j)).card+1)]

def stopDepth (j : ℕ) : ℕ := Nat.find (affordable j)

def retained (j : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 (j*j), if n.primeFactors.card<stopDepth j then core n else 0

/-- All unseen signs together cost at most one side length, at every square. -/
theorem pruned_cost (j : ℕ) : |coreWalk (j*j)-retained j|≤(j:ℝ) := by
  let X := j*j
  let d := stopDepth j
  have cap : tupleCap X d≤j := (Nat.find_spec (affordable j)).2
  rw [←rough_agrees,roughSum,retained,←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 X, |core n - (if n.primeFactors.card<d then core n else 0)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 X, (if ¬2 ∣ n ∧ ¬3 ∣ n ∧ d≤n.primeFactors.card then (1:ℝ) else 0) := by
      apply Finset.sum_le_sum
      intro n _
      by_cases h : n.primeFactors.card<d <;> by_cases even : 2 ∣ n <;> by_cases three : 3 ∣ n <;>
        simp [h,even,three,core,remove,show (d≤n.primeFactors.card) ↔ ¬n.primeFactors.card<d by omega,
          show |mu n|≤1 by unfold mu; exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n:=n))]
    _ = ((omitted X d).card:ℝ) := by simp [omitted]
    _ ≤ (j:ℝ) := by exact_mod_cast (omitted_bound X d).trans cap

#print axioms PALRH.RoughSquares.four_cores
#print axioms PALRH.RoughSquares.pruned_cost

private lemma drift {j n : ℕ} (le : j*j≤n) :
    |coreWalk n-coreWalk (j*j)|≤((n-j*j:ℕ):ℝ) := by
  obtain ⟨r,eq⟩ := Nat.exists_eq_add_of_le le
  rw [eq,Nat.add_sub_cancel_left]
  unfold coreWalk partialSum
  rw [Finset.sum_range_add,add_sub_cancel_left]
  calc
    _ ≤ ∑ i ∈ Finset.range r, |core (j*j+i+1)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range r, (1:ℝ) := Finset.sum_le_sum (fun i _ => core_bound _)
    _ = (r:ℝ) := by simp

/-- A bound for the signs actually retained at each square. -/
def SquareSigns : Prop := ∀ a : ℝ, 1/2<a → ∃ C : ℝ, 0≤C ∧
    ∀ j : ℕ, 0<j → |retained j| ≤ C*((j*j:ℕ):ℝ)^a

theorem core_bound_of_squares {a C : ℝ} (ha : 1/2<a) (hC : 0≤C)
    (check : ∀ j : ℕ, 0<j → |retained j|≤C*((j*j:ℕ):ℝ)^a) (n : ℕ) :
    |coreWalk n|≤(C+3)*(n:ℝ)^a := by
  have a0 : 0<a := by linarith
  by_cases empty : n=0
  · simp [empty,coreWalk,partialSum,Real.zero_rpow a0.ne']
  let j := n.sqrt
  have js : j*j≤n := Nat.sqrt_le n
  have next := Nat.lt_succ_sqrt n
  change n<(j+1)*(j+1) at next
  have jp : 0<j := by
    by_contra! h
    have z : j=0 := by omega
    rw [z] at next
    omega
  have distance : n-j*j ≤ 2*j := by nlinarith [Nat.sub_add_cancel js]
  have pos : 1≤(n:ℝ) := by exact_mod_cast (by omega : 1≤n)
  have jq : (j:ℝ)^2≤(n:ℝ) := by exact_mod_cast (by nlinarith : j^2≤n)
  have jhalf : (j:ℝ)≤(n:ℝ)^(1/2:ℝ) := by
    rw [←Real.sqrt_eq_rpow]
    exact (Real.le_sqrt (by positivity) (by positivity)).mpr jq
  have jfit := jhalf.trans (Real.rpow_le_rpow_of_exponent_le pos ha.le)
  have window := (drift js).trans (show ((n-j*j:ℕ):ℝ) ≤ 2*(j:ℝ) by exact_mod_cast distance)
  have paid := pruned_cost j
  have nq : ((j*j:ℕ):ℝ) ≤ (n:ℝ) := by exact_mod_cast js
  have small := (check j jp).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (by positivity) nq a0.le) hC)
  have first := abs_add_le (coreWalk n-coreWalk (j*j)) (coreWalk (j*j))
  have second := abs_add_le (coreWalk (j*j)-retained j) (retained j)
  rw [sub_add_cancel] at first second
  linarith

theorem rh_of_square_signs (checks : SquareSigns) : RiemannHypothesis := by
  apply rh_of_walk_growth
  intro a ha
  obtain ⟨C,hC,cap⟩ := checks a ha
  let D := C+3
  have hD : 0≤D := by dsimp [D]; linarith
  refine ⟨4*D,by positivity,?_⟩
  intro n
  have uniform (m : ℕ) (le : m≤n) : |coreWalk m|≤D*(n:ℝ)^a :=
    (core_bound_of_squares ha hC cap m).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) (by exact_mod_cast le) (by linarith)) hD)
  rw [four_cores]
  have h := abs_add_le (coreWalk n-coreWalk (n/3)-coreWalk (n/2)) (coreWalk (n/6))
  linarith [abs_sub (coreWalk n) (coreWalk (n/3)),abs_sub (coreWalk n-coreWalk (n/3)) (coreWalk (n/2)),
    uniform n le_rfl,uniform (n/3) (Nat.div_le_self _ _),uniform (n/2) (Nat.div_le_self _ _),
    uniform (n/6) (Nat.div_le_self _ _)]

#print axioms PALRH.RoughSquares.rh_of_square_signs

end PALRH.RoughSquares
