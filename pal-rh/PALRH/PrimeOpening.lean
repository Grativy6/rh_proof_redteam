import PALRH.OuterBlock
import Mathlib.Data.Nat.GCD.Basic

open Finset
open scoped BigOperators
noncomputable section
namespace PALRH.PrimeOpening
open RoughSquares CoreMatrix OneTick

/-- Each prime frame has its own arithmetic selector and signed source. -/
def allow (N k : ℕ) : ℝ := if k.Coprime N then 1 else 0
def marked (N k : ℕ) : ℝ := mu k*allow N k
def census (N k : ℕ) := partialSum (allow N) k
def signed (N k : ℕ) := partialSum (marked N) k

private lemma same_ifresh {N p : ℕ} (fresh : p.Coprime N) (k : ℕ) :
    allow N (p*k)=allow N k := by
  have turn : (p*k).Coprime N ↔ k.Coprime N := Nat.coprime_mul_iff_left.trans (and_iff_right fresh)
  simp only [allow,turn]

private lemma select_new {N p : ℕ} (prime : p.Prime) :
    allow (N*p)=remove p (allow N) := by
  funext k
  have atp : k.Coprime p ↔ ¬p ∣ k := Nat.coprime_comm.trans prime.coprime_iff_not_dvd
  by_cases hit : p ∣ k <;> simp [allow,remove,Nat.coprime_mul_iff_right,atp,hit]

/-- Adding a genuinely new prime subtracts its quotient-clock reading from the census. -/
theorem open_census {N p : ℕ} (prime : p.Prime) (fresh : p.Coprime N) (k : ℕ) :
    census (N*p) k = census N k-census N (k/p) := by
  unfold census
  rw [select_new prime]
  induction k with
  | zero => simp [partialSum]
  | succ n ih =>
    by_cases hit : p ∣ n+1
    · have dn := Nat.div_mul_cancel hit
      have equal : n+1=p*(n/p+1) := by
        rw [Nat.succ_div_of_dvd hit] at dn
        simpa only [Nat.mul_comm] using dn.symm
      have old : allow N (n+1)=allow N (n/p+1) := by rw [equal,same_ifresh fresh]
      have gone : remove p (allow N) (n+1)=0 := by simp [remove,hit]
      simp only [partialSum,Finset.sum_range_succ,Nat.succ_div_of_dvd hit] at ih ⊢
      rw [gone,old]
      linarith
    · have keep : remove p (allow N) (n+1)=allow N (n+1) := by simp [remove,hit]
      simp only [partialSum,Finset.sum_range_succ,Nat.succ_div_of_not_dvd hit] at ih ⊢
      rw [keep]; linarith

/-- Transporting the signed primitive goes in the other direction. The new
frame appears in both terms on the right, including the quotient argument. -/
theorem recover_signed {N p : ℕ} (prime : p.Prime) (fresh : p.Coprime N) (k : ℕ) :
    signed N k=signed (N*p) k-signed (N*p) (k/p) := by
  have law (n : ℕ) : marked N (p*n)=if p ∣ n then 0 else -marked N n := by
    rw [marked,mu_prime_mul prime,same_ifresh fresh]
    by_cases h : p ∣ n <;> simp [h,marked]
  have matchNew : marked (N*p)=remove p (marked N) := by
    funext n
    simp only [marked,select_new prime]
    by_cases h : p ∣ n <;> simp [remove,h,marked]
  unfold signed
  rw [matchNew]
  exact remove_split prime.pos _ law k

private lemma allow_six (k : ℕ) : allow 6 k=gate k := by
  have a : k.Coprime 2 ↔ ¬2 ∣ k := Nat.coprime_comm.trans Nat.prime_two.coprime_iff_not_dvd
  have b : k.Coprime 3 ↔ ¬3 ∣ k := Nat.coprime_comm.trans Nat.prime_three.coprime_iff_not_dvd
  have g : k.Coprime 6 ↔ k.Coprime 2 ∧ k.Coprime 3 := by
    change k.Coprime (2*3) ↔ _
    exact Nat.coprime_mul_iff_right
  by_cases h : 2 ∣ k <;> by_cases t : 3 ∣ k <;> simp [allow,gate,g,a,b,h,t]

theorem census_six (k : ℕ) : census 6 k=count k := by
  simp [census,count,partialSum,allow_six]

theorem five_price (k : ℕ) : census 30 k=count k-count (k/5) := by
  simpa only [census_six] using open_census (N:=6) Nat.prime_five (by decide) k

theorem before_seven {q : ℕ} (positive : 0<q) (first : q<7) : census 30 q=1 := by
  interval_cases q <;> norm_num [census,partialSum,Finset.sum_range_succ,allow,Nat.coprime_iff_gcd_eq_one] <;> decide

/-- A balanced coefficient vector in the same reciprocal band has zero
uncentered quadratic response after five is opened. -/
theorem five_flattened {h : ℕ} (S : Finset ℕ) (a : ℕ → ℝ)
    (low : ∀ i ∈ S, ∀ j ∈ S, 0<h*h/(i*j)) (high : ∀ i ∈ S, ∀ j ∈ S, h*h/(i*j)<7)
    (balanced : (∑ i ∈ S, a i)=0) :
    (∑ i ∈ S, ∑ j ∈ S, a i*a j*census 30 (h*h/(i*j)))=0 := by
  calc
    _ = ∑ i ∈ S, ∑ j ∈ S, a i*a j := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [before_seven (low i hi j hj) (high i hi j hj),mul_one]
    _ = _ := by simp only [←Finset.mul_sum,balanced,mul_zero,Finset.sum_const_zero]

#print axioms PALRH.PrimeOpening.recover_signed
#print axioms PALRH.PrimeOpening.five_price
#print axioms PALRH.PrimeOpening.five_flattened

/-- Integrating the affine error in each of the period's unit cells gives
this finite rational second moment. -/
def finiteCensus (N : ℕ) : ℕ → ℕ
  | 0 => 0
  | k+1 => finiteCensus N k + if (k+1).Coprime N then 1 else 0

theorem finiteCensus_eq (N k : ℕ) : (finiteCensus N k:ℝ)=census N k := by
  induction k with
  | zero => simp [finiteCensus,census,partialSum]
  | succ k ih =>
    simp only [finiteCensus,Nat.cast_add,census,partialSum,Finset.sum_range_succ] at ih ⊢
    rw [ih]
    by_cases h : (k+1).Coprime N <;> simp [allow,h]

private def cellSquare (N : ℕ) (ρ : ℚ) (k : ℕ) : ℚ :=
  let v := (finiteCensus N k:ℚ)-ρ*k
  v^2-ρ*v+ρ^2/3

def periodVariance (N : ℕ) : ℚ :=
  (∑ k ∈ Finset.range N, cellSquare N ((finiteCensus N N:ℚ)/N) k)/N

theorem six_variance : periodVariance 6=1/9 := by decide +kernel
theorem thirty_variance : periodVariance 30=8/45 := by decide +kernel
theorem price_of_opening_five : periodVariance 30=(8/5)*periodVariance 6 := by
  rw [six_variance,thirty_variance]
  norm_num

#print axioms PALRH.PrimeOpening.price_of_opening_five

end PALRH.PrimeOpening
