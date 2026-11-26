import PALRH.SieveFrame
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Dvd

open Finset
open scoped BigOperators

namespace PALRH.UpperHalfBoard
open PrimeBand PrimeBoard

/-- In the binomial expansion retain the terms with zero or one new symbol. -/
private theorem first_two_terms (a k : ℕ) :
    a^(k+1)+(k+1)*a^k≤(a+1)^(k+1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have payment:=Nat.mul_le_mul_right (a+1) ih
    calc
      _ ≤ (a^(k+1)+(k+1)*a^k)*(a+1) := by
        rw [pow_succ a (k+1),pow_succ a k]
        ring_nf
        omega
      _ ≤ _ := by simpa only [pow_succ (a+1) (k+1)] using payment

private theorem doubled_words (n : ℕ) (hn : 0<n) : 2*n^n≤(n+1)^n := by
  obtain ⟨k,rfl⟩:=Nat.exists_eq_succ_of_ne_zero hn.ne'
  calc
    _ = (k+1)^(k+1)+(k+1)*(k+1)^k := by
      change 2*(k+1)^(k+1)=(k+1)^(k+1)+(k+1)*(k+1)^k
      rw [pow_succ' (k+1) k]
      omega
    _ ≤ _ := first_two_terms (k+1) k

private theorem factorial_room {n : ℕ} (hn : 10≤n) : 2*(2^n*n.factorial)≤n^n := by
  induction n,hn using Nat.le_induction with
  | base => decide
  | succ m hm ih =>
    calc
      _ = (m+1)*(2*(2*(2^m*m.factorial))) := by rw [pow_succ,Nat.factorial_succ];ring
      _ ≤ (m+1)*(2*m^m) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 2 ih)
      _ ≤ (m+1)*((m+1)^m) := Nat.mul_le_mul_left _ (doubled_words m (by omega))
      _ = _ := by rw [pow_succ']

private theorem outer_dials (n : ℕ) : retained n ((n+1)/2) ≤ (2^n)^n := by
  let S:=(primes n).filter (fun p => (n+1)/2<p)
  have product_dvd : (∏ p ∈ S,p) ∣ n.choose (n/2) := by
    apply Finset.prod_primes_dvd
    · intro p hp
      exact (mem_filter.mp (mem_filter.mp hp).1).2.prime
    · intro p hp
      have head:=mem_filter.mp hp
      have prime:=(mem_filter.mp head.1).2
      have ends:=(mem_Icc.mp (mem_filter.mp head.1).1).2
      exact prime.dvd_choose (by omega) (by omega) ends
  have size := Nat.le_of_dvd (Nat.choose_pos (by omega : n/2≤n)) product_dvd
  calc
    retained n ((n+1)/2) ≤ ∏ p ∈ S,p^n := by
      unfold retained
      apply Finset.prod_le_prod'
      intro p hp
      have h:=mem_filter.mp hp
      exact Nat.pow_le_pow_right (mem_filter.mp h.1).2.pos (by omega)
    _ = (∏ p ∈ S,p)^n := Finset.prod_pow _ _ _
    _ ≤ _ := Nat.pow_le_pow_left (size.trans (Nat.choose_le_two_pow _ _)) _

/-- Every sufficiently large board can store all row orders and all upper-half prime dials,
and still has a full spare binary choice on every row. -/
theorem upper_half_with_spare {n : ℕ} (hn : 10≤n) :
    inputCount n ((n+1)/2)*2^n≤capacity n := by
  unfold inputCount capacity
  calc
    _ ≤ (n.factorial^n*(2^n)^n)*2^n := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (outer_dials n))
    _ = (2*(2^n*n.factorial))^n := by simp only [mul_pow];ring
    _ ≤ (n^n)^n := Nat.pow_le_pow_left (factorial_room hn) n
    _ = _ := by rw [←pow_mul,pow_two]

/-- The upper-half input count fits even at the small initial sizes. -/
theorem upper_half_fits (n : ℕ) (np : 0<n) : inputCount n ((n+1)/2)≤capacity n := by
  by_cases h : 10≤n
  · have bit : 1≤(2:ℕ)^n := Nat.succ_le_iff.mpr (by positivity)
    exact (by simpa using Nat.mul_le_mul_left (inputCount n ((n+1)/2)) bit :
      inputCount n ((n+1)/2)≤ inputCount n ((n+1)/2)*2^n).trans (upper_half_with_spare h)
  · interval_cases n <;> decide +kernel

#print axioms PALRH.UpperHalfBoard.upper_half_with_spare
#print axioms PALRH.UpperHalfBoard.upper_half_fits
end PALRH.UpperHalfBoard
