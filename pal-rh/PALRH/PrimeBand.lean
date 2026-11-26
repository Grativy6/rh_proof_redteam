import PALRH.QuarticBoards
import Mathlib.NumberTheory.Primorial

open Finset
open scoped BigOperators Classical

noncomputable section
namespace PALRH.PrimeBand
open PrimeBoard LinearPrimeIntegral QuarticBoards

def retained (n c : ℕ) := ∏ p ∈ (primes n).filter (fun p => c<p), p^(2*(n-p))
def removed (n c : ℕ) := ∏ p ∈ (primes n).filter (fun p => p≤c), p^(2*(n-p))
def inputCount (n c : ℕ) := n.factorial^n * retained n c

theorem exact_split (n c : ℕ) : demand n=inputCount n c*removed n c := by
  have split:=Finset.prod_filter_mul_prod_filter_not (primes n) (fun p => c<p)
    (fun p => p^(2*(n-p)))
  simp only [not_lt] at split
  unfold demand inputCount dials retained removed
  rw [mul_assoc,split]

theorem removed_pos (n c : ℕ) : 0<removed n c := by
  apply Finset.prod_pos
  intro p hp
  exact pow_pos (mem_filter.mp (mem_filter.mp hp).1).2.pos _

/-- Set aside every prime through c; their settings cost at most 4^(2*n*c) states. -/
theorem small_prime_price {n c : ℕ} (within : c≤n) : removed n c≤2^(4*n*c) := by
  have eq : (primes n).filter (fun p => p≤c)=Nat.primesLE c := by
    ext p
    simp only [primes,mem_filter,mem_Icc,Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨_,hp⟩,pc⟩
      exact ⟨pc,hp⟩
    · rintro ⟨pc,hp⟩
      exact ⟨⟨⟨hp.pos,pc.trans within⟩,hp⟩,pc⟩
  unfold removed
  rw [eq]
  calc
    _ ≤ ∏ p ∈ Nat.primesLE c, p^(2*n) := by
      apply Finset.prod_le_prod'
      intro p hp
      exact Nat.pow_le_pow_right (Nat.mem_primesLE.mp hp).2.pos
        (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
    _ = (primorial c)^(2*n) := by rw [Finset.prod_pow,primorial_eq_prod_primesLE]
    _ ≤ (4^c)^(2*n) := Nat.pow_le_pow_left (primorial_le_four_pow c) _
    _ = _ := by
      rw [show (4:ℕ)=2^2 by decide,←pow_mul,←pow_mul]
      congr 1
      ring

theorem full_cost {n c : ℕ} (cut : c≤n.sqrt) :
    inputCount n c≤demand n ∧ demand n≤ inputCount n c*allowance n := by
  have small:=small_prime_price (cut.trans (Nat.sqrt_le_self _))
  have k : 4*n*c≤4*n*(n.sqrt+1) := Nat.mul_le_mul_left _ (by omega)
  have paid : removed n c≤allowance n := small.trans (Nat.pow_le_pow_right (by decide) k)
  rw [exact_split n c]
  constructor
  · simpa using Nat.mul_le_mul_left (inputCount n c) (Nat.succ_le_iff.mpr (removed_pos n c))
  · exact Nat.mul_le_mul_left _ paid

/-- Distinct retained primes beyond the square root cannot own the same positive label. -/
theorem unique_large_prime {n m p q : ℕ} (mp : 0<m) (mn : m≤n)
    (pp : p.Prime) (qp : q.Prime) (pr : n.sqrt<p) (qr : n.sqrt<q)
    (pm : p∣m) (qm : q∣m) : p=q := by
  by_contra distinct
  have divides:=((Nat.coprime_primes pp qp).mpr distinct).mul_dvd_of_dvd_of_dvd pm qm
  have upper:= (Nat.le_of_dvd mp divides).trans mn
  have lower:=Nat.mul_le_mul pr qr
  have outside:=Nat.lt_succ_sqrt n
  omega

theorem large_square_absent {n m p : ℕ} (mp : 0<m) (mn : m≤n) (pr : n.sqrt<p) :
    ¬p^2∣m := by
  intro d
  have h:= (Nat.le_of_dvd mp d).trans mn
  have l:=Nat.sqrt_lt.mp pr
  simp only [pow_two] at h
  omega

/-- All dials through k squared may be omitted at the fourth-power heads. -/
theorem rh_of_large_primes
    (funded : ∀ k : ℕ, 0<k → inputCount (k^4) (k^2)≤capacity (k^4) ∧
      capacity (k^4)≤ inputCount (k^4) (k^2)*(allowance (k^4))^2) : RiemannHypothesis := by
  obtain ⟨C,cn,price⟩:=full_walk_price_with_room
  apply rh_of_full_walk (C:=1984*C+256) (by positivity)
  intro n np
  apply quartic_envelope cn _ np
  intro k
  by_cases kz : k=0
  · subst k;simp [error,fullWalk]
  have kp:=Nat.pos_of_ne_zero kz
  have cut : k^2≤(k^4).sqrt := Nat.le_sqrt.mpr (by rw [show k^2*k^2=k^4 by ring])
  obtain ⟨smaller,larger⟩:=full_cost cut
  obtain ⟨lo,hi⟩:=funded k kp
  have val:=price (k^4) (pow_pos kp _) ⟨larger.trans (Nat.mul_le_mul_right _ lo),
    hi.trans (Nat.mul_le_mul_right _ smaller)⟩
  have root : Real.sqrt ((k:ℝ)^4)=(k:ℝ)^2 := by
    rw [show (k:ℝ)^4=((k:ℝ)^2)^2 by ring,Real.sqrt_sq (by positivity)]
  unfold error
  push_cast at val ⊢
  rw [root] at val
  calc
    _ ≤ _ := val
    _ = _ := by ring

#print axioms PALRH.PrimeBand.small_prime_price
#print axioms PALRH.PrimeBand.unique_large_prime
#print axioms PALRH.PrimeBand.rh_of_large_primes
end PALRH.PrimeBand
