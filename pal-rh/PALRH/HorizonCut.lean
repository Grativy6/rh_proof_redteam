import PALRH.UpperHalfBoard
import Mathlib.Data.Nat.Find

open Finset
open scoped BigOperators

namespace PALRH.HorizonCut
open PrimeBoard PrimeBand

/-- A label is counted only when the declared test admits it and its distance exceeds the cut. -/
def records (n : ℕ) (tag : ℕ → Bool) (c : ℕ) : ℕ :=
  n.factorial^n * ∏ m ∈ Icc 2 n, if tag m = true ∧ c<m then m^(2*(n-m)) else 1

theorem fewer_labels {c d : ℕ} (cd : c≤d) (n : ℕ) (tag : ℕ → Bool) :
    records n tag d ≤ records n tag c := by
  unfold records
  apply Nat.mul_le_mul_left
  apply Finset.prod_le_prod'
  intro m hm
  have pos : 0<m := by have := (mem_Icc.mp hm).1; omega
  split_ifs with hd hc hc
  · exact le_rfl
  · exact False.elim (hc ⟨hd.1,cd.trans_lt hd.2⟩)
  · exact Nat.succ_le_iff.mpr (pow_pos pos _)
  · exact le_rfl

private theorem some_cut (n : ℕ) (tag : ℕ → Bool) : ∃ c, records n tag c≤capacity n := by
  refine ⟨n,?_⟩
  have endRow : (∏ m ∈ Icc 2 n, if tag m = true ∧ n<m then m^(2*(n-m)) else 1)=1 := by
    apply Finset.prod_eq_one
    intro m hm
    simp [not_lt.mpr (mem_Icc.mp hm).2]
  unfold records capacity
  rw [endRow,mul_one,show n^2=n*n by ring,pow_mul]
  exact Nat.pow_le_pow_left (Nat.factorial_le_pow n) _

noncomputable def boundary (n : ℕ) (tag : ℕ → Bool) := Nat.find (some_cut n tag)

/-- One number retains the outcome of every cut at this size. -/
theorem read_boundary {n c : ℕ} (tag : ℕ → Bool) :
    boundary n tag≤c ↔ records n tag c≤capacity n :=
  ⟨fun h => (fewer_labels h n tag).trans (Nat.find_spec (some_cut n tag)),
   fun h => Nat.find_min' (some_cut n tag) h⟩

private theorem inactive_step (n c : ℕ) (tag : ℕ → Bool) (off : tag (c+1)=false) :
    records n tag c=records n tag (c+1) := by
  unfold records
  congr 1
  apply Finset.prod_congr rfl
  intro m _
  by_cases hm : m=c+1
  · subst m;simp [off]
  · have same : c<m ↔ c+1<m := by omega
    simp only [same]

theorem boundary_tag (n : ℕ) (tag : ℕ → Bool) :
    boundary n tag=0 ∨ tag (boundary n tag)=true := by
  cases h : boundary n tag with
  | zero => exact Or.inl rfl
  | succ c =>
    right
    by_contra off
    have absent : tag (c+1)=false := by cases heq : tag (c+1) <;> simp_all
    have yes : records n tag (c+1)≤capacity n := (read_boundary tag).mp h.le
    rw [←inactive_step n c tag absent] at yes
    have before:=(read_boundary tag).mpr yes
    omega

def primeTag (m : ℕ) : Bool := decide m.Prime

theorem prime_record (n c : ℕ) : records n primeTag c=inputCount n c := by
  have sets : (Icc 2 n).filter (fun p => primeTag p=true ∧ c<p) = (primes n).filter (fun p => c<p) := by
    ext p
    simp only [mem_filter,mem_Icc,primes,primeTag,decide_eq_true_eq]
    constructor
    · rintro ⟨⟨_,endp⟩,pr,above⟩
      exact ⟨⟨⟨pr.pos,endp⟩,pr⟩,above⟩
    · rintro ⟨⟨⟨_,endp⟩,pr⟩,above⟩
      exact ⟨⟨pr.two_le,endp⟩,pr,above⟩
  unfold records inputCount retained
  rw [←Finset.prod_filter,sets]

theorem zero_or_prime (n : ℕ) : boundary n primeTag=0 ∨ (boundary n primeTag).Prime := by
  simpa [primeTag] using boundary_tag n primeTag

theorem upper_half_boundary {n : ℕ} (np : 0<n) : boundary n primeTag≤(n+1)/2 := by
  apply (read_boundary primeTag).mpr
  rw [prime_record]
  exact UpperHalfBoard.upper_half_fits n np

def missingFive (m : ℕ) : Bool := decide (m.gcd 6006=1)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 1500000 in
theorem first_repair_is_five : boundary 256 missingFive=5 := by
  have accepts : records 256 missingFive 5≤capacity 256 := by decide +kernel
  have rejects : ¬records 256 missingFive 4≤capacity 256 := by decide +kernel
  have yes:=(read_boundary missingFive).mpr accepts
  have no : ¬boundary 256 missingFive≤4 := fun h => rejects ((read_boundary missingFive).mp h)
  omega

#print axioms PALRH.HorizonCut.read_boundary
#print axioms PALRH.HorizonCut.zero_or_prime
#print axioms PALRH.HorizonCut.upper_half_boundary
#print axioms PALRH.HorizonCut.first_repair_is_five
end PALRH.HorizonCut
