import PALRH.AlignedHits

open Finset
open scoped BigOperators

def returnedNumerator (n d : ℕ) : ℤ :=
  (∑ j ∈ Icc 1 (2*n/d), (((2*n:ℕ):ℤ)-(d*j:ℕ))^5 *
    (7*((d*j:ℕ):ℤ)-(2*n:ℕ))) - ((2*n:ℕ):ℤ)^5 * (n-d:ℕ)

def primeDials (n : ℕ) : ℕ :=
  ∏ d ∈ Icc 1 (2*n), if d.Prime ∧ n^7 < d^8 then d^(returnedNumerator n d).toNat else 1

def cellTicks (k : ℕ) : ℕ := (2*k^4)^5 * k^4 * (k^4-k^2)^2

theorem rhOfSubpowerHits
    (hits : ∀ q : ℕ, 0<q → ∃ K : ℕ, ∀ k : ℕ, K≤k →
      ∃ j : ℕ, k≤j ∧ (j-k)^q≤k ∧
        (j^4+1)^cellTicks j ≤ (j^4)^cellTicks j * (primeDials (j^4))^14) :
    RiemannHypothesis := by
  exact PALRH.GapClock.rh_of_subpower_hits hits

#print axioms rhOfSubpowerHits

def fullyDivisible (k : ℕ) : Prop := ∀ m : ℕ, m.factorial^m ≤ k → m.factorial ∣ k

theorem framesAreNear :
    ∀ q : ℕ, 0<q → ∃ K : ℕ, ∀ k : ℕ, K≤k →
      ∃ j : ℕ, k≤j ∧ (j-k)^q≤k ∧ fullyDivisible j := by
  exact PALRH.AlignedHits.aligned_in_windows

theorem riemannHypothesis
    (paid : ∃ K : ℕ, ∀ k : ℕ, K≤k → fullyDivisible k →
       (k^4+1)^cellTicks k ≤ (k^4)^cellTicks k * (primeDials (k^4))^14) :
    RiemannHypothesis := by
  obtain ⟨K,late⟩:=paid
  exact PALRH.AlignedHits.rh_of_aligned K late

#print axioms framesAreNear
#print axioms riemannHypothesis
