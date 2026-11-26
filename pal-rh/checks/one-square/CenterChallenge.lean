import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Prime.Defs

open Finset
open scoped BigOperators

def returnedNumerator (n d : ℕ) : ℤ :=
  (∑ j ∈ Icc 1 (2*n/d), (((2*n:ℕ):ℤ)-(d*j:ℕ))^5 *
    (7*((d*j:ℕ):ℤ)-(2*n:ℕ))) - ((2*n:ℕ):ℤ)^5 * (n-d:ℕ)

def primeDials (n : ℕ) : ℕ :=
  ∏ d ∈ Icc 1 (2*n), if d.Prime ∧ n^7 < d^8 then d^(returnedNumerator n d).toNat else 1

def inward (k b : ℕ) : Finset ℕ :=
  ((Icc 1 (b-2)).image (fun t => b^2-t^2)).filter (fun d => 2*k^4<5*d ∧ d≤k^4)

def outward (k b : ℕ) (S : Finset ℕ) : Finset ℕ :=
  ((Icc 1 (k^2)).image (fun t => b^2+t^2)).filter
    (fun d => k^4<d ∧ d≤2*k^4 ∧ ∃ p ∈ S, 1<p ∧ p<d ∧ p ∣ d)

def labels : Finset ℕ := {2,3,5,7,17}

def holes (k b : ℕ) : Finset ℕ := inward k b ∪ outward k b labels

def bill (k b : ℕ) : ℕ :=
  (∑ r ∈ range (2*k^4), r^6) -
    (16*(k^4)^7 + ∑ d ∈ holes k b, (returnedNumerator (k^4) d).toNat)

def covered (k b : ℕ) : Prop :=
  (k^4+1)^(k^4*bill k b) ≤ (k^4)^(k^4*bill k b)*primeDials (k^4)

theorem compositePlaces {k b d : ℕ} (h : d∈holes k b) : 0<d ∧ d≤2*k^4 ∧ ¬d.Prime := by
  sorry

theorem sevenAtEight : outward 8 64 {17}={4097,4352,4420,5185,5321,6596,6800} := by
  sorry

theorem keepSeventeen : outward 2 4 {17}=∅ := by
  sorry

theorem riemannHypothesis (paid : ∃ K : ℕ, ∀ k : ℕ, K≤k →
    ∃ b ∈ Icc (k^2) (k^2+62), covered k b) : RiemannHypothesis := by
  sorry
