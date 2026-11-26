import PALRH.UpperHalfBoard

open Finset
open scoped BigOperators

def relPrimeRecords (n f : ℕ) := n.factorial^n *
  ∏ m ∈ Icc 2 n, if m.gcd f=1 then m^(2*(n-m)) else 1

def upperRecords (n : ℕ) := n.factorial^n *
  ∏ p ∈ ((Icc 1 n).filter Nat.Prime).filter (fun p => (n+1)/2<p), p^(2*(n-p))

theorem fourthPowersFromGCD (h : ∀ k : ℕ, 0<k →
    relPrimeRecords (k^4) (k^2).factorial ≤ (k^4)^((k^4)^2) ∧
    (k^4)^((k^4)^2) ≤ relPrimeRecords (k^4) (k^2).factorial*2^(8*k^4*(k^2+1))) :
    RiemannHypothesis := by
  exact PALRH.SieveFrame.rh_of_factorial_frame h

set_option maxRecDepth 24000 in
set_option maxHeartbeats 1500000 in
theorem forgettingFive :
    relPrimeRecords 256 30030 ≤ 256^(256^2) ∧
    256^(256^2) < relPrimeRecords 256 6006 := by
  decide +kernel

theorem allUpperHalfRecords (n : ℕ) (np : 0<n) : upperRecords n≤n^(n^2) := by
  exact PALRH.UpperHalfBoard.upper_half_fits n np

#print axioms fourthPowersFromGCD
#print axioms forgettingFive
#print axioms allUpperHalfRecords
