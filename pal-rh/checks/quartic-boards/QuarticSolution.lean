import PALRH.QuarticBoards

open Finset
open scoped BigOperators

def primeBoardDemand (n : ℕ) :=
  n.factorial^n * ∏ p ∈ (Icc 1 n).filter Nat.Prime, p^(2*(n-p))

def primeBoardCapacity (n : ℕ) := n^(n^2)
def permittedSpare (n : ℕ) := 2^(4*n*(n.sqrt+1))

def freePairedPlaces (n : ℕ) :=
  ∏ p ∈ (Icc 1 n).filter Nat.Prime, (n^2/p)^(2*(n-p))
def allPairedPlaces (n : ℕ) :=
  ∏ p ∈ (Icc 1 n).filter Nat.Prime, (n^2)^(2*(n-p))

theorem fourthPowerBoards (h : ∀ k : ℕ, 0<k →
    primeBoardDemand (k^4)≤primeBoardCapacity (k^4) ∧
    primeBoardCapacity (k^4)≤primeBoardDemand (k^4)*permittedSpare (k^4)) :
    RiemannHypothesis :=
  PALRH.QuarticBoards.rh_of_quartic_boards h

theorem fourthPowerPairs (h : ∀ k : ℕ, 0<k →
    (k^4).factorial^(k^4)*allPairedPlaces (k^4)≤primeBoardCapacity (k^4)*freePairedPlaces (k^4) ∧
    primeBoardCapacity (k^4)≤primeBoardDemand (k^4)*permittedSpare (k^4)) :
    RiemannHypothesis :=
  PALRH.QuarticBoards.rh_of_quartic_pairs h

#print axioms fourthPowerBoards
#print axioms fourthPowerPairs
