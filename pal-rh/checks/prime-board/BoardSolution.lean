import PALRH.PrimeBoard

open Finset
open scoped BigOperators

def boardDials (n : ℕ) := ∏ p ∈ (Icc 1 n).filter Nat.Prime, p^(2*(n-p))
def boardDemand (n : ℕ) := n.factorial^n*boardDials n
def boardSpace (n : ℕ) := n^(n^2)
def binaryRoom (n : ℕ) := 2^(4*n*(n.sqrt+1))
def twoCellRemainder (n : ℕ) := ∏ p ∈ (Icc 1 n).filter Nat.Prime, (n^2/p)^(2*(n-p))
def twoCellSpace (n : ℕ) := ∏ p ∈ (Icc 1 n).filter Nat.Prime, (n^2)^(2*(n-p))

theorem integerBoardReduction (h : ∀ n : ℕ, 0<n →
    boardDemand n≤boardSpace n ∧ boardSpace n≤boardDemand n*binaryRoom n) : RiemannHypothesis :=
  PALRH.PrimeBoard.rh_of_integer_board h

theorem pairedBoardReduction (h : ∀ n : ℕ, 0<n →
    n.factorial^n*twoCellSpace n≤boardSpace n*twoCellRemainder n ∧
    boardSpace n≤boardDemand n*binaryRoom n) : RiemannHypothesis :=
  PALRH.PrimeBoard.rh_of_paired_board h

#print axioms integerBoardReduction
#print axioms pairedBoardReduction
