import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Algebra.BigOperators.Intervals

open Finset
open scoped BigOperators

def keptRecords (n : ℕ) (tag : ℕ → Bool) (c : ℕ) := n.factorial^n *
  ∏ m ∈ Icc 2 n, if tag m = true ∧ c<m then m^(2*(n-m)) else 1

theorem everyCutFromOneNumber (n : ℕ) (tag : ℕ → Bool) : ∃ c : ℕ,
    (c=0 ∨ tag c=true) ∧ ∀ d : ℕ, c≤d ↔ keptRecords n tag d≤n^(n^2) := by sorry

theorem fiveRepairsCapacity :
    let marks := fun m : ℕ => decide (m.gcd 6006=1)
    keptRecords 256 marks 5≤256^(256^2) ∧ 256^(256^2)<keptRecords 256 marks 4 := by sorry

theorem primeOrProduct {c m n : ℕ} (lo : 2≤m) (hi : m≤n) (cube : n<(c+1)^3) :
    m.Coprime c.factorial ↔ (m.Prime ∧ c<m) ∨
      ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ c<p ∧ p≤q ∧ m=p*q := by sorry

theorem stackedTriangle (t : ℕ) : 6*(∑ j ∈ range t,(j+1)*(t-j))=t*(t+1)*(t+2) := by sorry
