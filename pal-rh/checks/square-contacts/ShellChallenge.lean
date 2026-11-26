import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.LSeries.RiemannZeta

open Finset
open scoped BigOperators

def fixedRunningMass (n : ℕ) : ℤ :=
  let L:=Nat.log 2 n+1
  ∑ i ∈ Finset.range (L+1), ∑ j ∈ Finset.range (L+1),
    let v : ℕ:=2^i*3^j
    (v:ℤ)*∑ d ∈ Finset.Icc 1 (n/v^2), if d.Coprime 6 then ArithmeticFunction.moebius d else 0

theorem squareHeadReduction (h : ∃ K : ℕ, ∀ j : ℕ, 0<j →
    fixedRunningMass (j^2)≤(K:ℤ)*j) : RiemannHypothesis := by sorry

theorem squareContactReduction (h : ∃ K : ℕ, ∀ j : ℕ, 0<j → ∃ n : ℕ,
    j^2≤n ∧ n<(j+1)^2 ∧ fixedRunningMass n≤(K:ℤ)*j) : RiemannHypothesis := by sorry
