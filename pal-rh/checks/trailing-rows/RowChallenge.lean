import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.LSeries.RiemannZeta

open Finset
open scoped BigOperators

def fixedRunningMass (n : ℕ) : ℤ :=
  let L:=Nat.log 2 n+1
  ∑ i ∈ Finset.range (L+1), ∑ j ∈ Finset.range (L+1),
    let v : ℕ:=2^i*3^j
    (v:ℤ)*∑ d ∈ Finset.Icc 1 (n/v^2), if d.Coprime 6 then ArithmeticFunction.moebius d else 0

def trailingPrice (m n : ℕ) : ℤ :=
  ∑ k ∈ Finset.Ico m n, (fixedRunningMass n-fixedRunningMass k)

theorem adaptiveRowReduction (h : ∃ K : ℕ, ∀ n : ℕ, 0<n → ∃ m<n,
    (n:ℤ)*(max 0 (trailingPrice m n))^2 ≤ (K:ℤ)*(((n-m)*(n-m+1):ℕ):ℤ)^2) :
    RiemannHypothesis := by sorry

theorem nonpositiveRowReduction (h : ∃ B : ℕ, ∀ n : ℕ, B≤n → 0<n →
    ∃ m<n, trailingPrice m n≤0) : RiemannHypothesis := by sorry
