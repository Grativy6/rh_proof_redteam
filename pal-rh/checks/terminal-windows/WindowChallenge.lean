import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.LSeries.RiemannZeta

open Finset
open scoped BigOperators

def fixedRunningMass (n : ℕ) : ℤ :=
  let L:=Nat.log 2 n+1
  ∑ i ∈ Finset.range (L+1), ∑ j ∈ Finset.range (L+1),
    let v : ℕ:=2^i*3^j
    (v:ℤ)*∑ d ∈ Finset.Icc 1 (n/v^2), if d.Coprime 6 then ArithmeticFunction.moebius d else 0

def halfRise (n : ℕ) : ℤ := fixedRunningMass n - fixedRunningMass (n/2)

def mixedRise (n : ℕ) : ℤ := halfRise n - halfRise (n/3)

theorem halfWindowReduction (h : ∃ K : ℕ, ∀ n : ℕ, (max 0 (halfRise n))^2 ≤ (K:ℤ)*n) :
    RiemannHypothesis := by sorry

theorem mixedWindowReduction (h : ∃ K : ℕ, ∀ n : ℕ, (max 0 (mixedRise n))^2 ≤ (K:ℤ)*n) :
    RiemannHypothesis := by sorry
