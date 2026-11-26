import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.LSeries.RiemannZeta

open Finset
open scoped BigOperators

/-- Sum the ordinary arithmetic marks against the one-sided linear ramp at 2*j^4. -/
def fixedPrimitive (j : ℕ) : ℚ :=
  let T:=2*j^4
  let L:=Nat.log 2 (j^4)+1
  ∑ i ∈ Finset.range (L+1), ∑ k ∈ Finset.range (L+1),
    let v : ℕ:=2^i*3^k
    ∑ d ∈ Finset.Icc 1 T, if d.Coprime 6 then
      (ArithmeticFunction.moebius d:ℚ)*v*max 0 ((T:ℚ)/((d:ℚ)*v^2)-1)
      else 0

/-- Fixed conditional statement in a stock Mathlib environment. -/
theorem primitiveFourthReduction (signs : ∃ B : ℕ, ∀ j : ℕ, B≤j → 0≤fixedPrimitive j) :
    RiemannHypothesis := by sorry
