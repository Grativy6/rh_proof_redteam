import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.LSeries.RiemannZeta

open Finset
open scoped BigOperators

/-- The price is specified directly by an ordinary Möbius sum on the first 2H indices. -/
def fixedAreaPrice (H : ℕ) : ℚ :=
  ∑ n ∈ Finset.Icc 1 (2*H), if n.Coprime 6 then
    (ArithmeticFunction.moebius n:ℚ)/n*
      (if n≤H then 1 else ((2*H-n:ℕ):ℚ)/H) else 0

def fixedAreaCount (positive : Bool) (J : ℕ) : ℚ :=
  ∑ j ∈ Finset.Icc 1 J, (j:ℚ)*max (if positive then fixedAreaPrice (j^4) else -fixedAreaPrice (j^4)) 0

/- Separate reference environment for the fixed conditional challenge. -/
theorem fourthPowerAreaReduction
    (small : ∀ k : ℕ, 0<k → ∀ B : ℕ, ∃ J : ℕ, B≤J ∧
      ∃ positive : Bool, (fixedAreaCount positive J)^k≤(J:ℚ)) : RiemannHypothesis := by sorry
