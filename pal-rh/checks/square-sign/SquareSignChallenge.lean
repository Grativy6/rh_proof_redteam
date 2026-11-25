import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.LSeries.RiemannZeta

open Finset
open scoped BigOperators

/-- At the physical fourth power, take the ordinary Mobius marks coprime to six,
multiply their indices by the two squares and taper them on the same head. -/
def fixedFourthSignValue (j : ℕ) : ℚ :=
  let H:=j^4
  let L:=Nat.log 2 H+1
  ∑ a ∈ Finset.range (L+1), ∑ b ∈ Finset.range (L+1),
    ∑ d ∈ Finset.Icc 1 (2*H), if d.Coprime 6 then
      (ArithmeticFunction.moebius d:ℚ)/(d*(2^a*3^b:ℕ))*
        max 0 (min 1 (2-((d*(2^a*3^b)^2:ℕ):ℚ)/H)) else 0

/- Standalone reference for a conditional fixed statement. -/
theorem firstPassFourthReduction (signs : ∃ B : ℕ, ∀ j : ℕ, B≤j → 0≤fixedFourthSignValue j) :
    RiemannHypothesis := by sorry
