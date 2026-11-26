import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.LSeries.RiemannZeta

open Finset
open scoped BigOperators

def fixedEvenEnergy (endLabel d : ℕ) : ℚ :=
  if d≤endLabel then
    ((endLabel%d:ℕ):ℚ)^2*((d:ℚ)-(endLabel%d:ℕ))^2/(4*d*(endLabel:ℚ)^2)
  else 0

def fixedEvenSource (T N : ℕ) : ℚ :=
  (T:ℚ)*∑ a ∈ Finset.range (N+1), ∑ b ∈ Finset.range (N+1),
    let p : ℕ:=2^a*3^b
    (p:ℚ)*∑ n ∈ Finset.Icc 1 T,
      if n=3^(Nat.log 3 n) then (max 0 (1-((n*p^2:ℕ):ℚ)/T))^3 else 0

/-- Squared circular remainders on one physical interval near a fourth power. -/
def fixedEvenWindow (j : ℕ) : ℚ :=
  let H:=j^4
  let S:=2*H
  let T:=2*(H+j^2)
  let N:=Nat.log 2 (H+j^2)+1
  fixedEvenSource T N-fixedEvenSource S N+
    ∑ a ∈ Finset.range (N+1), ∑ b ∈ Finset.range (N+1),
      let p : ℕ:=2^a*3^b
      (p:ℚ)*∑ d ∈ Finset.Icc 1 T,
        let k:=d*p^2
        if j^10<k^3 ∧ d.Coprime 6 then (ArithmeticFunction.moebius d:ℚ)*
          ((fixedEvenEnergy T k-fixedEvenEnergy S k)-
           (fixedEvenEnergy T (2*k)-fixedEvenEnergy S (2*k))) else 0

/- Isolated reference environment for the fixed conditional statement. -/
theorem evenRemainderReduction (funded : ∃ B : ℕ, ∀ j : ℕ, B≤j → 0≤fixedEvenWindow j) :
    RiemannHypothesis := by sorry
