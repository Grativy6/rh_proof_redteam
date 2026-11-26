import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Algebra.BigOperators.Intervals

open Finset
open scoped BigOperators

def traceCount (n : ℕ) : ℤ := ∑ j ∈ Icc 1 n, ArithmeticFunction.moebius j

def squareStep (a : ℕ) (n : ℕ) : ℤ :=
  if a^2 ∣ n then (a:ℤ)*ArithmeticFunction.moebius (n/a^2) else 0

def allowedSwitches (u : ℕ → ℤ) : Prop :=
  u 1=1 ∧ (∀ a b : ℕ, u (a*b)=u a*u b) ∧ ∀ a : ℕ, (u a).natAbs≤1

def markedWalk (u : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ a ∈ Icc 1 n, u a*traceCount (n/a^2)

def ink (N m : ℕ) : ℤ := ((N:ℤ)-m)^5*(7*(m:ℤ)-N)
def ruler (N d : ℕ) : ℤ := ∑ j ∈ Icc 1 (N/d), ink N (d*j)

theorem squareEnergy {a : ℕ} (ha : 2≤a) (n : ℕ) :
    (∑ m ∈ Icc 1 (a^2*n), (squareStep a m)^2)=(a:ℤ)^2*∑ m ∈ Icc 1 n, (ArithmeticFunction.moebius m)^2 := by
  sorry

theorem signedMaterial {n : ℕ} (hn : 0<n) :
    (∑ j ∈ Icc 1 n, traceCount j*(ruler n j-ruler n (j+1)))=ink n 1 := by
  sorry

theorem inverseSigns {u : ℕ → ℤ} (legal : allowedSwitches u) (n : ℕ) :
    (∑ a ∈ Icc 1 n, ArithmeticFunction.moebius a*u a*markedWalk u (n/a^2))=traceCount n := by
  sorry

theorem flexibleSquareReturns (paid : ∀ q : ℕ, 0<q → ∃ K : ℕ, ∀ n : ℕ, K≤n →
    ∃ a : ℕ, 2≤a ∧ ∃ c : ℤ, c.natAbs≤a ∧
      (traceCount n-c*traceCount (n/a^2)).natAbs^(2*q)≤n^(q+1)) : RiemannHypothesis := by
  sorry

theorem riemannHypothesis (paid : ∀ b : ℝ, 1/2<b → ∃ C : ℝ, 0≤C ∧ ∀ n : ℕ,
    ∃ u : ℕ → ℤ, allowedSwitches u ∧ ∀ m≤n, |(markedWalk u m:ℝ)|≤C*(m:ℝ)^b) : RiemannHypothesis := by
  sorry
