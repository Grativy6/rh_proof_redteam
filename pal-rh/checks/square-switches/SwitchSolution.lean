import PALRH.RulerBalance

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
  exact PALRH.SquareCarry.balanced_energy ha n

theorem signedMaterial {n : ℕ} (hn : 0<n) :
    (∑ j ∈ Icc 1 n, traceCount j*(ruler n j-ruler n (j+1)))=ink n 1 := by
  exact PALRH.RulerBalance.signed_balance hn

theorem inverseSigns {u : ℕ → ℤ} (legal : allowedSwitches u) (n : ℕ) :
    (∑ a ∈ Icc 1 n, ArithmeticFunction.moebius a*u a*markedWalk u (n/a^2))=traceCount n := by
  have restored:=PALRH.ColoredSquares.recover legal n
  have cast : ((traceCount n):ℝ)=PALRH.Octaves.walk n := by simp [traceCount,PALRH.Octaves.walk]
  rw [←cast] at restored
  change (∑ a ∈ Icc 1 n, ArithmeticFunction.moebius a*u a*PALRH.ColoredSquares.reading u (n/a^2))=traceCount n
  exact_mod_cast restored

theorem flexibleSquareReturns (paid : ∀ q : ℕ, 0<q → ∃ K : ℕ, ∀ n : ℕ, K≤n →
    ∃ a : ℕ, 2≤a ∧ ∃ c : ℤ, c.natAbs≤a ∧
      (traceCount n-c*traceCount (n/a^2)).natAbs^(2*q)≤n^(q+1)) : RiemannHypothesis := by
  exact PALRH.SquareCarry.rh_of_square_returns paid

theorem riemannHypothesis (paid : ∀ b : ℝ, 1/2<b → ∃ C : ℝ, 0≤C ∧ ∀ n : ℕ,
    ∃ u : ℕ → ℤ, allowedSwitches u ∧ ∀ m≤n, |(markedWalk u m:ℝ)|≤C*(m:ℝ)^b) : RiemannHypothesis := by
  exact PALRH.ColoredSquares.rh_of_switches paid

#print axioms squareEnergy
#print axioms signedMaterial
#print axioms inverseSigns
#print axioms flexibleSquareReturns
#print axioms riemannHypothesis
