import PALRH.PascalBoard
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

open Finset
open scoped BigOperators

namespace PALRH.PascalInventory

/-- The recovered tail of the target ramp at height 1/d after Möbius inversion. -/
def requiredAt (d : ℕ) : ℚ :=
  (∑ k ∈ Icc 1 d, (ArithmeticFunction.moebius k : ℚ)*(((d:ℚ)^2/k)-(k:ℚ)))/2

theorem fifth_mark :
    (∑ k ∈ Icc 1 5, (ArithmeticFunction.moebius k : ℚ)/k)= -1/30 ∧
    requiredAt 6=39/10 ∧ requiredAt 5=49/12 := by decide +kernel

def above {ι : Type*} (rows : Finset ι) (size mass : ι → ℚ) (y : ℚ) :=
  ∑ i ∈ rows, if y≤size i then mass i else 0

theorem positive_tail_decreases {ι : Type*} (rows : Finset ι) (size mass : ι → ℚ)
    (pos : ∀ i ∈ rows, 0≤mass i) : Antitone (above rows size mass) := by
  intro lower upper order
  apply Finset.sum_le_sum
  intro i hi
  by_cases allowed : upper≤size i
  · simp [allowed,order.trans allowed]
  · simp only [allowed,if_false]
    split_ifs
    · exact pos i hi
    · exact le_rfl

/-- These two target readings cannot both be supplied by a nonnegative row inventory. -/
theorem incompatible_readings {ι : Type*} (rows : Finset ι) (size mass : ι → ℚ)
    (pos : ∀ i ∈ rows, 0≤mass i) :
    ¬(above rows size mass (1/6)=requiredAt 6 ∧ above rows size mass (1/5)=requiredAt 5) := by
  rintro ⟨low,high⟩
  have necessary:=positive_tail_decreases rows size mass pos (by norm_num : (1/6:ℚ)≤1/5)
  rw [high,low,fifth_mark.2.2,fifth_mark.2.1] at necessary
  norm_num at necessary

#print axioms PALRH.PascalInventory.fifth_mark
#print axioms PALRH.PascalInventory.incompatible_readings
end PALRH.PascalInventory
