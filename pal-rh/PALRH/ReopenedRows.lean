import PALRH.DivisorBracket

open Finset
open scoped BigOperators
namespace PALRH.ReopenedRows
open DivisorBracket

/-- The exact area remaining at label j's multiples, in the units of the dividend k. -/
def triangle (j k : ℕ) : ℚ :=
  ((2:ℚ)*k*(k/j:ℕ)-j*(k/j:ℕ)*((k/j:ℕ)+1))/2

def shapeError (a : ℕ → ℚ) (M k : ℕ) : ℚ :=
  ((∑ j ∈ Icc 1 M, a j*triangle j k) - (k-1:ℕ)) / k

/-- Integral of an affine error over reciprocal cells 1/(K+1) through 1. -/
def prefixArea (a : ℕ → ℚ) (M K : ℕ) : ℚ :=
  ∑ k ∈ Icc 1 K, (shapeError a M k+shapeError a M (k+1))*(1/(k:ℚ)-1/((k:ℚ)+1))/2

def firstUpper (j : ℕ) : ℚ := (j:ℚ)*(upper j:ℤ)/102

private theorem unseen {j k : ℕ} (jp : 0<j) (bound : k≤j) : triangle j k=0 := by
  rcases eq_or_lt_of_le bound with e|before
  · subst k; simp [triangle,Nat.div_self jp]; ring
  · simp [triangle,Nat.div_eq_of_lt before]

theorem frozen_address {a b : ℕ → ℚ} {M L k : ℕ} (extend : M≤L) (visible : k≤M+1)
    (agree : ∀ j ∈ Icc 1 M, a j=b j) :
    shapeError b L k=shapeError a M k := by
  unfold shapeError
  have keep : (∑ j ∈ Icc 1 M,b j*triangle j k)=(∑ j ∈ Icc 1 L,b j*triangle j k) := by
    apply sum_subset (fun j hj => mem_Icc.mpr ⟨(mem_Icc.mp hj).1,(mem_Icc.mp hj).2.trans extend⟩)
    intro j hj outside
    have pos := (mem_Icc.mp hj).1
    have later : M<j := by by_contra! h;exact outside (mem_Icc.mpr ⟨pos,h⟩)
    rw [unseen pos (by omega),mul_zero]
  rw [←keep, sum_congr rfl (fun j hj => by rw [←agree j hj])]

theorem frozen_area {a b : ℕ → ℚ} {M L : ℕ} (extend : M≤L)
    (agree : ∀ j ∈ Icc 1 M,a j=b j) : prefixArea b L M=prefixArea a M M := by
  apply sum_congr rfl
  intro k hk
  have within := (mem_Icc.mp hk).2
  rw [frozen_address extend (by omega : k≤M+1) agree,
      frozen_address extend (by omega : k+1≤M+1) agree]

theorem old_price : prefixArea firstUpper 16 16=1568059/885224340 := by decide +kernel

/-- Later labels cannot reduce this part of the positive area at all. -/
theorem permanent_first_cost {b : ℕ → ℚ} {L : ℕ} (extend : 16≤L)
    (agree : ∀ j ∈ Icc 1 16,firstUpper j=b j) :
    prefixArea b L 16=1568059/885224340 := (frozen_area extend agree).trans old_price

#print axioms PALRH.ReopenedRows.frozen_area
#print axioms PALRH.ReopenedRows.permanent_first_cost
end PALRH.ReopenedRows
