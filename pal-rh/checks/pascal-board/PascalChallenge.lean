import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Rat.Defs

open Finset
open scoped BigOperators

def pascalStates (n : ℕ) := ∏ a ∈ range (n+1),n.choose a
def oneDirection (n : ℕ) :=
  ∏ p ∈ ((Icc 1 n).filter Nat.Prime).filter (fun p => n.sqrt<p),p^(n-p)

theorem twoFamiliesFit (n : ℕ) : n.factorial^n*(pascalStates n)^2≤n^(n^2) := by sorry

theorem samePrimeDigitsFit (n : ℕ) : n.factorial^n*((oneDirection n).gcd (pascalStates n))^2≤n^(n^2) := by sorry

theorem capacityAtOnePrime {n p : ℕ} (prime : p.Prime) (large : n<p^2) :
    (pascalStates n).factorization p=(n/p)*(p-1-n%p) := by sorry

theorem firstSixteenLedger : oneDirection 16/((oneDirection 16).gcd (pascalStates 16))=175 := by sorry

theorem whatRemainsIsCoprime (n : ℕ) :
    let common := (oneDirection n).gcd (pascalStates n)
    Nat.Coprime (oneDirection n/common) (pascalStates n/common) := by sorry

theorem leftoverComparisonPays (n : ℕ)
    (h : oneDirection n/((oneDirection n).gcd (pascalStates n)) ≤
         pascalStates n/((oneDirection n).gcd (pascalStates n))) :
    n.factorial^n*(oneDirection n)^2≤n^(n^2) := by sorry

theorem positiveRowsDoNotGainAboveACut {ι : Type} (rows : Finset ι) (size mass : ι → ℚ)
    (pos : ∀ i ∈ rows, 0≤mass i) :
    ¬ ((∑ i ∈ rows, if (1/6:ℚ)≤size i then mass i else 0)=39/10 ∧
       (∑ i ∈ rows, if (1/5:ℚ)≤size i then mass i else 0)=49/12) := by sorry
