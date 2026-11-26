import PALRH.PascalCarry
import PALRH.PascalInventory

open Finset
open scoped BigOperators

def pascalStates (n : ℕ) := ∏ a ∈ range (n+1),n.choose a
def oneDirection (n : ℕ) :=
  ∏ p ∈ ((Icc 1 n).filter Nat.Prime).filter (fun p => n.sqrt<p),p^(n-p)

theorem twoFamiliesFit (n : ℕ) : n.factorial^n*(pascalStates n)^2≤n^(n^2) := PALRH.PascalBoard.two_pascal_rows_fit n

theorem samePrimeDigitsFit (n : ℕ) : n.factorial^n*((oneDirection n).gcd (pascalStates n))^2≤n^(n^2) := PALRH.PascalBoard.registered_digits_fit n

theorem capacityAtOnePrime {n p : ℕ} (prime : p.Prime) (large : n<p^2) :
    (pascalStates n).factorization p=(n/p)*(p-1-n%p) := PALRH.PascalCarry.digit_count prime large

set_option maxRecDepth 24000 in
theorem firstSixteenLedger : oneDirection 16/((oneDirection 16).gcd (pascalStates 16))=175 := by decide +kernel

theorem whatRemainsIsCoprime (n : ℕ) :
    let common := (oneDirection n).gcd (pascalStates n)
    Nat.Coprime (oneDirection n/common) (pascalStates n/common) := PALRH.PascalCarry.leftovers_coprime n

theorem leftoverComparisonPays (n : ℕ)
    (h : oneDirection n/((oneDirection n).gcd (pascalStates n)) ≤
         pascalStates n/((oneDirection n).gcd (pascalStates n))) :
    n.factorial^n*(oneDirection n)^2≤n^(n^2) := by
  have a:=PALRH.PascalCarry.exchange_iff n |>.mp h
  exact (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left a 2)).trans (PALRH.PascalBoard.two_pascal_rows_fit n)

theorem positiveRowsDoNotGainAboveACut {ι : Type} (rows : Finset ι) (size mass : ι → ℚ)
    (pos : ∀ i ∈ rows, 0≤mass i) :
    ¬ ((∑ i ∈ rows, if (1/6:ℚ)≤size i then mass i else 0)=39/10 ∧
       (∑ i ∈ rows, if (1/5:ℚ)≤size i then mass i else 0)=49/12) := by
  have h:=PALRH.PascalInventory.incompatible_readings rows size mass pos
  simpa only [PALRH.PascalInventory.above,PALRH.PascalInventory.fifth_mark.2.1,
    PALRH.PascalInventory.fifth_mark.2.2] using h

#print axioms twoFamiliesFit
#print axioms samePrimeDigitsFit
#print axioms capacityAtOnePrime
#print axioms firstSixteenLedger
#print axioms whatRemainsIsCoprime
#print axioms leftoverComparisonPays
#print axioms positiveRowsDoNotGainAboveACut
