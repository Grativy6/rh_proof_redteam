import PALRH.DivisorEconomy

open Finset
open scoped BigOperators
noncomputable section
namespace PALRH.AreaBracket
open DivisorBracket DivisorEconomy LinearPrimeIntegral

private def packet (c : ℕ → ℤ) : ℕ := ∏ j ∈ slots,j^(c j).toNat
private def opposite (c : ℕ → ℤ) (j : ℕ) : ℤ := -c j
private def integerError (c : ℕ → ℤ) : ℤ := ∑ j ∈ slots, 3*j*|c j|

private theorem packet_pos (c : ℕ → ℤ) : 0 < packet c := by
  apply Finset.prod_pos
  intro j hj
  exact pow_pos (Finset.mem_Icc.mp hj).1 _

private theorem logs (c : ℕ → ℤ) :
    coefficient c = Real.log (packet c:ℝ)-Real.log (packet (opposite c):ℝ) := by
  have posSum (b : ℕ → ℤ) :
      Real.log (packet b:ℝ)=∑ j ∈ slots, ((b j).toNat:ℝ)*Real.log j := by
    unfold packet
    push_cast
    rw [Real.log_prod]
    · simp only [Real.log_pow]
    · intro j hj
      exact pow_ne_zero _ (by exact_mod_cast (show 0<j from (mem_Icc.mp hj).1).ne')
  rw [posSum,posSum,←sum_sub_distrib]
  apply sum_congr rfl
  intro j _
  have z : (((c j).toNat:ℝ)-((opposite c j).toNat:ℝ))=(c j:ℝ) := by
    unfold opposite
    exact_mod_cast (show ((c j).toNat:ℤ)-((-c j).toNat:ℤ)=c j by omega)
  rw [←sub_mul,z]

private theorem error_cast (c : ℕ → ℤ) : priceError c = (integerError c:ℝ) := by
  unfold priceError integerError
  push_cast
  rfl

private theorem upper_arithmetic :
    (packet (opposite upper))^64 ≤ 2^9490*(packet upper)^64 ∧ integerError upper=2724 := by
  decide +kernel

private theorem lower_arithmetic :
    2^18142*(packet (opposite lower))^64 ≤ (packet lower)^64 ∧ integerError lower=5118 := by
  decide +kernel

theorem upper_coefficient : -(coefficient upper)/2 ≤ 102*(63/125:ℝ) := by
  have pp : (0:ℝ)<(packet upper:ℝ) := by exact_mod_cast packet_pos upper
  have pn : (0:ℝ)<(packet (opposite upper):ℝ) := by exact_mod_cast packet_pos (opposite upper)
  have order : (packet (opposite upper):ℝ)^64 ≤ (2:ℝ)^9490*(packet upper:ℝ)^64 := by
    exact_mod_cast upper_arithmetic.1
  have game := Real.log_le_log (pow_pos pn 64) order
  rw [Real.log_mul (by positivity) (by positivity)] at game
  simp only [Real.log_pow,Nat.cast_ofNat] at game
  rw [logs]
  linarith only [game,Real.log_two_lt_d9.le]

theorem lower_coefficient : 198*(62/125:ℝ) ≤ coefficient lower/2 := by
  have pp : (0:ℝ)<(packet lower:ℝ) := by exact_mod_cast packet_pos lower
  have pn : (0:ℝ)<(packet (opposite lower):ℝ) := by exact_mod_cast packet_pos (opposite lower)
  have order : (2:ℝ)^18142*(packet (opposite lower):ℝ)^64 ≤ (packet lower:ℝ)^64 := by
    exact_mod_cast lower_arithmetic.1
  have game := Real.log_le_log (show 0 < (2:ℝ)^18142*(packet (opposite lower):ℝ)^64 by positivity) order
  rw [Real.log_mul (by positivity) (by positivity)] at game
  simp only [Real.log_pow,Nat.cast_ofNat] at game
  rw [logs]
  linarith only [game,Real.log_two_gt_d9.le]

/-- A uniform two-sided price on the genuine integrated prime-power sum.
The proof uses sixteen signed integer rows and only elementary logarithmic estimates. -/
theorem raw_box {n : ℕ} (large : 16 ≤ n) :
    (62/125:ℝ)*(n:ℝ)^2-32*n*Real.log ((n:ℝ)+1) ≤ fullWalk n ∧
    fullWalk n ≤ (63/125:ℝ)*(n:ℝ)^2+32*n*Real.log ((n:ℝ)+1) := by
  have one := mixture_price upper upper_data.1 large
  have two := mixture_price lower lower_data.1 large
  rw [error_cast,upper_arithmetic.2,abs_le] at one
  rw [error_cast,lower_arithmetic.2,abs_le] at two
  norm_num only [Int.cast_ofNat] at one two
  have cap := mul_le_mul_of_nonneg_right upper_coefficient (sq_nonneg (n:ℝ))
  have floor := mul_le_mul_of_nonneg_right lower_coefficient (sq_nonneg (n:ℝ))
  have lp : 0 ≤ (n:ℝ)*Real.log ((n:ℝ)+1) :=
    mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by linarith only [Nat.cast_nonneg (α:=ℝ) n]))
  constructor
  · nlinarith only [lower_all n,two.2,floor,lp]
  · nlinarith only [upper_all n,one.2,cap,lp]

#print axioms PALRH.AreaBracket.upper_coefficient
#print axioms PALRH.AreaBracket.lower_coefficient
#print axioms PALRH.AreaBracket.raw_box
end PALRH.AreaBracket
