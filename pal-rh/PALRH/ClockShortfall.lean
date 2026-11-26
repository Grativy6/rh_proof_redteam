import PALRH.PrimeCopies
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas

open Finset
open scoped BigOperators
noncomputable section
namespace PALRH.ClockShortfall
open PrimeCopies RulerOmissions QuarticBoards LinearPrimeIntegral DoubledRuler

/-- Log demand per copy, less the actual log return per common denominator. -/
def shortfall (k : ℕ) : ℝ := demand k/14-earned (k^4)

theorem payment_sign {k : ℕ} (kp : 0<k) : pays 14 k ↔ shortfall k≤0 := by
  rw [pays_iff kp]
  unfold shortfall
  norm_num only [Nat.cast_ofNat]
  constructor <;> intro h <;> linarith only [h]

theorem omitted_price :
    ∃ C : ℝ, 0≤C ∧ ∀ k : ℕ, 0<k →
      0≤outlay (k^4)-fullWalk (k^4)-earned (k^4) ∧
      outlay (k^4)-fullWalk (k^4)-earned (k^4) ≤ C*(k:ℝ)^6 := by
  obtain ⟨c,rep⟩:=Chebyshev.psi_sub_theta_le_mul_sqrt
  let b:=max c 0
  have bn : 0≤b := le_max_right _ _
  refine ⟨1+28*b,by positivity,?_⟩
  intro k kp
  let n:=k^4
  let N:=2*n
  let D:=Nat.nthRoot 8 (n^7)
  have np : 0<n := pow_pos kp _
  have nr : (n:ℝ)=(k:ℝ)^4 := by dsimp [n];push_cast;rfl
  have NN : (N:ℝ)=2*(k:ℝ)^4 := by dsimp [N,n];push_cast;rfl
  have Np : 0<(N:ℝ) := by dsimp [N];positivity
  have budget : D^8≤n^7 := Nat.pow_nthRoot_le (Or.inl (by decide))
  have low : D≤n := (Nat.pow_le_pow_iff_left (by decide : 8≠0)).mp
    (budget.trans (Nat.pow_le_pow_right np (by decide : 7≤8)))
  have short : ∀ d : ℕ, d^8≤n^7 → d≤D := fun _ hd => (Nat.le_nthRoot_iff (by decide : 8≠0)).mpr hd
  have fourth : D^4≤k^14 := by
    apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
    calc
      (D^4)^2 = D^8 := by ring
      _ ≤ n^7 := budget
      _ = (k^14)^2 := by dsimp [n];ring
  have all := loss_with_prices (n:=n) (D:=D) (low.trans (by omega)) short
    (fee:=7*(N:ℝ)^6) (shortFee:=(2/3:ℝ)*(D:ℝ)^3*(N:ℝ)^3) (by positivity) (by positivity)
    (fun dp hd => extra_cap dp hd) (fun {d} dp hd => (extra_cubic dp (hd.trans low)).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (Nat.cast_nonneg (α:=ℝ) d) (by exact_mod_cast hd) 3)
        (by norm_num : (0:ℝ)≤2/3)) (by positivity)))
  have square : Real.sqrt (N:ℝ) ≤ 2*(k:ℝ)^2 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    rw [NN]
    nlinarith only [pow_nonneg (Nat.cast_nonneg (α:=ℝ) k) 4]
  have r := (rep (N:ℝ)).trans (mul_le_mul (le_max_left c 0) square
    (Real.sqrt_nonneg _) bn)
  have log4 : Real.log 4 ≤ 2 := by
    rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [Real.log_two_lt_d9.le]
  have small := (Chebyshev.psi_le_const_mul_self (x:=(D:ℝ)) (Nat.cast_nonneg _)).trans
    (mul_le_mul_of_nonneg_right (show Real.log 4+4≤6 by linarith only [log4]) (Nat.cast_nonneg _))
  have bigFee:=mul_le_mul_of_nonneg_left r (by positivity : 0≤7*(N:ℝ)^6)
  have smallFee:=mul_le_mul_of_nonneg_left small (by positivity : 0≤(2/3:ℝ)*(D:ℝ)^3*(N:ℝ)^3)
  have bound4 : (D:ℝ)^4≤(k:ℝ)^14 := by exact_mod_cast fourth
  have scaled:=mul_le_mul_of_nonneg_right bound4 (by positivity : 0≤4*(N:ℝ)^3)
  have idn:=original_and_return n
  change ordinary N=(N:ℝ)^5*fullWalk n+_ at idn
  change _-Real.log (primeSettings n:ℝ) ≤
    7*(N:ℝ)^6*(Chebyshev.psi (N:ℝ)-Chebyshev.theta (N:ℝ))+
      (2/3:ℝ)*(D:ℝ)^3*(N:ℝ)^3*Chebyshev.psi D at all
  change 0 ≤ outlay n-fullWalk n-earned n ∧ outlay n-fullWalk n-earned n ≤ _
  refine ⟨sub_nonneg.mpr (earned_upper np),?_⟩
  unfold outlay earned
  change ordinary N/(N:ℝ)^5-fullWalk n-Real.log (primeSettings n:ℝ)/(N:ℝ)^5 ≤ _
  apply le_of_mul_le_mul_right (a:=(N:ℝ)^5) _ (pow_pos Np _)
  rw [sub_mul,sub_mul,div_mul_cancel₀ _ (pow_pos Np _).ne',div_mul_cancel₀ _ (pow_pos Np _).ne']
  rw [NN] at idn bigFee smallFee scaled all ⊢
  nlinarith only [idn,all,bigFee,smallFee,scaled]

/-- The logarithmic shortfall on the retained first primes tracks the original
integrated prime-power error with a genuine uniform square-root-scale price. -/
theorem transfer :
    ∃ C : ℝ, 0≤C ∧ ∀ k : ℕ, 2≤k →
      |shortfall k - error (k^4)| ≤ C*(k:ℝ)^6 := by
  obtain ⟨B,bn,omitted⟩:=omitted_price
  refine ⟨500+B,by positivity,?_⟩
  intro k large
  have kp : 0<k := by omega
  have loss:=omitted k kp
  obtain ⟨dl,dh,al,ah⟩:=clock_price_bands large
  have kr : (1:ℝ)≤k := by exact_mod_cast kp
  have small:=pow_le_pow_right₀ kr (by decide : 5≤6)
  have reserve:=mul_nonneg bn (pow_nonneg (Nat.cast_nonneg (α:=ℝ) k) 6)
  unfold shortfall error
  push_cast
  rw [abs_le]
  constructor <;> nlinarith only [loss.1,loss.2,dl,dh,al,ah,small,reserve,
    pow_nonneg (Nat.cast_nonneg (α:=ℝ) k) 6]

#print axioms PALRH.ClockShortfall.payment_sign
#print axioms PALRH.ClockShortfall.omitted_price
#print axioms PALRH.ClockShortfall.transfer
end PALRH.ClockShortfall
