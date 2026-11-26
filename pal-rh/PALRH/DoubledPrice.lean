import PALRH.DoubledRuler

open Finset
open scoped BigOperators
noncomputable section
namespace PALRH.DoubledPrice
open DoubledRuler LinearPrimeIntegral QuarticBoards

private def potential (N m : ℕ) : ℝ := (m:ℝ)*((N:ℝ)-m)^6

/-- The derivative weight exceeds the exact finite difference by at most
six units after the common fifth-power denominator is removed. -/
private theorem ink_le_step {N m : ℕ} (pos : 0 < m) (cap : m ≤ N) :
    (ink N m:ℝ) ≤ potential N (m-1) - potential N m + 6*(N:ℝ)^5 := by
  let t : ℝ := (N:ℝ)-m
  have hp : (1:ℝ) ≤ m := by exact_mod_cast pos
  have tn : 0 ≤ t := sub_nonneg.mpr (by exact_mod_cast cap)
  have small : t ≤ N := by dsimp [t]; linarith only [Nat.cast_nonneg (α:=ℝ) m]
  have raise : 6*t^5 ≤ (t+1)^6-t^6 := by
    have rest : 0 ≤ 15*t^4+20*t^3+15*t^2+6*t+1 := by positivity
    nlinarith only [rest]
  have weighed := mul_le_mul_of_nonneg_left raise (sub_nonneg.mpr hp)
  have f := pow_le_pow_left₀ tn small 5
  unfold ink potential
  push_cast [Nat.cast_sub (show 1 ≤ m by omega)]
  change t^5*(7*(m:ℝ)-N) ≤ ((m:ℝ)-1)*((N:ℝ)-(m-1))^6 - (m:ℝ)*t^6 + 6*N^5
  rw [show (N:ℝ)-((m:ℝ)-1)=t+1 by dsimp [t]; ring,
    show (7*(m:ℝ)-N)=6*m-t by dsimp [t]; ring]
  nlinarith only [weighed, f]

private theorem log_steps (N L : ℕ) :
    (∑ m ∈ Icc 1 L, (potential N (m-1)-potential N m)*Real.log m) =
    (∑ m ∈ Icc 1 L, potential N m*(Real.log ((m:ℝ)+1)-Real.log m)) -
      potential N L * Real.log ((L:ℝ)+1) := by
  induction L with
  | zero => simp [potential]
  | succ L old =>
    rw [sum_Icc_succ_top (by omega : 1 ≤ L+1), sum_Icc_succ_top (by omega : 1 ≤ L+1), old]
    simp only [Nat.succ_sub_one, Nat.cast_succ]
    ring

private theorem sum_six_bound (N L : ℕ) (cap : L ≤ N) :
    7*(∑ m ∈ Icc 1 L, ((N:ℝ)-m)^6) ≤ (N:ℝ)^7-((N:ℝ)-L)^7 := by
  induction L with
  | zero => simp
  | succ L old =>
    have bound := old (by omega : L ≤ N)
    rw [sum_Icc_succ_top (by omega : 1 ≤ L+1), mul_add]
    push_cast
    let t : ℝ := (N:ℝ)-(L+1)
    have tn : 0 ≤ t := sub_nonneg.mpr (by exact_mod_cast cap)
    have rest : 0 ≤ 21*t^5+35*t^4+35*t^3+21*t^2+7*t+1 := by positivity
    have price : 7*t^6 ≤ (t+1)^7-t^7 := by nlinarith only [rest]
    rw [show (N:ℝ)-L=t+1 by dsimp [t]; ring] at bound
    linarith only [bound,price]

theorem ordinary_price (N : ℕ) :
    ordinary N ≤ (N:ℝ)^7/7 + 6*(N:ℝ)^6*Real.log N := by
  have sums : ordinary N ≤
      (∑ m ∈ Icc 1 N,(potential N (m-1)-potential N m)*Real.log m) +
      6*(N:ℝ)^6*Real.log N := by
    unfold ordinary
    calc
      _ ≤ ∑ m ∈ Icc 1 N, ((potential N (m-1)-potential N m)*Real.log m +
                                6*(N:ℝ)^5*Real.log N) := by
        apply sum_le_sum
        intro m hm
        have hp := (mem_Icc.mp hm).1
        have hj := (mem_Icc.mp hm).2
        have lm := Real.log_nonneg (show 1 ≤ (m:ℝ) by exact_mod_cast hp)
        have logBound := Real.log_le_log (show 0 < (m:ℝ) by exact_mod_cast hp) (by exact_mod_cast hj : (m:ℝ) ≤ N)
        have summed := mul_le_mul_of_nonneg_right (ink_le_step hp hj) lm
        have fee := mul_le_mul_of_nonneg_left logBound (by positivity : 0 ≤ 6*(N:ℝ)^5)
        nlinarith only [summed,fee]
      _ = _ := by rw [sum_add_distrib]; simp [Nat.card_Icc]; ring
  rw [log_steps] at sums
  have sumSteps : (∑ m ∈ Icc 1 N,potential N m*(Real.log ((m:ℝ)+1)-Real.log m)) ≤
      ∑ m ∈ Icc 1 N, ((N:ℝ)-m)^6 := by
    apply sum_le_sum
    intro m hm
    have mp : 0 < (m:ℝ) := by exact_mod_cast (mem_Icc.mp hm).1
    have a := Real.log_le_sub_one_of_pos (show 0 < ((m:ℝ)+1)/m by positivity)
    rw [Real.log_div (by positivity) mp.ne'] at a
    have b := (le_div_iff₀ mp).mp (show Real.log ((m:ℝ)+1)-Real.log m ≤ 1/m by
      convert a using 1; field_simp; ring)
    unfold potential
    nlinarith only [mul_le_mul_of_nonneg_right b (by positivity : 0 ≤ ((N:ℝ)-m)^6)]
  have cap := sum_six_bound N N le_rfl
  simp [potential] at sums sumSteps cap
  linarith only [sums,sumSteps,cap]

private theorem prime_log_le_all (n : ℕ) :
    Real.log (primeSettings n : ℝ) ≤
      ∑ d ∈ Icc 1 (2*n), ArithmeticFunction.vonMangoldt d * (extra n d:ℝ) := by
  classical
  unfold primeSettings
  push_cast
  rw [Real.log_prod]
  · apply sum_le_sum
    intro d hd
    have h : 0 ≤ extra n d := extra_nonneg (mem_Icc.mp hd).1 (mem_Icc.mp hd).2
    by_cases keep : d.Prime ∧ n^7 < d^8
    · rw [if_pos keep, Real.log_pow, ArithmeticFunction.vonMangoldt_apply_prime keep.1]
      have same : ((extra n d).toNat:ℝ) = (extra n d:ℝ) := by exact_mod_cast (Int.toNat_of_nonneg h)
      simpa only [same, mul_comm] using (le_refl ((extra n d:ℝ)*Real.log d))
    · simp only [keep, if_false, Real.log_one]
      exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (by exact_mod_cast h)
  · intro d hd
    by_cases keep : d.Prime ∧ n^7 < d^8
    · rw [if_pos keep]
      exact_mod_cast (pow_pos keep.1.pos (extra n d).toNat).ne'
    · simp [keep]

theorem rh_of_prime_settings (K : ℕ)
    (paid : ∀ k : ℕ, K ≤ k → 0 < k →
      let n := k^4
      (n+1)^(ticks k) ≤ n^(ticks k)*(primeSettings n)^14) :
    RiemannHypothesis := by
  apply OneSidedBoard.rh_of_eventual_upper_area K (C:=52) (by norm_num)
  intro k late kp
  let n := k^4
  let N := 2*n
  have np : 0 < n := pow_pos kp _
  have nreal : 0 < (n:ℝ) := by exact_mod_cast np
  have Nreal : 0 < (N:ℝ) := by dsimp [N]; positivity
  have settings_pos : 0 < primeSettings n := by
    unfold primeSettings
    apply Finset.prod_pos
    intro d hd
    split_ifs with h
    · exact pow_pos h.1.pos _
    · decide
  have input := paid k late kp
  change (n+1)^ticks k ≤ n^ticks k*(primeSettings n)^14 at input
  have logs := Real.log_le_log (by positivity : 0 < (((n+1:ℕ)^(ticks k):ℕ):ℝ))
    (by exact_mod_cast input :
      (((n+1:ℕ)^(ticks k):ℕ):ℝ) ≤ ((n^(ticks k)*(primeSettings n)^14:ℕ):ℝ))
  push_cast at logs
  rw [Real.log_mul (by positivity) (by positivity)] at logs
  simp only [Real.log_pow, Nat.cast_ofNat] at logs
  have step := Real.one_sub_inv_le_log_of_pos (show 0 < ((n:ℝ)+1)/n by positivity)
  rw [Real.log_div (by positivity) nreal.ne'] at step
  have frac : 1-(((n:ℝ)+1)/n)⁻¹=1/(n+1:ℝ) := by field_simp; ring
  rw [frac] at step
  have kr : 1 ≤ (k:ℝ) := by exact_mod_cast kp
  have rootbound : k^2 ≤ n := by
    dsimp [n]
    exact Nat.pow_le_pow_right kp (by decide)
  have clock : (ticks k:ℝ)=(N:ℝ)^5*n*((n:ℝ)-(k:ℝ)^2)^2 := by
    change (((2*n)^5 * n * (n-k^2)^2:ℕ):ℝ) = _
    push_cast [Nat.cast_sub rootbound]
    dsimp [N]
    push_cast
    ring
  have times := mul_le_mul_of_nonneg_left step (by positivity : 0 ≤ (ticks k:ℝ))
  have price := prime_log_le_all n
  have align := original_and_return n
  have ordinaryBound := ordinary_price N
  have caplog : Real.log (N:ℝ) ≤ 4*(k:ℝ)^2 := by
    have h := Real.log_le_sub_one_of_pos (show 0 < (2:ℝ)*k^2 by positivity)
    have logmon := Real.log_le_log Nreal (by
      dsimp [N,n];push_cast;nlinarith only [sq_nonneg ((k:ℝ)^2)] :
      (N:ℝ) ≤ ((2:ℝ)*k^2)^2)
    rw [Real.log_pow] at logmon
    push_cast at logmon
    linarith only [logmon,h]
  have negpart : 0 ≤ (n:ℝ) := nreal.le
  have nn : ((n:ℕ):ℝ) = (k:ℝ)^4 := by dsimp [n];push_cast;rfl
  have lowinner : (n:ℝ)^2-2*n*k^2-n ≤ n*((n:ℝ)-k^2)^2/(n+1) := by
    apply (le_div_iff₀ (by positivity : 0 < (n:ℝ)+1)).mpr
    nlinarith only [sq_nonneg ((k:ℝ)^2),mul_nonneg negpart (sq_nonneg ((k:ℝ)^2)),negpart,mul_nonneg negpart (sq_nonneg (k:ℝ))]
  have cost : (N:ℝ)^5*((n:ℝ)^2-2*n*k^2-n) ≤ 14 * Real.log (primeSettings n:ℝ) := by
    have scaled := mul_le_mul_of_nonneg_left lowinner (by positivity : 0 ≤ (N:ℝ)^5)
    rw [clock] at times logs
    calc
      _ ≤ (N:ℝ)^5*(n*((n:ℝ)-k^2)^2/(n+1)) := scaled
      _ = ((N:ℝ)^5*n*((n:ℝ)-k^2)^2)*(1/(n+1)) := by ring
      _ ≤ _ := by nlinarith only [logs,times]
  change ordinary N = (N:ℝ)^5*fullWalk n+_ at align
  have nN : (N:ℝ)=2*(n:ℝ) := by dsimp [N];push_cast;rfl
  have ref : (N:ℝ)^7/7 - (N:ℝ)^5*(n:ℝ)^2/14 = (N:ℝ)^5*(n:ℝ)^2/2 := by
    rw [nN]; ring
  have raw : (N:ℝ)^5*(fullWalk n - (n:ℝ)^2/2) ≤
      6*(N:ℝ)^6*Real.log N + (N:ℝ)^5*(2*n*(k:ℝ)^2+n)/14 := by
    nlinarith only [align,price,cost,ordinaryBound,ref]
  have small : (k:ℝ)^4 ≤ (k:ℝ)^6 := pow_le_pow_right₀ kr (by decide)
  have finalPrice : 6*(N:ℝ)*(4*(k:ℝ)^2)+(2*(n:ℝ)*k^2+n)/14 ≤ 52*(k:ℝ)^6 := by
    rw [nN,nn]
    nlinarith only [small, pow_nonneg (Nat.cast_nonneg (α:=ℝ) k) 6]
  have fee := mul_le_mul_of_nonneg_left caplog (by positivity : 0 ≤ 6*(N:ℝ)^6)
  have scaled := mul_le_mul_of_nonneg_left finalPrice (by positivity : 0 ≤ (N:ℝ)^5)
  have joint : (N:ℝ)^5*(fullWalk n - (n:ℝ)^2/2) ≤ (N:ℝ)^5*(52*(k:ℝ)^6) := by
    nlinarith only [raw,fee,scaled]
  exact le_of_mul_le_mul_left joint (by positivity : 0 < (N:ℝ)^5)

#print axioms PALRH.DoubledPrice.ordinary_price
#print axioms PALRH.DoubledPrice.rh_of_prime_settings

end PALRH.DoubledPrice
