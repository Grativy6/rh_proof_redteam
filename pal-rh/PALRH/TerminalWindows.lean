import PALRH.RunningMass

open Finset
open scoped BigOperators Classical

noncomputable section
namespace PALRH.TerminalWindows
open RunningMass

private theorem reciprocal_sqrt_sum (m : ℕ) :
    (∑ r ∈ Icc 1 m, 1 / Real.sqrt (r:ℝ)) ≤ 2 * Real.sqrt (m:ℝ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_Icc_succ_top (by omega : 1 ≤ m + 1)]
    push_cast
    have positive : 0 < Real.sqrt ((m:ℝ)+1) := by positivity
    have cost : 1 / Real.sqrt ((m:ℝ)+1) ≤
        2 * (Real.sqrt ((m:ℝ)+1) - Real.sqrt (m:ℝ)) := by
      apply (div_le_iff₀ positive).mpr
      nlinarith [Real.sq_sqrt (by positivity : 0 ≤ (m:ℝ)+1),
        Real.sq_sqrt (by positivity : 0 ≤ (m:ℝ)), sq_nonneg (Real.sqrt ((m:ℝ)+1) - Real.sqrt (m:ℝ))]
    linarith

/-- A one-sided square-root upper bound on the physical running integer is sufficient. -/
theorem rh_of_running_upper {C : ℝ} (cn : 0 ≤ C)
    (bound : ∀ n : ℕ, running n ≤ C * Real.sqrt (n:ℝ)) : RiemannHypothesis := by
  apply OneHeadPhysical.rh_of_primitive_floor (C := 4*C) (by positivity)
  refine ⟨1, ?_⟩
  intro j _ jp
  let T := 2*j^4
  let X := T.factorial
  let N := Nat.log 2 X+1
  have tp : 0 < T := by dsimp [T]; positivity
  have xp : 0 < X := Nat.factorial_pos _
  have tr : 0 < (T:ℝ) := by exact_mod_cast tp
  have xr : 0 < (X:ℝ) := by exact_mod_cast xp
  have rootT := Real.sqrt_pos_of_pos tr
  have common : T ∣ X := Nat.dvd_factorial tp le_rfl
  have enough : X ≤ 2^N := (Nat.lt_pow_succ_log_self (by decide : 1<2) X).le
  have mcast : ((X/T : ℕ):ℝ) = (X:ℝ)/T := Nat.cast_div common tr.ne'
  have total := positive_multiples N X
  rw [split_divisor_rows X T] at total
  have jsmall : j^4 ≤ T := by dsimp [T]; omega
  have price := price_normalized jp (jsmall.trans ((Nat.le_of_dvd xp common).trans enough))
  rw [factorial_price N T tp, ←price] at total
  have low : (∑ r ∈ Icc 1 (X/T), mass N (X/r)) ≤ (C*Real.sqrt X)*(2*Real.sqrt ((X/T:ℕ):ℝ)) := by
    calc
      _ ≤ ∑ r ∈ Icc 1 (X/T), (C*Real.sqrt X)*(1/Real.sqrt (r:ℝ)) := by
        apply Finset.sum_le_sum
        intro r _
        rw [canonical ((Nat.div_le_self X r).trans enough)]
        calc
          _ ≤ C*Real.sqrt ((X/r:ℕ):ℝ) := bound _
          _ ≤ C*Real.sqrt ((X:ℝ)/r) := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt Nat.cast_div_le) cn
          _ = _ := by rw [Real.sqrt_div xr.le]; ring
      _ ≤ _ := by
        rw [←Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (reciprocal_sqrt_sum _) (by positivity)
  have factor : Real.sqrt X*(Real.sqrt X/Real.sqrt T) = ((X:ℝ)/T)*Real.sqrt T := by
    rw [←mul_div_assoc,Real.mul_self_sqrt xr.le]
    calc
      _ = (X:ℝ)/(Real.sqrt T*Real.sqrt T)*Real.sqrt T := by field_simp
      _ = _ := by rw [Real.mul_self_sqrt tr.le]
  have leftprice : (C*Real.sqrt X)*(2*Real.sqrt ((X/T:ℕ):ℝ)) =
      ((X:ℝ)/T)*(2*C*Real.sqrt T) := by
    rw [mcast,Real.sqrt_div xr.le]
    calc
      _ = (2*C)*(Real.sqrt X*(Real.sqrt X/Real.sqrt T)) := by ring
      _ = _ := by rw [factor]; ring
  rw [leftprice] at low
  have cost : -(2*C*Real.sqrt T) ≤ (OneHeadPhysical.primitive j:ℝ) := by
    apply le_of_mul_le_mul_left (a := (X:ℝ)/T) _ (by positivity)
    rw [mul_neg]
    linarith only [total,low]
  have rt : Real.sqrt (T:ℝ) = Real.sqrt 2*(j:ℝ)^2 := by
    rw [show (T:ℝ)=2*((j:ℝ)^2)^2 by dsimp [T]; push_cast; ring,
      Real.sqrt_mul (by norm_num : 0 ≤ (2:ℝ)),Real.sqrt_sq (sq_nonneg _)]
  have cap : Real.sqrt (2:ℝ) ≤ 2 := Real.sqrt_le_iff.mpr (by norm_num)
  rw [rt] at cost
  apply le_trans _ cost
  nlinarith only [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left cap cn) (sq_nonneg (j:ℝ))]

private theorem upper_from_window (f : ℕ → ℝ) (zero : f 0 = 0) {b : ℕ} (two : 2 ≤ b)
    {C : ℝ} (cn : 0 ≤ C) (rise : ∀ n : ℕ, f n-f (n/b) ≤ C*Real.sqrt (n:ℝ)) :
    ∀ n : ℕ, f n ≤ (4*C)*Real.sqrt (n:ℝ) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases np : n=0
    · subst n
      simp [zero]
    have step := ih (n/b) (Nat.div_lt_self (Nat.pos_of_ne_zero np) (by omega))
    have small : Real.sqrt ((n/b:ℕ):ℝ) ≤ (3/4)*Real.sqrt (n:ℝ) := by
      have before : ((n/b:ℕ):ℝ) ≤ ((n/2:ℕ):ℝ) := by
        exact_mod_cast Nat.div_le_div_left two (by decide : 0<2)
      apply (Real.sqrt_le_sqrt before).trans
      apply (Real.sqrt_le_sqrt (Nat.cast_div_le (m:=n) (n:=2) (α:=ℝ))).trans
      push_cast
      rw [Real.sqrt_div (by positivity : 0 ≤ (n:ℝ))]
      have frac : 1 / Real.sqrt (2:ℝ) ≤ 3/4 := by
        apply (div_le_iff₀ (by positivity)).mpr
        have root : (4/3:ℝ) ≤ Real.sqrt 2 := (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
        linarith only [root]
      calc
        _ = Real.sqrt (n:ℝ)*(1/Real.sqrt (2:ℝ)) := by ring
        _ ≤ Real.sqrt (n:ℝ)*(3/4) := mul_le_mul_of_nonneg_left frac (Real.sqrt_nonneg _)
        _ = _ := mul_comm _ _
    linarith only [rise n,step,mul_le_mul_of_nonneg_left small (by positivity : 0 ≤ 4*C)]

/-- Only increases from the preceding half-head need an upper bound. -/
theorem rh_of_half_window {C : ℝ} (cn : 0 ≤ C)
    (rise : ∀ n : ℕ, running n-running (n/2) ≤ C*Real.sqrt (n:ℝ)) : RiemannHypothesis :=
  rh_of_running_upper (C:=4*C) (by positivity)
    (upper_from_window running (by simp [running,mass]) (b:=2) le_rfl cn rise)

/-- A second difference retains both the 2- and 3-adic comparisons. -/
theorem rh_of_mixed_window {C : ℝ} (cn : 0 ≤ C)
    (rise : ∀ n : ℕ, (running n-running (n/2))-(running (n/3)-running (n/6)) ≤
      C*Real.sqrt (n:ℝ)) : RiemannHypothesis := by
  apply rh_of_half_window (C:=4*C) (by positivity)
  apply upper_from_window (fun n => running n-running (n/2)) (by simp) (b:=3) (by decide) cn
  intro n
  simpa only [Nat.div_div_eq_div_mul] using rise n

#print axioms PALRH.TerminalWindows.rh_of_running_upper
#print axioms PALRH.TerminalWindows.rh_of_half_window
#print axioms PALRH.TerminalWindows.rh_of_mixed_window
end PALRH.TerminalWindows
