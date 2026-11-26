import PALRH.TerminalWindows

open Finset
open scoped BigOperators

def fixedRunningMass (n : ℕ) : ℤ :=
  let L:=Nat.log 2 n+1
  ∑ i ∈ Finset.range (L+1), ∑ j ∈ Finset.range (L+1),
    let v : ℕ:=2^i*3^j
    (v:ℤ)*∑ d ∈ Finset.Icc 1 (n/v^2), if d.Coprime 6 then ArithmeticFunction.moebius d else 0

private theorem agrees (n : ℕ) : (fixedRunningMass n:ℝ)=PALRH.RunningMass.running n := by
  unfold fixedRunningMass PALRH.RunningMass.running PALRH.RunningMass.mass
  push_cast
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  apply congrArg (fun z : ℝ => (2:ℝ)^i*3^j*z)
  apply Finset.sum_congr rfl; intro d _
  by_cases rough : d.Coprime 6
  · have h : PALRH.TaperedNewton.marks d=(ArithmeticFunction.moebius d:ℚ) := by
      change (ArithmeticFunction.moebius d:ℚ)*(if d.Coprime 6 then 1 else 0)=_
      rw [if_pos rough,mul_one]
    rw [if_pos rough,h]
    norm_cast
  · have h : PALRH.TaperedNewton.marks d=0 := by
      change (ArithmeticFunction.moebius d:ℚ)*(if d.Coprime 6 then 1 else 0)=0
      rw [if_neg rough,mul_zero]
    rw [if_neg rough,h]
    norm_num

def halfRise (n : ℕ) : ℤ := fixedRunningMass n - fixedRunningMass (n/2)

def mixedRise (n : ℕ) : ℤ := halfRise n - halfRise (n/3)

private theorem root_bound (d : ℤ) (K n : ℕ) (h : (max 0 d)^2 ≤ (K:ℤ)*n) :
    (d:ℝ) ≤ Real.sqrt K * Real.sqrt n := by
  have non : 0 ≤ ((max 0 d:ℤ):ℝ) := by exact_mod_cast (le_max_left (0:ℤ) d)
  have sq : ((max 0 d:ℤ):ℝ)^2 ≤ (K:ℝ)*n := by exact_mod_cast h
  have b := (Real.le_sqrt non (by positivity : 0 ≤ (K:ℝ)*n)).mpr sq
  rw [Real.sqrt_mul (by positivity : 0 ≤ (K:ℝ))] at b
  exact (show (d:ℝ) ≤ ((max 0 d:ℤ):ℝ) by exact_mod_cast (le_max_right (0:ℤ) d)).trans b

theorem halfWindowReduction (h : ∃ K : ℕ, ∀ n : ℕ, (max 0 (halfRise n))^2 ≤ (K:ℤ)*n) :
    RiemannHypothesis := by
  obtain ⟨K,check⟩ := h
  apply PALRH.TerminalWindows.rh_of_half_window (C:=Real.sqrt K) (Real.sqrt_nonneg _)
  intro n
  have b := root_bound (halfRise n) K n (check n)
  simpa only [halfRise,Int.cast_sub,agrees] using b

#print axioms halfWindowReduction

theorem mixedWindowReduction (h : ∃ K : ℕ, ∀ n : ℕ, (max 0 (mixedRise n))^2 ≤ (K:ℤ)*n) :
    RiemannHypothesis := by
  obtain ⟨K,check⟩ := h
  apply PALRH.TerminalWindows.rh_of_mixed_window (C:=Real.sqrt K) (Real.sqrt_nonneg _)
  intro n
  have b := root_bound (mixedRise n) K n (check n)
  simpa only [mixedRise,halfRise,Nat.div_div_eq_div_mul,Int.cast_sub,agrees] using b

#print axioms mixedWindowReduction
