import PALRH.RunningMass

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

theorem runningIntegerReduction (h : ∃ B : ℕ, ∀ n : ℕ, B≤n → fixedRunningMass n≤0) :
    RiemannHypothesis := by
  obtain ⟨B,late⟩:=h
  apply PALRH.RunningMass.rh_of_running_nonpositive
  refine ⟨B,?_⟩
  intro n hn
  rw [←agrees]
  exact_mod_cast late n hn

#print axioms runningIntegerReduction
