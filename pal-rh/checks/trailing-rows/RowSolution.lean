import PALRH.TrailingRows

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

def trailingPrice (m n : ℕ) : ℤ :=
  ∑ k ∈ Finset.Ico m n, (fixedRunningMass n-fixedRunningMass k)

private theorem price_agrees (m n : ℕ) :
    (trailingPrice m n:ℝ)=PALRH.TrailingRows.price PALRH.RunningMass.running m n := by
  simp only [trailingPrice,PALRH.TrailingRows.price,Int.cast_sum,Int.cast_sub,agrees]

theorem adaptiveRowReduction (h : ∃ K : ℕ, ∀ n : ℕ, 0<n → ∃ m<n,
    (n:ℤ)*(max 0 (trailingPrice m n))^2 ≤ (K:ℤ)*(((n-m)*(n-m+1):ℕ):ℤ)^2) :
    RiemannHypothesis := by
  obtain ⟨K,check⟩:=h
  apply PALRH.TrailingRows.rh_of_adaptive_rows (C:=Real.sqrt (K:ℝ)) (Real.sqrt_nonneg _)
  intro n np
  obtain ⟨m,mn,row⟩:=check n np
  refine ⟨m,mn,?_⟩
  rw [←price_agrees]
  let d:=trailingPrice m n
  let len:ℝ:=((n-m:ℕ):ℝ)
  have square : (n:ℝ)*((max 0 d:ℤ):ℝ)^2 ≤ (K:ℝ)*(len*(len+1))^2 := by
    dsimp only [len,d]
    exact_mod_cast row
  have dp : 0≤((max 0 d:ℤ):ℝ) := by exact_mod_cast (le_max_left (0:ℤ) d)
  have root := (sq_le_sq₀ (by positivity : 0≤Real.sqrt (n:ℝ)*((max 0 d:ℤ):ℝ))
    (by positivity : 0≤Real.sqrt (K:ℝ)*(len*(len+1)))).mp (by
      simpa only [mul_pow,Real.sq_sqrt (Nat.cast_nonneg n),Real.sq_sqrt (Nat.cast_nonneg K)] using square)
  apply (mul_le_mul_of_nonneg_left (by exact_mod_cast (le_max_right (0:ℤ) d) :
      (d:ℝ)≤((max 0 d:ℤ):ℝ)) (Real.sqrt_nonneg _)).trans
  simpa only [mul_assoc] using root

theorem nonpositiveRowReduction (h : ∃ B : ℕ, ∀ n : ℕ, B≤n → 0<n →
    ∃ m<n, trailingPrice m n≤0) : RiemannHypothesis := by
  obtain ⟨B,late⟩:=h
  apply PALRH.TrailingRows.rh_of_free_rows
  refine ⟨B,?_⟩
  intro n hn np
  obtain ⟨m,mn,price⟩:=late n hn np
  refine ⟨m,mn,?_⟩
  rw [←price_agrees]
  exact_mod_cast price

#print axioms adaptiveRowReduction
#print axioms nonpositiveRowReduction
