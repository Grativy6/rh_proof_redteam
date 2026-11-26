import PALRH.TerminalWindows

open Finset
open scoped BigOperators Classical

noncomputable section
namespace PALRH.TrailingRows

/-- A row compares its newest count with each strictly earlier count in the window. -/
def price (f : ℕ → ℝ) (m n : ℕ) := ∑ k ∈ Ico m n, (f n-f k)

theorem price_eq (f : ℕ → ℝ) (m n : ℕ) :
    price f m n = ((n-m:ℕ):ℝ)*f n - ∑ k ∈ Ico m n, f k := by
  simp [price,Finset.sum_sub_distrib,Nat.card_Ico,nsmul_eq_mul]

/-- The same quantity charges each original increment once per remaining position. -/
theorem ramp (f : ℕ → ℝ) (m n : ℕ) (mn : m≤n) :
    price f m n = ∑ d ∈ Ioc m n, ((d-m:ℕ):ℝ)*(f d-f (d-1)) := by
  induction n, mn using Nat.le_induction with
  | base => simp [price]
  | succ n mn ih =>
    rw [Finset.sum_Ioc_succ_top mn,←ih,price_eq,price_eq,
      Finset.sum_Ico_succ_top mn]
    have cast : ((n+1-m:ℕ):ℝ) = ((n-m:ℕ):ℝ)+1 := by
      exact_mod_cast (by omega : n+1-m=n-m+1)
    rw [cast,Nat.add_sub_cancel]
    ring

/-- Each head can use its own earlier starting point. A positive excess over the barrier
would also be a positive excess on that selected row at its first occurrence. -/
theorem maximum_principle (f g : ℕ → ℝ) (start : f 0≤g 0)
    (row : ∀ n : ℕ, 0<n → ∃ m<n, price f m n≤price g m n) : ∀ n : ℕ, f n≤g n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases z : n=0
    · simpa [z] using start
    obtain ⟨m,small,compare⟩:=row n (Nat.pos_of_ne_zero z)
    have past : (∑ k ∈ Ico m n, f k) ≤ ∑ k ∈ Ico m n, g k :=
      Finset.sum_le_sum (fun k hk => ih k (Finset.mem_Ico.mp hk).2)
    simp only [price_eq] at compare
    have len : 0<((n-m:ℕ):ℝ) := by exact_mod_cast Nat.sub_pos_of_lt small
    exact le_of_mul_le_mul_left (by linarith only [compare,past] :
      ((n-m:ℕ):ℝ)*f n≤((n-m:ℕ):ℝ)*g n) len

private theorem steps (m n : ℕ) (mn : m≤n) :
    (∑ k ∈ Ico m n, ((n:ℝ)-k)) = ((n-m:ℕ):ℝ)*(((n-m:ℕ):ℝ)+1)/2 := by
  induction n, mn using Nat.le_induction with
  | base => simp
  | succ n mn ih =>
    rw [Finset.sum_Ico_succ_top mn]
    push_cast
    have add (k : ℕ) : (n:ℝ)+1-k=(n-k)+1 := by ring
    simp_rw [add]
    rw [Finset.sum_add_distrib,ih]
    have cast : ((n+1-m:ℕ):ℝ)=((n-m:ℕ):ℝ)+1 := by
      exact_mod_cast (by omega : n+1-m=n-m+1)
    rw [cast]
    simp [Nat.card_Ico]
    ring

/-- The square-root barrier has a strictly positive, explicit finite price at every width. -/
theorem root_price {m n : ℕ} (mn : m<n) :
    ((n-m:ℕ):ℝ)*(((n-m:ℕ):ℝ)+1) ≤ 4*Real.sqrt n*price (fun k => Real.sqrt k) m n := by
  have non : 0≤Real.sqrt (n:ℝ) := Real.sqrt_nonneg _
  have bound : (∑ k ∈ Ico m n, ((n:ℝ)-k)) ≤ (2*Real.sqrt n)*price (fun k => Real.sqrt k) m n := by
    rw [price,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    have nk : (k:ℝ)≤n := by exact_mod_cast (mem_Ico.mp hk).2.le
    have sk:=Real.sqrt_le_sqrt nk
    nlinarith only [Real.sq_sqrt (show 0≤(n:ℝ) by positivity),
      Real.sq_sqrt (show 0≤(k:ℝ) by positivity),sq_nonneg (Real.sqrt (n:ℝ)-Real.sqrt (k:ℝ))]
  rw [steps m n mn.le] at bound
  linarith only [bound]

/-- One trailing row suffices at each head. Its length may be chosen after seeing the marks. -/
theorem rh_of_adaptive_rows {C : ℝ} (cn : 0≤C)
    (paid : ∀ n : ℕ, 0<n → ∃ m<n, Real.sqrt n*price RunningMass.running m n ≤
      C*((n-m:ℕ):ℝ)*(((n-m:ℕ):ℝ)+1)) : RiemannHypothesis := by
  apply TerminalWindows.rh_of_running_upper (C:=4*C) (by positivity)
  apply maximum_principle RunningMass.running (fun k => 4*C*Real.sqrt k)
  · simp [RunningMass.running,RunningMass.mass]
  intro n np
  obtain ⟨m,mn,row⟩:=paid n np
  refine ⟨m,mn,?_⟩
  have eq : price (fun k => 4*C*Real.sqrt k) m n=4*C*price (fun k => Real.sqrt k) m n := by
    simp only [price,←Finset.mul_sum,←mul_sub]
  rw [eq]
  have rp : 0<Real.sqrt (n:ℝ) := by positivity
  apply le_of_mul_le_mul_left (a:=Real.sqrt n) _ rp
  have credit:=mul_le_mul_of_nonneg_left (root_price mn) cn
  nlinarith only [credit,row]

/-- Finite early exceptions are affordable when one nonpositive row exists at every late head. -/
theorem rh_of_free_rows
    (paid : ∃ B : ℕ, ∀ n : ℕ, B≤n → 0<n → ∃ m<n, price RunningMass.running m n≤0) :
    RiemannHypothesis := by
  obtain ⟨B,late⟩:=paid
  let cost := fun k : ℕ => |Real.sqrt (k:ℝ)*price RunningMass.running 0 k|
  let C := ∑ k ∈ Icc 1 B, cost k
  have cn : 0≤C := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  apply rh_of_adaptive_rows cn
  intro n np
  by_cases big : B≤n
  · obtain ⟨m,mn,good⟩:=late n big np
    exact ⟨m,mn,(mul_nonpos_of_nonneg_of_nonpos (Real.sqrt_nonneg _) good).trans (by positivity)⟩
  · refine ⟨0,np,?_⟩
    have single : cost n≤C := Finset.single_le_sum (fun k _ => abs_nonneg _) (mem_Icc.mpr ⟨np,by omega⟩)
    have nr : 1≤(n:ℝ) := by exact_mod_cast np
    have scale : (1:ℝ)≤(n:ℝ)*(n+1) := by nlinarith only [nr,sq_nonneg (n:ℝ)]
    simp only [Nat.sub_zero]
    apply (le_abs_self _).trans (single.trans _)
    simpa only [mul_assoc] using (le_mul_of_one_le_right cn scale)

#print axioms PALRH.TrailingRows.rh_of_free_rows
#print axioms PALRH.TrailingRows.ramp
#print axioms PALRH.TrailingRows.maximum_principle
#print axioms PALRH.TrailingRows.root_price
#print axioms PALRH.TrailingRows.rh_of_adaptive_rows
end PALRH.TrailingRows
