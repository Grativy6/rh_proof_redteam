import PALRH.RectangleBalance
import PALRH.DysonOctave
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

open Finset
open scoped BigOperators Classical

noncomputable section
namespace PALRH.FactorialReturn

def tail (N : ℕ) (f : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ k ∈ Icc 1 (N/m), (ArithmeticFunction.moebius k:ℝ)*f (m*k)

def change (N : ℕ) (f : ℕ → ℝ) (m : ℕ) := tail N f m-tail N f (m+1)

/-- Group once by the physical integer, with all original factors still attached. -/
theorem products (N : ℕ) (a b f : ℕ → ℝ) :
    (∑ r ∈ Icc 1 N, a r*∑ d ∈ Icc 1 (N/r), b d*f (r*d)) =
      ∑ n ∈ Icc 1 N, (∑ d ∈ n.divisors, b d*a (n/d))*f n := by
  have collect:=RectangleBalance.collect_weights N b a (fun n => (n:ℝ)*f n)
  calc
    _ = ∑ r ∈ Icc 1 N, (a r/r)*∑ d ∈ Icc 1 (N/r), (b d/d)*(((r*d:ℕ):ℝ)*f (r*d)) := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.mul_sum,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      have rr : (r:ℝ)≠0 := by exact_mod_cast (show 0<r from (mem_Icc.mp hr).1).ne'
      have dr : (d:ℝ)≠0 := by exact_mod_cast (show 0<d from (mem_Icc.mp hd).1).ne'
      rw [Nat.cast_mul]
      field_simp
    _ = _ := collect
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      have nr : (n:ℝ)≠0 := by exact_mod_cast (show 0<n from (mem_Icc.mp hn).1).ne'
      field_simp

private theorem source (n : ℕ) :
    (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d:ℝ)*Real.log (n/d:ℕ))=
      ArithmeticFunction.vonMangoldt n := by
  have h:=DFunLike.congr_fun ArithmeticFunction.moebius_mul_log_eq_vonMangoldt n
  rw [ArithmeticFunction.mul_apply] at h
  change (∑ v ∈ n.divisorsAntidiagonal, (ArithmeticFunction.moebius v.1:ℝ)*Real.log (v.2:ℝ))=_ at h
  rw [Nat.sum_divisorsAntidiagonal (fun i j => (ArithmeticFunction.moebius i:ℝ)*Real.log (j:ℝ))] at h
  exact h

private theorem unit_source (n : ℕ) :
    (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d:ℝ)*1)=if n=1 then 1 else 0 := by
  have eq:=DFunLike.congr_fun ArithmeticFunction.moebius_mul_coe_zeta n
  rw [ArithmeticFunction.coe_mul_zeta_apply,ArithmeticFunction.one_apply] at eq
  simp only [mul_one]
  by_cases one : n=1 <;> simp only [one,if_true,if_false] at eq ⊢ <;> exact_mod_cast eq

/-- Undo the tail point by point, before evaluating it on any prime sum. -/
theorem return_weight {N d : ℕ} (dp : 0<d) (covered : d≤N) (f : ℕ → ℝ) :
    (∑ r ∈ Icc 1 (N/d), tail N f (d*r))=f d := by
  have non := Nat.div_pos covered dp
  have h:=products (N/d) (fun _ => 1) (fun k => (ArithmeticFunction.moebius k:ℝ)) (fun k => f (d*k))
  simp only [one_mul,unit_source] at h
  have eq : (∑ p ∈ Icc 1 (N/d), (if p=1 then (1:ℝ) else 0)*f (d*p))=f d := by
    rw [Finset.sum_eq_single 1]
    · simp
    · intro n _ hn; simp [hn]
    · intro no; exact False.elim (no (mem_Icc.mpr ⟨le_rfl,non⟩))
  rw [←eq,←h]
  apply Finset.sum_congr rfl
  intro r _
  simp only [tail,Nat.div_div_eq_div_mul,Nat.mul_assoc]

/-- Summation by parts, including the last tail. -/
theorem difference_sum (N : ℕ) (G A : ℕ → ℝ) :
    (∑ m ∈ Icc 1 N, (G m-G (m+1))*A m)=
      (∑ m ∈ Icc 1 N, G m*(A m-A (m-1)))+G 1*A 0-G (N+1)*A N := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [sum_Icc_succ_top (by omega : 1≤n+1),sum_Icc_succ_top (by omega : 1≤n+1),ih]
    simp only [Nat.add_sub_cancel]
    ring

/-- The exact signed factorial comparison for any finite weight function. -/
theorem signed_factorials (N : ℕ) (f : ℕ → ℝ) :
    (∑ m ∈ Icc 1 N, change N f m*Real.log (m.factorial:ℝ))=
      ∑ n ∈ Icc 1 N, ArithmeticFunction.vonMangoldt n*f n := by
  have step {m : ℕ} (mp : 0<m) : Real.log (m.factorial:ℝ)-
      Real.log ((m-1).factorial:ℝ)=Real.log (m:ℝ) := by
    obtain ⟨k,rfl⟩:=Nat.exists_eq_succ_of_ne_zero mp.ne'
    rw [Nat.succ_sub_one,Nat.factorial_succ,Nat.cast_mul,Real.log_mul (by positivity) (by positivity)]
    ring
  have gone : tail N f (N+1)=0 := by simp [tail,Nat.div_eq_of_lt (Nat.lt_succ_self N)]
  unfold change
  rw [difference_sum]
  simp only [Nat.factorial_zero,Nat.cast_one,Real.log_one,mul_zero,add_zero,gone,zero_mul,sub_zero]
  calc
    _ = ∑ m ∈ Icc 1 N, Real.log (m:ℝ)*tail N f m := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [step (mem_Icc.mp hm).1,mul_comm]
    _ = _ := by
      unfold tail
      rw [products]
      simp only [source]

/-- No net first moment is charged when the target gives label one no weight. -/
theorem first_moment {N : ℕ} (np : 0<N) (f : ℕ → ℝ) :
    (∑ m ∈ Icc 1 N, change N f m*(m:ℝ))=f 1 := by
  unfold change
  rw [difference_sum]
  have gone : tail N f (N+1)=0 := by simp [tail,Nat.div_eq_of_lt (Nat.lt_succ_self N)]
  simp only [Nat.cast_zero,mul_zero,add_zero,gone,zero_mul,sub_zero]
  have e : (∑ m ∈ Icc 1 N, tail N f m*((m:ℝ)-(m-1:ℕ)))=∑ m ∈ Icc 1 N, tail N f m := by
    apply Finset.sum_congr rfl
    intro m hm
    rw [Nat.cast_sub (mem_Icc.mp hm).1,Nat.cast_one];ring
  rw [e]
  simpa using return_weight (N:=N) (d:=1) (by decide) np f

/-- Every sampled divisor reading is recovered from the actual signed floor rows. -/
theorem floor_return {N d : ℕ} (dp : 0<d) (covered : d≤N) (f : ℕ → ℝ) :
    (∑ m ∈ Icc 1 N, change N f m*((m/d:ℕ):ℝ))=f d := by
  have gone : tail N f (N+1)=0 := by simp [tail,Nat.div_eq_of_lt (Nat.lt_succ_self N)]
  have count {m : ℕ} (within : m≤N) :
      (∑ r ∈ Icc 1 (N/d), if r*d≤m then (1:ℝ) else 0)=(m/d:ℕ) := by
    rw [Finset.sum_boole]
    have sets : (Icc 1 (N/d)).filter (fun r => r*d≤m)=Icc 1 (m/d) := by
      ext r
      simp only [mem_filter,mem_Icc,←Nat.le_div_iff_mul_le dp]
      have := Nat.div_le_div_right (c:=d) within
      omega
    rw [sets,Nat.card_Icc]
    simp
  calc
    _ = ∑ m ∈ Icc 1 N, ∑ r ∈ Icc 1 (N/d), if r*d≤m then change N f m else 0 := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [←count (mem_Icc.mp hm).2,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      split_ifs <;> simp
    _ = ∑ r ∈ Icc 1 (N/d), ∑ m ∈ Icc 1 N, if r*d≤m then change N f m else 0 := Finset.sum_comm
    _ = ∑ r ∈ Icc 1 (N/d), tail N f (d*r) := by
      apply Finset.sum_congr rfl
      intro r hr
      have low : 0<r*d := Nat.mul_pos (mem_Icc.mp hr).1 dp
      have high : r*d≤N := (Nat.le_div_iff_mul_le dp).mp (mem_Icc.mp hr).2
      rw [←Finset.sum_filter]
      have sets : (Icc 1 N).filter (fun m => r*d≤m)=Ico (r*d) (N+1) := by
        ext m
        simp only [mem_filter,mem_Icc,mem_Ico]
        omega
      rw [sets,Nat.mul_comm d r]
      have diff:=Finset.sum_Ico_sub (fun m => -tail N f m) (by omega : r*d≤N+1)
      simpa only [neg_sub_neg,gone,sub_zero,change] using diff
    _ = _ := return_weight dp covered f

/-- At an actual square the signed factorials return the program's prime-power reading. -/
def squareWeight (j n : ℕ) : ℝ :=
  max 0 (Real.log 2 - |Real.log ((n:ℝ)/(j:ℝ)^2)|) / Real.sqrt n

theorem square_reading (j : ℕ) :
    (∑ m ∈ Icc 1 (2*j^2), change (2*j^2) (squareWeight j) m*Real.log (m.factorial:ℝ))=
      DysonOctave.fullReading j := by
  rw [signed_factorials]
  unfold DysonOctave.fullReading
  apply Finset.sum_congr rfl
  intro n _
  unfold squareWeight
  ring

#print axioms PALRH.FactorialReturn.floor_return
#print axioms PALRH.FactorialReturn.square_reading
#print axioms PALRH.FactorialReturn.return_weight
#print axioms PALRH.FactorialReturn.signed_factorials
#print axioms PALRH.FactorialReturn.first_moment
end PALRH.FactorialReturn
