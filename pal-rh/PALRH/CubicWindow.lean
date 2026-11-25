import PALRH.SquareSignRows

open Finset Set
open scoped BigOperators Classical
noncomputable section
namespace PALRH.CubicWindow
open RectangleBalance TaperedNewton

/-- Twice the polynomial for one term's curvature, with its common positive denominator removed. -/
def curvature (n : ℕ) (x : ℝ) := 2*(n:ℝ)*(x-n)*(2*n-x)

theorem curvature_sum (N : ℕ) (x : ℝ) :
    (∑ n ∈ Finset.Icc 1 N, curvature n x)=
      (N:ℝ)*(N+1)*(x-N)*(N+1-x) := by
  induction N with
  | zero => simp
  | succ N old =>
    rw [Finset.sum_Icc_succ_top (by omega),old]
    unfold curvature
    push_cast
    ring

theorem positive_tail (M N : ℕ) {x : ℝ} (lo : N≤x) (hi : x≤(N:ℝ)+1) :
    0≤∑ n ∈ Finset.Icc 1 N, if M<n then curvature n x else 0 := by
  by_cases small : 2*(M:ℝ)≤x
  · have full : 0≤∑ n ∈ Finset.Icc 1 N, curvature n x := by
      rw [curvature_sum]
      exact mul_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr lo)) (sub_nonneg.mpr hi)
    apply full.trans
    apply Finset.sum_le_sum
    intro n hn
    by_cases keep : M<n
    · rw [if_pos keep]
    · rw [if_neg keep]
      have nm : (n:ℝ)≤M := by exact_mod_cast (le_of_not_gt keep)
      have nx : (n:ℝ)≤x := (by exact_mod_cast (Finset.mem_Icc.mp hn).2 : (n:ℝ)≤N).trans lo
      exact mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg (by positivity) (sub_nonneg.mpr nx)) (by linarith)
  · apply Finset.sum_nonneg
    intro n hn
    by_cases keep : M<n
    · rw [if_pos keep]
      have nm : (M:ℝ)<n := by exact_mod_cast keep
      have nx : (n:ℝ)≤x := (by exact_mod_cast (Finset.mem_Icc.mp hn).2 : (n:ℝ)≤N).trans lo
      exact mul_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr nx)) (by linarith)
    · simp [keep]

private theorem odd_mark {d : ℕ} (nz : marks d≠0) : Odd d := by
  have good : d.Coprime 6 := by
    by_contra bad
    apply nz
    simp [marks,allowed,bad]
  exact Nat.odd_iff.mpr (by
    have h := (Nat.prime_two.coprime_iff_not_dvd.mp (good.of_dvd_right (by decide : 2∣6)).symm)
    omega)

def oddTag (n : ℕ) : ℝ := if Odd n then 1 else 0

theorem odd_mass {n : ℕ} (np : 0<n) :
    (∑ d ∈ n.divisors, (marks d:ℝ)*oddTag (n/d))=
      if ∃ b : ℕ, n=3^b then 1 else 0 := by
  classical
  have factor : (∑ d ∈ n.divisors, (marks d:ℝ)*oddTag (n/d))=
      (divisorMass n:ℝ)*oddTag n := by
    rw [divisorMass,Rat.cast_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases zero : marks d=0
    · simp [zero]
    have od := odd_mark zero
    have eq : Odd (n/d) ↔ Odd n := by
      conv_rhs => rw [←Nat.div_mul_cancel (Nat.mem_divisors.mp hd).1]
      simp [Nat.odd_mul,od]
    simp [oddTag,eq]
  rw [factor]
  by_cases three : ∃ b : ℕ, n=3^b
  · obtain ⟨b,rfl⟩ := three
    have amount : divisorMass (3^b)=1 := by simpa using smooth_source 0 b
    rw [if_pos ⟨b,rfl⟩,amount]
    simp [oddTag,Odd.pow (by decide : Odd 3)]
  · rw [if_neg three]
    by_cases zero : divisorMass n=0
    · simp [zero]
    obtain ⟨a,b,e⟩ := support_exact np zero
    have even : ¬Odd n := by
      rcases a with _|a
      · exfalso;apply three;exact ⟨b,by simpa using e⟩
      · rw [e,pow_succ',Nat.mul_assoc]
        simp
    simp [oddTag,even]

/-- Group all ordinary positive odd multipliers, at a finite cutoff and for an arbitrary test weight. -/
theorem three_feed (N : ℕ) (w : ℕ → ℝ) :
    (∑ r ∈ Finset.Icc 1 N, (oddTag r/(r:ℝ))*∑ d ∈ Finset.Icc 1 (N/r),
      (marks d:ℝ)/d*((r*d:ℕ):ℝ)*w (r*d))=
      ∑ n ∈ Finset.Icc 1 N, if ∃ b : ℕ, n=3^b then w n else 0 := by
  classical
  have h := collect_with N oddTag (fun n => (n:ℝ)*w n)
  simp only [←mul_assoc] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro n hn
  have np : 0<n := (Finset.mem_Icc.mp hn).1
  rw [odd_mass np]
  split_ifs <;> simp [show (n:ℝ)≠0 by positivity]

/-- Transform of the cubic observer with the first summand removed, evaluated at a zeta zero. -/
def cutMultiplier (s : ℂ) :=
  6*(s-1)*(riemannZeta s-1)/((s+1)*(s+2)*(s+3))

theorem sees_zero {s : ℂ} (hs : riemannZeta s=0) (pos : 0<s.re) (one : s≠1) :
    cutMultiplier s≠0 := by
  have plus (n : ℕ) : s+(n:ℂ)≠0 := by
    intro eq
    have v := congrArg Complex.re eq
    simp only [Complex.add_re,Complex.natCast_re,Complex.zero_re] at v
    linarith [Nat.cast_nonneg (α:=ℝ) n]
  rw [cutMultiplier,hs]
  apply div_ne_zero
  · exact mul_ne_zero (mul_ne_zero (by norm_num) (sub_ne_zero.mpr one)) (by norm_num)
  · exact mul_ne_zero (mul_ne_zero (by simpa using plus 1) (by simpa using plus 2)) (by simpa using plus 3)

#print axioms PALRH.CubicWindow.curvature_sum
#print axioms PALRH.CubicWindow.positive_tail
#print axioms PALRH.CubicWindow.three_feed
#print axioms PALRH.CubicWindow.sees_zero
end PALRH.CubicWindow
