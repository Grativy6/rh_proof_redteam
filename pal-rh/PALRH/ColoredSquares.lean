import PALRH.SquareCarry
import PALRH.FactorialReturn

open Finset
open scoped BigOperators
namespace PALRH.ColoredSquares

/-- A switch is assigned once to each prime, then extended multiplicatively. -/
def allowed (u : ℕ → ℤ) : Prop :=
  u 1=1 ∧ (∀ a b : ℕ, u (a*b)=u a*u b) ∧ ∀ a : ℕ, (u a).natAbs≤1

def reading (u : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ a ∈ Icc 1 n, u a*SquareCarry.walk (n/a^2)

noncomputable section
private def applySquares (u f : ℕ → ℝ) (n : ℕ) :=
  ∑ a ∈ Icc 1 n, u a*f (n/a^2)

private theorem group {u g f : ℕ → ℝ} (zero : f 0=0) (n : ℕ) :
    applySquares u (applySquares g f) n =
      ∑ m ∈ Icc 1 n, (∑ j ∈ m.divisors,g j*u (m/j))*f (n/m^2) := by
  have each {a : ℕ} (pa : 0<a) :
      applySquares g f (n/a^2)= ∑ j ∈ Icc 1 (n/a),g j*f (n/(a*j)^2) := by
    have aq : a≤a^2 := Nat.le_self_pow (by decide : 2≠0) a
    have cover : n/a^2≤n/a := (Nat.le_div_iff_mul_le pa).mpr
      ((Nat.mul_le_mul_left (n/a^2) aq).trans (Nat.div_mul_le_self _ _))
    unfold applySquares
    simp_rw [mul_pow,Nat.div_div_eq_div_mul]
    apply sum_subset (fun j hj => mem_Icc.mpr ⟨(mem_Icc.mp hj).1,(mem_Icc.mp hj).2.trans cover⟩)
    intro j hj outside
    have jp := (mem_Icc.mp hj).1
    have far : n/a^2<j := by by_contra! good;exact outside (mem_Icc.mpr ⟨jp,good⟩)
    rw [←Nat.div_div_eq_div_mul,Nat.div_eq_of_lt (far.trans_le (Nat.le_self_pow (by decide : 2≠0) j)),zero,mul_zero]
  unfold applySquares
  calc
    _ = ∑ a ∈ Icc 1 n, u a*∑ j ∈ Icc 1 (n/a),g j*f (n/(a*j)^2) := by
      apply sum_congr rfl
      intro a ha
      exact congrArg (u a*·) (each (mem_Icc.mp ha).1)
    _ = _ := FactorialReturn.products n u g (fun m=>f (n/m^2))

private theorem unit_sum (m : ℕ) :
    (∑ j ∈ m.divisors, (ArithmeticFunction.moebius j:ℝ))=if m=1 then 1 else 0 := by
  have eq:=DFunLike.congr_fun ArithmeticFunction.moebius_mul_coe_zeta m
  rw [ArithmeticFunction.coe_mul_zeta_apply,ArithmeticFunction.one_apply] at eq
  by_cases one : m=1 <;> simp only [one,if_true,if_false] at eq ⊢ <;> exact_mod_cast eq

private theorem cancel {u : ℕ → ℤ} (rule : allowed u) (m : ℕ) :
    (∑ j ∈ m.divisors,(u j:ℝ)*((ArithmeticFunction.moebius (m/j):ℝ)*(u (m/j):ℝ))) =
      if m=1 then 1 else 0 := by
  have rewrite (j : ℕ) (dj : j∈m.divisors) :
      (u j:ℝ)*((ArithmeticFunction.moebius (m/j):ℝ)*(u (m/j):ℝ)) =
        (u m:ℝ)*(ArithmeticFunction.moebius (m/j):ℝ) := by
    have dv := (Nat.mem_divisors.mp dj).1
    have prod := rule.2.1 j (m/j)
    rw [Nat.mul_div_cancel' dv] at prod
    have cast : (u m:ℝ)=(u j:ℝ)*(u (m/j):ℝ) := by exact_mod_cast prod
    rw [cast];ring
  rw [sum_congr rfl rewrite,←mul_sum,Nat.sum_div_divisors m (fun j=>(ArithmeticFunction.moebius j:ℝ)),unit_sum]
  by_cases one : m=1 <;> simp [one,rule.1]

private theorem real_read (u : ℕ → ℤ) (n : ℕ) :
    (reading u n:ℝ)=applySquares (fun a=>(u a:ℝ)) Octaves.walk n := by
  simp [reading,applySquares,SquareCarry.walk,Octaves.walk]

/-- The inverse uses the same square positions and an additional Möbius sign on
their roots. The identity uses only the input up to the stated head. -/
theorem recover {u : ℕ → ℤ} (rule : allowed u) (n : ℕ) :
    (∑ a ∈ Icc 1 n, (ArithmeticFunction.moebius a:ℝ)*(u a:ℝ)*(reading u (n/a^2):ℝ)) =
      Octaves.walk n := by
  simp_rw [real_read]
  change applySquares (fun a=>(ArithmeticFunction.moebius a:ℝ)*(u a:ℝ))
      (applySquares (fun a=>(u a:ℝ)) Octaves.walk) n=_
  rw [group (by simp [Octaves.walk])]
  simp_rw [cancel rule]
  by_cases pos : n=0
  · simp [pos,Octaves.walk]
  rw [sum_eq_single 1]
  · simp
  · intro m _ diff;simp [diff]
  · intro gone;exact False.elim (gone (mem_Icc.mpr ⟨le_rfl,Nat.pos_of_ne_zero pos⟩))

/-- A single choice of prime switches must serve every prefix in the selected
head. A new head can choose its switches independently. -/
def supplied : Prop := ∀ b : ℝ, 1/2<b → ∃ C : ℝ, 0≤C ∧ ∀ n : ℕ,
  ∃ u : ℕ → ℤ, allowed u ∧ ∀ m≤n, |(reading u m:ℝ)|≤C*(m:ℝ)^b

theorem rh_of_switches (hyp : supplied) : RiemannHypothesis := by
  apply Octaves.rh_of_walk_growth
  intro b half
  obtain ⟨C,cn,avail⟩ := hyp b half
  let S:ℝ:= ∑' a:ℕ, 1/(a:ℝ)^(2*b)
  have bp : 0≤b := by linarith
  have sn : 0≤S := tsum_nonneg (fun _=> by positivity)
  refine ⟨C*S,mul_nonneg cn sn,?_⟩
  intro n
  obtain ⟨u,rule,within⟩:=avail n
  rw [←recover rule n]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ a ∈ Icc 1 n, C*(n:ℝ)^b*(1/(a:ℝ)^(2*b)) := by
      apply sum_le_sum
      intro a ha
      have ap : 0<a := (mem_Icc.mp ha).1
      have ar : 0<(a:ℝ) := by exact_mod_cast ap
      have order : (((n/a^2:ℕ):ℝ)*(a:ℝ)^2)≤n := by exact_mod_cast Nat.div_mul_le_self n (a^2)
      have grow:=Real.rpow_le_rpow (by positivity) order bp
      rw [Real.mul_rpow (by positivity) (by positivity),←Real.rpow_natCast_mul ar.le] at grow
      norm_num only [Nat.cast_ofNat] at grow
      have divide := (le_div_iff₀ (Real.rpow_pos_of_pos ar (2*b))).mpr grow
      have term:=(within _ (Nat.div_le_self _ _)).trans (mul_le_mul_of_nonneg_left divide cn)
      have mu : |(ArithmeticFunction.moebius a:ℝ)|≤1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n:=a)
      have sw : |(u a:ℝ)|≤1 := by
        exact_mod_cast ((Int.natCast_natAbs (u a)).symm.le.trans (by exact_mod_cast rule.2.2 a :
          ((u a).natAbs:ℤ)≤1))
      simp only [abs_mul]
      have coeff := mul_le_mul mu sw (abs_nonneg _) (by norm_num : 0≤(1:ℝ))
      have cost:=mul_le_mul_of_nonneg_right coeff (abs_nonneg (reading u (n/a^2):ℝ))
      simp only [one_mul] at cost
      calc
        _ ≤ _ := cost
        _ ≤ _ := term
        _ = _ := by ring
    _ = C*(n:ℝ)^b*∑ a ∈ Icc 1 n, 1/(a:ℝ)^(2*b) := by rw [mul_sum]
    _ ≤ _ := by
      have finite:=(Real.summable_one_div_nat_rpow.mpr (by linarith : 1<2*b)).sum_le_tsum
        (Icc 1 n) (fun _ _ => by positivity)
      change _≤S at finite
      have bound:=mul_le_mul_of_nonneg_left finite (by positivity : 0≤C*(n:ℝ)^b)
      linarith only [bound,show C*S*(n:ℝ)^b=C*(n:ℝ)^b*S by ring]

#print axioms PALRH.ColoredSquares.recover
#print axioms PALRH.ColoredSquares.rh_of_switches
end
end PALRH.ColoredSquares
