import PALRH.Octaves

open Finset
open scoped BigOperators
namespace PALRH.SquareCarry

def walk (n : ℕ) : ℤ := ∑ m ∈ Icc 1 n, ArithmeticFunction.moebius m

def lifted (a : ℕ) (c : ℤ) (n : ℕ) : ℤ :=
  if a^2 ∣ n then c*ArithmeticFunction.moebius (n/a^2) else 0

def remaining (a : ℕ) (c : ℤ) (n : ℕ) : ℤ := walk n-c*walk (n/a^2)

private theorem multiples (a N : ℕ) (_pos : 0<a) (f : ℕ → ℤ) :
    (∑ n ∈ Icc 1 N, if a ∣ n then f (n/a) else 0)=∑ m ∈ Icc 1 (N/a), f m := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_Icc_succ_top (by omega : 1≤N+1),ih]
    by_cases dv : a ∣ N+1
    · rw [if_pos dv,Nat.succ_div_of_dvd dv,sum_Icc_succ_top (Nat.succ_le_succ (Nat.zero_le (N/a)))]
    · rw [if_neg dv,Nat.succ_div_of_not_dvd dv,add_zero]

theorem prefix_sum {a : ℕ} (pos : 0<a) (c : ℤ) (n : ℕ) :
    (∑ m ∈ Icc 1 n, (ArithmeticFunction.moebius m-lifted a c m))=remaining a c n := by
  rw [sum_sub_distrib]
  unfold lifted remaining walk
  rw [multiples (a^2) n (pow_pos pos 2) (fun j => c*ArithmeticFunction.moebius j),mul_sum]

theorem disjoint {a : ℕ} (large : 2≤a) (c : ℤ) (n : ℕ) :
    ArithmeticFunction.moebius n * lifted a c n = 0 := by
  unfold lifted
  split_ifs with dv
  · have bad : ¬ Squarefree n := by
      intro sq
      have one := sq a (by simpa [pow_two] using dv)
      have eq : a=1 := Nat.isUnit_iff.mp one
      omega
    rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree bad,zero_mul]
  · simp

theorem squared_steps {a : ℕ} (large : 2≤a) (c : ℤ) (n : ℕ) :
    (∑ m ∈ Icc 1 n, (ArithmeticFunction.moebius m-lifted a c m)^2)=
      (∑ m ∈ Icc 1 n, (ArithmeticFunction.moebius m)^2)+
      c^2*∑ m ∈ Icc 1 (n/a^2), (ArithmeticFunction.moebius m)^2 := by
  have per (m : ℕ) :
      (ArithmeticFunction.moebius m-lifted a c m)^2=(ArithmeticFunction.moebius m)^2+
        (if a^2 ∣ m then c^2*(ArithmeticFunction.moebius (m/a^2))^2 else 0) := by
    have id := disjoint large c m
    unfold lifted at id ⊢
    split_ifs at id ⊢ <;> nlinarith only [id]
  simp_rw [per]
  rw [sum_add_distrib,multiples (a^2) n (by positivity) (fun j=> c^2*(ArithmeticFunction.moebius j)^2),mul_sum]

/-- The square root of the dilation gives exact equality of the two mean-square
step energies on their respective complete boards. -/
theorem balanced_energy {a : ℕ} (large : 2≤a) (n : ℕ) :
    (∑ m ∈ Icc 1 (a^2*n), (lifted a (a:ℤ) m)^2)=
      (a:ℤ)^2*∑ m ∈ Icc 1 n, (ArithmeticFunction.moebius m)^2 := by
  have per (m : ℕ) : (lifted a (a:ℤ) m)^2=
      (if a^2 ∣ m then (a:ℤ)^2*(ArithmeticFunction.moebius (m/a^2))^2 else 0) := by
    unfold lifted
    split_ifs <;> ring
  simp_rw [per]
  have pos : 0<a^2 := by positivity
  rw [multiples (a^2) (a^2*n) pos (fun j => (a:ℤ)^2*(ArithmeticFunction.moebius j)^2),Nat.mul_div_cancel_left _ pos,mul_sum]

noncomputable section
private theorem real_walk (n : ℕ) : (walk n:ℝ)=Octaves.walk n := by
  simp [walk,Octaves.walk]

private theorem parent_cost {a n : ℕ} (large : 2≤a) {b : ℝ} (half : 1/2<b) :
    (a:ℝ)*(n/a^2:ℕ)^b*(2:ℝ)^(2*b-1)≤(n:ℝ)^b := by
  have aa : 2≤(a:ℝ) := by exact_mod_cast large
  have ap : 0<(a:ℝ) := by linarith
  have bp : 0≤b := by linarith
  have sized : (((n/a^2:ℕ):ℝ)*(a:ℝ)^2)≤n := by exact_mod_cast Nat.div_mul_le_self n (a^2)
  have total := Real.rpow_le_rpow (by positivity) sized bp
  rw [Real.mul_rpow (by positivity) (by positivity)] at total
  have scale := Real.rpow_le_rpow (by norm_num : 0≤(2:ℝ)) aa (by linarith : 0≤2*b-1)
  have equal : (a:ℝ)*(a:ℝ)^(2*b-1)=((a:ℝ)^2)^b := by
    rw [←Real.rpow_natCast_mul ap.le]
    norm_num
    conv_lhs => lhs; rw [←Real.rpow_one (a:ℝ)]
    rw [←Real.rpow_add ap]
    congr 1; ring
  have price := mul_le_mul_of_nonneg_left scale (by positivity : 0≤(a:ℝ)*((n/a^2:ℕ):ℝ)^b)
  calc
    _ ≤ (a:ℝ)*((n/a^2:ℕ):ℝ)^b*(a:ℝ)^(2*b-1) := price
    _ = ((n/a^2:ℕ):ℝ)^b*((a:ℝ)^2)^b := by rw [←equal];ring
    _ ≤ _ := total

/-- Each row may pick its own older square dilation and sign, at the exact
square-root amplitude ceiling. The displayed residual is in integer units. -/
def supplied : Prop := ∀ q : ℕ, 0<q → ∃ K : ℕ, ∀ n : ℕ, K≤n →
  ∃ a : ℕ, 2≤a ∧ ∃ c : ℤ, c.natAbs≤a ∧ (remaining a c n).natAbs^(2*q)≤n^(q+1)

private theorem choose_bound (supply : supplied) {b : ℝ} (half : 1/2<b) :
    ∃ C : ℝ, 0≤C ∧ ∀ n : ℕ, 0<n →
      ∃ a : ℕ, 2≤a ∧ ∃ c : ℤ, c.natAbs≤a ∧ |(remaining a c n:ℝ)|≤C*(n:ℝ)^b := by
  obtain ⟨i,rate⟩ := exists_nat_one_div_lt (show 0<b-1/2 by linarith)
  let q:=i+1
  have qp : 0<q := Nat.succ_pos _
  have qr : 0<(q:ℝ) := by exact_mod_cast qp
  have small : 1/(q:ℝ)<b-1/2 := by simpa [q] using rate
  have exponent : ((q:ℝ)+1)/(2*q)≤b := by
    rw [show ((q:ℝ)+1)/(2*q)=1/2+(1/q)/2 by field_simp]
    linarith only [small,half]
  obtain ⟨K,late⟩:=supply q qp
  let early:=∑ j ∈ range (K+1), |(walk j:ℝ)|
  have en : 0≤early := sum_nonneg (fun _ _ => abs_nonneg _)
  refine ⟨1+early,by linarith,?_⟩
  intro n pos
  have nr : 1≤(n:ℝ) := by exact_mod_cast pos
  have bp : 0≤b := by linarith
  have unit := Real.one_le_rpow nr bp
  by_cases h : K≤n
  · obtain ⟨a,al,c,cap,count⟩:=late n h
    refine ⟨a,al,c,cap,?_⟩
    have cast : ((remaining a c n).natAbs:ℝ)^(2*q)≤(n:ℝ)^(q+1) := by exact_mod_cast count
    have pow := Real.rpow_le_rpow (by positivity) cast (by positivity : (0:ℝ)≤1/(2*q))
    simp only [←Real.rpow_natCast_mul (Nat.cast_nonneg (α:=ℝ) _),Nat.cast_mul,
      Nat.cast_add,Nat.cast_ofNat,Nat.cast_one] at pow
    rw [show (2*(q:ℝ))*(1/(2*q))=1 by field_simp,Real.rpow_one,
      show ((q:ℝ)+1)*(1/(2*q))=((q:ℝ)+1)/(2*q) by ring] at pow
    have absEq : |(remaining a c n:ℝ)|=((remaining a c n).natAbs:ℝ) := by
      calc
        _ = ((|(remaining a c n)|:ℤ):ℝ) := by simp
        _ = (((remaining a c n).natAbs:ℤ):ℝ) :=
          congrArg (fun z : ℤ => (z:ℝ)) (Int.natCast_natAbs (remaining a c n)).symm
        _ = _ := by simp
    rw [absEq]
    exact (pow.trans (Real.rpow_le_rpow_of_exponent_le nr exponent)).trans
      (by nlinarith only [mul_nonneg en (zero_le_one.trans unit)])
  · refine ⟨2,by decide,0,by decide,?_⟩
    have term:=single_le_sum (s:=range (K+1)) (f:=fun j=>|(walk j:ℝ)|)
      (fun _ _=> abs_nonneg _) (mem_range.mpr (by omega : n<K+1))
    change |(walk n:ℝ)|≤early at term
    simp only [remaining,zero_mul,sub_zero]
    nlinarith only [term,unit,mul_le_mul_of_nonneg_left unit en]

theorem rh_of_square_returns (supply : supplied) : RiemannHypothesis := by
  apply Octaves.rh_of_walk_growth
  intro b half
  obtain ⟨C,cn,pay⟩:=choose_bound supply half
  let Q:ℝ:=(2:ℝ)^(2*b-1)
  have q1 : 1<Q := Real.one_lt_rpow (by norm_num) (by linarith)
  let H:=C*Q/(Q-1)
  have hn : 0≤H := div_nonneg (mul_nonneg cn (by linarith)) (by linarith)
  have balance : H*Q=C*Q+H := by
    dsimp [H]
    field_simp [sub_ne_zero.mpr (ne_of_gt q1)]
    ring
  refine ⟨H,hn,?_⟩
  intro n
  rw [←real_walk]
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases zero : n=0
    · subst n
      simp [walk,Real.zero_rpow (by linarith : b≠0)]
    have np:=Nat.pos_of_ne_zero zero
    obtain ⟨a,al,c,cap,fee⟩:=pay n np
    have atwo : 1<a^2 := by nlinarith only [Nat.pow_le_pow_left al 2]
    have before:=ih (n/a^2) (Nat.div_lt_self np atwo)
    have ar : 0≤(a:ℝ) := Nat.cast_nonneg _
    have magnitude : |(c:ℝ)|≤a := by exact_mod_cast ((Int.natCast_natAbs c).symm.le.trans
      (by exact_mod_cast cap : ((c.natAbs:ℕ):ℤ)≤(a:ℤ)))
    have pred:=mul_le_mul magnitude before (abs_nonneg _) ar
    have identity : (walk n:ℝ)=(remaining a c n:ℝ)+(c:ℝ)*(walk (n/a^2):ℝ) := by
      unfold remaining
      push_cast
      ring
    have triangle:=abs_add_le (remaining a c n:ℝ) ((c:ℝ)*(walk (n/a^2):ℝ))
    rw [←identity,abs_mul] at triangle
    have curr:=mul_le_mul_of_nonneg_right (triangle.trans (add_le_add fee pred)) (by linarith : 0≤Q)
    have cost:=mul_le_mul_of_nonneg_left (parent_cost (n:=n) al half) hn
    change H*((a:ℝ)*((n/a^2:ℕ):ℝ)^b*Q)≤_ at cost
    have ident:=congrArg (fun x : ℝ => x*(n:ℝ)^b) balance
    apply le_of_mul_le_mul_right (a:=Q) _ (by linarith)
    nlinarith only [curr,cost,ident]

#print axioms PALRH.SquareCarry.prefix_sum
#print axioms PALRH.SquareCarry.squared_steps
#print axioms PALRH.SquareCarry.balanced_energy
#print axioms PALRH.SquareCarry.rh_of_square_returns
end
end PALRH.SquareCarry
