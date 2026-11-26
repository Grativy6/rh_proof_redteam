import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

open Finset
open scoped BigOperators

namespace PALRH.ExpiringCredit

/-- A positive excess spends a pocket cell. The net and absolute totals determine exactly
how many such cells are spent by a partition whose remainders expire. -/
theorem lost_and_kept {ι : Type*} (I : Finset ι) (demand room : ι → ℕ) :
    2*(∑ i ∈ I,(demand i-room i))+(∑ i ∈ I,room i)=
      (∑ i ∈ I,((demand i-room i)+(room i-demand i)))+(∑ i ∈ I,demand i) := by
  rw [Finset.mul_sum,←sum_add_distrib,←sum_add_distrib]
  apply sum_congr rfl
  intro i _
  omega

theorem separated_groups_cost {ι : Type*} (I good : Finset ι) (demand room : ι → ℕ)
    (subset : good⊆I) {price net : ℕ}
    (separated : ∀ i∈good, price≤(demand i-room i)+(room i-demand i))
    (balanced : (∑ i ∈ I,room i)≤(∑ i ∈ I,demand i)+net) :
    good.card*price≤2*(∑ i ∈ I,(demand i-room i))+net := by
  have bound : good.card*price≤∑ i ∈ I,((demand i-room i)+(room i-demand i)) := by
    calc
      _ = ∑ _ ∈ good,price := by simp
      _ ≤ ∑ i ∈ good,((demand i-room i)+(room i-demand i)) := sum_le_sum separated
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg subset (fun _ _ _ => Nat.zero_le _)
  have split:=lost_and_kept I demand room
  omega

/-- A single interval of log prices is simultaneously separated from integer column
counts for every possible block length from one through r. -/
theorem phase_gap (r s a g : ℕ) (sp : 1≤s) (sr : s≤r) {y : ℝ}
    (near : |y-((a:ℝ)+1/((r:ℝ)+1))|≤1/(4*r*((r:ℝ)+1))) :
    3/(4*((r:ℝ)+1))≤|(s:ℝ)*y-g| := by
  have rp : 0<(r:ℝ) := by exact_mod_cast (sp.trans sr)
  have sr' : (s:ℝ)≤r := by exact_mod_cast sr
  have so : 1≤(s:ℝ) := by exact_mod_cast sp
  let h:ℝ:=1/((r:ℝ)+1)
  let w:ℝ:=1/(4*r*((r:ℝ)+1))
  have hp : 0<h := by dsimp [h];positivity
  have wn : 0≤w := by dsimp [w];positivity
  have rw' : (r:ℝ)*w=h/4 := by dsimp [h,w];field_simp
  have rh : (r:ℝ)*h=1-h := by dsimp [h];field_simp;ring
  have dist : |(s:ℝ)*(y-(a+h))|≤h/4 := by
    rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg _),←rw']
    exact mul_le_mul (le_refl _) near (abs_nonneg _) (Nat.cast_nonneg _) |>.trans
      (mul_le_mul_of_nonneg_right sr' wn)
  have radius : 3/(4*((r:ℝ)+1))=3*h/4 := by dsimp [h];field_simp
  rw [radius]
  have low : h≤(s:ℝ)*h := by calc
    _ = 1*h := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right so hp.le
  have high : (s:ℝ)*h≤1-h := rh ▸ mul_le_mul_of_nonneg_right sr' hp.le
  have left:= (abs_le.mp dist).1
  have right:= (abs_le.mp dist).2
  by_cases before : g≤s*a
  · have b : (g:ℝ)≤s*a := by exact_mod_cast before
    apply le_trans _ (le_abs_self _)
    nlinarith only [left,low,b]
  · have b : (s:ℝ)*a+1≤g := by exact_mod_cast (by omega : s*a+1≤g)
    apply le_trans _ (neg_le_abs _)
    nlinarith only [right,high,b]

#print axioms PALRH.ExpiringCredit.separated_groups_cost
#print axioms PALRH.ExpiringCredit.phase_gap
end PALRH.ExpiringCredit
