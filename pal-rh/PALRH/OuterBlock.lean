import PALRH.CoreMatrix

open Finset
open scoped BigOperators
noncomputable section
namespace PALRH.OuterBlock
open RoughSquares CoreMatrix Octaves

def weight (k : ℕ) : ℝ := 1/((k:ℝ)*(k+1))

private lemma nonneg (k : ℕ) : 0≤weight k := by unfold weight; positivity

private lemma mass {m H : ℕ} (mp : 0<m) (le : m≤H) :
    (∑ k ∈ Finset.Ico m H, weight k)=1/(m:ℝ)-1/(H:ℝ) := by
  have term (k : ℕ) (hk : k∈Finset.Ico m H) :
      weight k=(-1/((k+1:ℕ):ℝ))-(-1/(k:ℝ)) := by
    have kp : 0<k := lt_of_lt_of_le mp (Finset.mem_Ico.mp hk).1
    unfold weight; push_cast; field_simp; ring
  rw [Finset.sum_congr rfl term,Finset.sum_Ico_sub (fun k : ℕ => -1/(k:ℝ)) le]
  ring

private def saved (r k : ℕ) := coreWalk k-coreWalk r

private lemma saved_step (r k : ℕ) : saved r (k+1)=saved r k+core (k+1) := by
  simp only [saved,coreWalk,partialSum,Finset.sum_range_succ]
  ring

private lemma abel (r : ℕ) (rp : 0<r) (H : ℕ) (le : r≤H) :
    (∑ i ∈ Finset.Ioc r H, core i/(i:ℝ)) =
    saved r H/(H:ℝ)+∑ k ∈ Finset.Ico r H, weight k*saved r k := by
  induction H,le using Nat.le_induction with
  | base => simp [saved]
  | succ H le ih =>
    rw [Finset.sum_Ioc_succ_top le,Finset.sum_Ico_succ_top le,ih,saved_step]
    have pos : 0<H := rp.trans_le le
    unfold weight
    push_cast
    field_simp
    ring

private lemma saved_sum (r H : ℕ) (le : r≤H) :
    (∑ i ∈ Finset.Ioc r H, core i)=saved r H := by
  have split : Finset.Icc 1 H=Finset.Icc 1 r ∪ Finset.Ioc r H := by
    ext n; simp only [Finset.mem_union,Finset.mem_Icc,Finset.mem_Ioc]; omega
  have dis : Disjoint (Finset.Icc 1 r) (Finset.Ioc r H) := Finset.disjoint_left.mpr
    (fun _ a b => (not_lt_of_ge (Finset.mem_Icc.mp a).2) (Finset.mem_Ioc.mp b).1)
  simp only [saved,←rough_agrees,roughSum,split,Finset.sum_union dis,add_sub_cancel_left]

private lemma weighted_square (I : Finset ℕ) (a : ℕ → ℝ) :
    (∑ k ∈ I, weight k*a k)^2≤(∑ k ∈ I, weight k)*(∑ k ∈ I, weight k*(a k)^2) := by
  have cs := Finset.sum_mul_sq_le_sq_mul_sq I (fun k => Real.sqrt (weight k))
    (fun k => Real.sqrt (weight k)*a k)
  simpa only [←mul_assoc,Real.mul_self_sqrt (nonneg _),mul_pow,Real.sq_sqrt (nonneg _)] using cs

def outer (H : ℕ) : ℝ :=
  ∑ i ∈ Finset.Ioc (H/2) H, ∑ j ∈ Finset.Ioc (H/2) H,
    core i*core j*(count (H*H/(i*j))-(H:ℝ)^2/(3*(i:ℝ)*j))

private lemma flat {H i j : ℕ} (hi : i∈Finset.Ioc (H/2) H) (hj : j∈Finset.Ioc (H/2) H) :
    count (H*H/(i*j))=1 := by
  obtain ⟨il,iu⟩ := Finset.mem_Ioc.mp hi
  obtain ⟨jl,ju⟩ := Finset.mem_Ioc.mp hj
  have ip : 0 < i := by omega
  have jp : 0<j := by omega
  have ij := Nat.mul_pos ip jp
  have hlo : 1≤H*H/(i*j) := Nat.div_pos (Nat.mul_le_mul iu ju) ij
  have hhi : H*H/(i*j)<5 := by
    apply (Nat.div_lt_iff_lt_mul ij).mpr
    have mul := Nat.mul_lt_mul_of_lt_of_lt (by omega : H<2*i) (by omega : H<2*j)
    nlinarith
  generalize H*H/(i*j)=q at hlo hhi ⊢
  interval_cases q <;> norm_num [count,partialSum,Finset.sum_range_succ,gate]

private lemma outer_value (H : ℕ) :
    outer H = (saved (H/2) H)^2-((H:ℝ)*(∑ i ∈ Finset.Ioc (H/2) H, core i/(i:ℝ)))^2/3 := by
  let I := Finset.Ioc (H/2) H
  have terms (i : ℕ) (hi : i∈I) (j : ℕ) (hj : j∈I) :
      core i*core j*(count (H*H/(i*j))-(H:ℝ)^2/(3*(i:ℝ)*j)) =
      core i*core j-((H:ℝ)^2/3)*(core i/(i:ℝ))*(core j/(j:ℝ)) := by
    rw [flat hi hj]
    ring
  have rewrite_form : outer H=
      (∑ i ∈ I, core i)*(∑ j ∈ I, core j) -
      ((H:ℝ)^2/3)*(∑ i ∈ I, core i/(i:ℝ))*(∑ j ∈ I, core j/(j:ℝ)) := by
    unfold outer
    simp only [Finset.sum_mul,Finset.mul_sum,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [terms i hi j hj]
    ring
  rw [rewrite_form]
  have sum := saved_sum (H/2) H (Nat.div_le_self _ _)
  change (∑ i ∈ I, core i)=_ at sum
  rw [sum]
  dsimp only [I]
  ring

/-- For the true signed vector the entire upper-half square has a lower bound
paid by the earlier physical rough-core octave. -/
theorem outer_funded {H : ℕ} (hH : 2≤H) :
    -((H:ℝ)/2)*price coreWalk (H/2)≤outer H := by
  let r := H/2
  let I := Finset.Ico (r+1) H
  let W := price coreWalk r
  let part := ∑ k ∈ I, weight k*saved r k
  let z := (H:ℝ)*part
  have rp : 0<r := by dsimp [r]; omega
  have smaller : r<H := by dsimp [r]; omega
  have full := abel r rp H smaller.le
  have skip := Finset.sum_Ico_sub_bot (fun k => weight k*saved r k) smaller
  simp only [saved,sub_self,mul_zero,sub_zero] at skip
  change (∑ i ∈ Finset.Ioc r H, core i/(i:ℝ)) = saved r H/(H:ℝ)+_ at full
  have gap : (∑ k ∈ Finset.Ico r H, weight k*saved r k)=part := by simpa only [part,I,saved] using skip
  rw [gap] at full
  have Hpos : 0<(H:ℝ) := by exact_mod_cast (by omega : 0<H)
  have zRel : (H:ℝ)*(∑ i ∈ Finset.Ioc r H, core i/(i:ℝ))=saved r H+z := by
    rw [full]; dsimp only [z]; field_simp
  have small_mass : (∑ k ∈ I, weight k)≤1/(H:ℝ) := by
    rw [mass (by omega : 0<r+1) (by omega : r+1≤H)]
    have old : (H:ℝ)≤2*((r+1:ℕ):ℝ) := by dsimp [r]; exact_mod_cast (by omega : H≤2*(H/2+1))
    apply (sub_le_iff_le_add).mpr
    field_simp
    linarith
  have inside : I ⊆ Finset.Ioc r (2*r) := by
    intro k hk
    obtain ⟨lo,hi⟩ := Finset.mem_Ico.mp hk
    have hh : H≤2*r+1 := by dsimp [r]; omega
    exact Finset.mem_Ioc.mpr ⟨by omega,by omega⟩
  have cap : (∑ k ∈ I, weight k*(saved r k)^2) ≤ W := by
    change _≤price coreWalk r
    dsimp only [price]
    simp only [weight,saved,div_eq_inv_mul,mul_one]
    apply Finset.sum_le_sum_of_subset_of_nonneg inside
    intro k _ _
    positivity
  have cs := (weighted_square I (saved r)).trans (mul_le_mul small_mass cap
    (Finset.sum_nonneg (fun k _ => mul_nonneg (nonneg _) (sq_nonneg _))) (by positivity))
  change part^2≤1/(H:ℝ)*W at cs
  have pay : z^2≤(H:ℝ)*W := by
    have up := mul_le_mul_of_nonneg_left cs (sq_nonneg (H:ℝ))
    have he : (H:ℝ)^2*(1/H*W)=H*W := by field_simp
    rw [he] at up
    simpa only [z,mul_pow] using up
  rw [outer_value]
  change -((H:ℝ)/2)*W ≤ (saved r H)^2-((H:ℝ)*(∑ i ∈ Finset.Ioc r H, core i/(i:ℝ)))^2/3
  rw [zRel]
  nlinarith [sq_nonneg (2*saved r H-z)]

#print axioms PALRH.OuterBlock.outer_funded
end PALRH.OuterBlock
