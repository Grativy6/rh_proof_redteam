import PALRH.PrimeOpening

open Finset
open scoped BigOperators
noncomputable section
namespace PALRH.Smoothed
open CoreMatrix RoughSquares

/-- Two discrete integrations of an actual threshold reading. With a cumulative
arithmetic input this gives squared triangular weights, before division by x^2. -/
def twice (f : ℕ → ℝ) (x : ℕ) : ℝ :=
  ∑ k ∈ Finset.range x, (2*((x:ℝ)-k)-1)*f k

private lemma twice_step (f : ℕ → ℝ) (n : ℕ) :
    twice f (n+1)-twice f n=f n+2*∑ k ∈ Finset.range n, f k := by
  unfold twice
  rw [Finset.sum_range_succ]
  push_cast
  have terms (k : ℕ) : (2*((n:ℝ)+1-k)-1)*f k=(2*((n:ℝ)-k)-1)*f k+2*f k := by ring
  simp_rw [terms]
  rw [Finset.sum_add_distrib,←Finset.mul_sum]
  ring

theorem threshold_difference (f : ℕ → ℝ) (n : ℕ) :
    twice f (n+2)-2*twice f (n+1)+twice f n=f n+f (n+1) := by
  have a := twice_step f n
  have b := twice_step f (n+1)
  rw [Finset.sum_range_succ] at b
  linarith

/-- The coefficient that enters at i+1 receives the exact square of its remaining
distance from x. This identity holds for any sequence. -/
theorem twice_partial (a : ℕ → ℝ) (x : ℕ) :
    twice (partialSum a) x = ∑ i ∈ Finset.range x, a (i+1)*((x:ℝ)-(i+1))^2 := by
  let B := fun n : ℕ => ∑ i ∈ Finset.range n, a (i+1)*((n:ℝ)-(i+1))^2
  have second (n : ℕ) : B (n+2)-2*B (n+1)+B n=partialSum a n+partialSum a (n+1) := by
    dsimp only [B,partialSum]
    rw [show n+2=n+1+1 by omega]
    simp only [Finset.sum_range_succ,Nat.cast_add,Nat.cast_one,sub_self,zero_pow (by decide : 2≠0),
      mul_zero,add_zero]
    have h (i : ℕ) : a (i+1)*((n:ℝ)+1+1-(i+1))^2 =
        2*(a (i+1)*((n:ℝ)+1-(i+1))^2)-a (i+1)*((n:ℝ)-(i+1))^2+2*a (i+1) := by ring
    simp_rw [h]
    simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum]
    ring
  change twice (partialSum a) x=B x
  induction x using Nat.twoStepInduction with
  | zero => simp [twice,B]
  | one => simp [twice,partialSum,B]
  | more n n0 n1 =>
    have h := threshold_difference (partialSum a) n
    rw [n0,n1] at h
    linarith [second n]

private lemma extend_zero {h x : ℕ} (le : x≤h) : form h x=form x x := by
  let I := indices x
  let J := indices h
  have sub : I⊆J := fun i hi => Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hi).1,(Finset.mem_Icc.mp hi).2.trans le⟩
  have vanish (i j : ℕ) (hi : i∈J) (hj : j∈J) (missing : i∉I) :
      core i*core j*count (x/(i*j))=0 := by
    have ip := (Finset.mem_Icc.mp hi).1
    have jp := (Finset.mem_Icc.mp hj).1
    have far : x < i := by
      by_contra! back; exact missing (Finset.mem_Icc.mpr ⟨ip,back⟩)
    have bigger : i ≤ i*j := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left i jp
    simp [Nat.div_eq_of_lt (far.trans_le bigger),count,partialSum]
  have crop (S : Finset ℕ) (inside : S⊆J) : block I S x=block J S x := by
    apply Finset.sum_subset sub
    intro i hi missing
    exact Finset.sum_eq_zero (fun j hj => vanish i j hi (inside hj) missing)
  have flip (S T : Finset ℕ) : block S T x=block T S x := by
    unfold block
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    rw [Nat.mul_comm i j,mul_comm (core i) (core j)]
  symm
  change block I I x=block J J x
  rw [crop I sub,flip J I,crop J (by rfl)]

private lemma clamped {H n : ℕ} (hi : n<(H+1)*(H+1)) :
    coreWalk n=2*coreWalk (min H n)-form H n := by
  rcases le_total H n with h|h
  · rw [min_eq_left h]
    exact square_sweep h hi
  · rw [min_eq_right h,extend_zero h]
    exact square_sweep le_rfl (by nlinarith : n<(n+1)*(n+1))

theorem smooth_square (H : ℕ) :
    twice coreWalk (H*H)=2*twice (fun n => coreWalk (min H n)) (H*H)-twice (form H) (H*H) := by
  unfold twice
  rw [Finset.mul_sum,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have h := Finset.mem_range.mp hn
  have full := clamped (H:=H) (n:=n) (by nlinarith)
  linear_combination (2*((H*H:ℕ):ℝ)-2*(n:ℝ)-1)*full

theorem reversing_at_square {H : ℕ} (hH : 1<H) :
    twice (form H) (H*H+1)-2*twice (form H) (H*H)+twice (form H) (H*H-1)=2*form H (H*H) := by
  have pos : 0<H*H := by positivity
  have h := threshold_difference (form H) (H*H-1)
  rw [show H*H-1+2=H*H+1 by omega,show H*H-1+1=H*H by omega,
    ←square_jump_vanishes hH] at h
  linarith

/-- The accumulated side reading up to and including zero-based row i. -/
def previous (a : ℕ → ℝ) (i : ℕ) := ∑ k ∈ Finset.range (i+1), a k

def sideCost (a : ℕ → ℝ) (N : ℕ) := ∑ i ∈ Finset.range N, |previous a i|/((i:ℝ)+1)

private lemma parts (a f : ℕ → ℝ) (N : ℕ) :
    (∑ i ∈ Finset.range (N+1), a i*f i)=previous a N*f N+
      ∑ i ∈ Finset.range N, previous a i*(f i-f (i+1)) := by
  induction N with
  | zero => simp [previous]
  | succ N old =>
    rw [Finset.sum_range_succ,old,Finset.sum_range_succ (f:=fun i => previous a i*(f i-f (i+1)))]
    have next : previous a (N+1)=previous a N+a (N+1) := Finset.sum_range_succ _ _
    rw [next]
    ring

private lemma side_estimate (a f : ℕ → ℝ) (N : ℕ) (b c : ℝ) (end_bound : |f N|≤b)
    (changes : ∀ i<N, |f i-f (i+1)|≤c/((i:ℝ)+1)) :
    |∑ i ∈ Finset.range (N+1), a i*f i|≤b*|previous a N|+c*sideCost a N := by
  rw [parts]
  apply (abs_add_le _ _).trans
  apply add_le_add
  · rw [abs_mul,mul_comm]
    exact mul_le_mul_of_nonneg_right end_bound (abs_nonneg _)
  · apply (Finset.abs_sum_le_sum_abs _ _).trans
    unfold sideCost
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    rw [abs_mul]
    calc
      _ ≤ |previous a i| *(c/((i:ℝ)+1)) := mul_le_mul_of_nonneg_left (changes i (Finset.mem_range.mp hi)) (abs_nonneg _)
      _ = _ := by ring

/-- Side information suffices for a kernel whose first and mixed differences are
funded. The twice-averaged rough census supplies the constants 1,4,12 on paper. -/
theorem matrix_transfer (a : ℕ → ℝ) (K : ℕ → ℕ → ℝ) (N : ℕ) {b : ℝ}
    (end_bound : |K N N|≤b)
    (last_row : ∀ j<N, |K N j-K N (j+1)|≤4*b/((j:ℝ)+1))
    (last_col : ∀ i<N, |K i N-K (i+1) N|≤4*b/((i:ℝ)+1))
    (mixed : ∀ i<N, ∀ j<N, |(K i j-K (i+1) j)-(K i (j+1)-K (i+1) (j+1))|≤
      12*b/(((i:ℝ)+1)*((j:ℝ)+1))) :
    let U := |previous a N|
    let L := sideCost a N
    |∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (N+1), a i*a j*K i j| ≤
      b*U^2+8*b*U*L+12*b*L^2 := by
  let U := |previous a N|
  let L := sideCost a N
  let Y := fun i => ∑ j ∈ Finset.range (N+1), a j*K i j
  have endY : |Y N|≤b*U+4*b*L := side_estimate a (K N) N _ _ end_bound last_row
  have diff (i : ℕ) (hi : i<N) : |Y i-Y (i+1)| ≤ (4*b*U+12*b*L)/((i:ℝ)+1) := by
    have eq : Y i-Y (i+1)=∑ j ∈ Finset.range (N+1), a j*(K i j-K (i+1) j) := by
      simp only [Y,mul_sub,Finset.sum_sub_distrib]
    rw [eq]
    apply (side_estimate a (fun j => K i j-K (i+1) j) N (4*b/((i:ℝ)+1)) (12*b/((i:ℝ)+1))
      (last_col i hi) (fun j hj => (mixed i hi j hj).trans_eq (by field_simp))).trans_eq
    dsimp only [U,L]
    ring
  have total := side_estimate a Y N _ _ endY diff
  have eq : (∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (N+1), a i*a j*K i j)=
      ∑ i ∈ Finset.range (N+1), a i*Y i := by simp only [Y,Finset.mul_sum,mul_assoc]
  rw [eq]
  change _ ≤ b*U^2+8*b*U*L+12*b*L^2
  exact total.trans_eq (by dsimp only [U,L];ring)

#print axioms PALRH.Smoothed.smooth_square
#print axioms PALRH.Smoothed.twice_partial
#print axioms PALRH.Smoothed.reversing_at_square
#print axioms PALRH.Smoothed.matrix_transfer

private theorem count_multiples (d n : ℕ) :
    partialSum (fun k => if d ∣ k then gate (k/d) else 0) n=count (n/d) := by
  induction n with
  | zero => simp [partialSum,count]
  | succ n old =>
    by_cases hit : d ∣ n+1
    · simp only [partialSum,Finset.sum_range_succ,count,Nat.succ_div_of_dvd hit,if_pos hit] at old ⊢
      rw [old]
    · simp only [partialSum,Finset.sum_range_succ,count,Nat.succ_div_of_not_dvd hit,if_neg hit,add_zero] at old ⊢
      exact old

/-- Entry by entry, the averaged threshold is an exact squared polynomial weight
on multiples of the actual product. -/
theorem twice_census (d x : ℕ) :
    twice (fun k => count (k/d)) x =
      ∑ i ∈ Finset.range x, (if d ∣ i+1 then gate ((i+1)/d) else 0)*((x:ℝ)-(i+1))^2 := by
  have eq : (fun k => count (k/d))=partialSum (fun k => if d ∣ k then gate (k/d) else 0) :=
    funext (fun k => (count_multiples d k).symm)
  rw [eq,twice_partial]

theorem twice_form (H x : ℕ) :
    twice (form H) x=∑ i ∈ indices H, ∑ j ∈ indices H,
      core i*core j*twice (fun k => count (k/(i*j))) x := by
  unfold twice form block
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

#print axioms PALRH.Smoothed.twice_form
#print axioms PALRH.Smoothed.twice_census

end PALRH.Smoothed
