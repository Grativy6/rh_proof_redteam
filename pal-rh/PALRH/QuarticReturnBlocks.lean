import PALRH.QuarticBoards
import PALRH.MovingEndpoint

open Finset
open scoped BigOperators
noncomputable section
namespace PALRH.QuarticReturnBlocks
open LinearPrimeIntegral QuarticBoards

/-- The slope of the centered prime-power area between successive integer marks. -/
def drift (n : ℕ) : ℝ := MovingEndpoint.slope n - n - 1/2

theorem step (n : ℕ) : error (n+1)-error n=drift n := by
  have increment : fullWalk (n+1)=fullWalk n+MovingEndpoint.slope n := by
    unfold fullWalk MovingEndpoint.slope
    rw [sum_Icc_succ_top (by omega : 1≤n+1)]
    simp only [sub_self,zero_mul,add_zero,Nat.cast_succ]
    rw [←sum_add_distrib]
    apply sum_congr rfl
    intro d _
    ring
  unfold error drift
  rw [increment]
  push_cast
  ring

private theorem interval_price {a b : ℕ} (ab : a≤b) (s D : ℝ)
    (localBound : ∀ u : ℕ, a≤u → u<b → |drift u-s|≤D) :
    |error b-error a-((b:ℝ)-a)*s| ≤ ((b:ℝ)-a)*D := by
  induction b,ab using Nat.le_induction with
  | base => simp
  | succ b ab old =>
    have stored:=old (fun u hu ub => localBound u hu (by omega))
    have last:=localBound b ab (Nat.lt_succ_self _)
    have ident : error (b+1)-error a-(((b+1:ℕ):ℝ)-a)*s =
        (error b-error a-((b:ℝ)-a)*s)+(drift b-s) := by
      have h:=step b
      push_cast
      linarith only [h]
    rw [ident]
    have est := (abs_add_le _ _).trans (add_le_add stored last)
    push_cast
    linarith only [est]

/-- One side of a good head keeps its upper price, even if the center has a large
unknown absolute drift. Only the change in that drift is charged. -/
theorem good_side (m H : ℕ) {D : ℝ} (dn : 0≤D)
    (localBound : ∀ u : ℕ, m-H≤u → u≤m+H → |drift u-drift m|≤D) :
    (∀ t : ℕ, m-H≤t → t≤m → error t≤error m+H*D) ∨
    (∀ t : ℕ, m≤t → t≤m+H → error t≤error m+H*D) := by
  rcases le_total 0 (drift m) with up|down
  · left
    intro t lo hi
    have h:=interval_price hi (drift m) D (fun u tu um => localBound u (by omega) (by omega))
    have len : (m:ℝ)-(t:ℝ)≤H := by
      apply sub_le_iff_le_add.mpr
      exact_mod_cast (show m≤H+t by omega)
    have dpos : 0≤(m:ℝ)-(t:ℝ) := sub_nonneg.mpr (by exact_mod_cast hi)
    have lower := (abs_le.mp h).1
    nlinarith only [lower,mul_le_mul_of_nonneg_right len dn,mul_nonneg dpos up]
  · right
    intro t lo hi
    have h:=interval_price lo (drift m) D (fun u mu ut => localBound u (by omega) (by omega))
    have len : (t:ℝ)-(m:ℝ)≤H := by
      apply sub_le_iff_le_add.mpr
      exact_mod_cast (show t≤H+m by omega)
    have dpos : 0≤(t:ℝ)-(m:ℝ) := sub_nonneg.mpr (by exact_mod_cast lo)
    have upper := (abs_le.mp h).2
    nlinarith only [upper,mul_le_mul_of_nonneg_right len dn,mul_nonpos_of_nonneg_of_nonpos dpos down]

private theorem fourth_gap {a b : ℕ} (ab : a≤b) : b^4 ≤ a^4 + 4*(b-a)*b^3 := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le ab
  rw [Nat.add_sub_cancel_left]
  have non : 0 ≤ 6*a^2*d^2+8*a*d^3+3*d^4 := Nat.zero_le _
  nlinarith only [non]

/-- Both directions contain an explicitly counted run of consecutive quartic heads. -/
theorem consecutive (m H j B : ℕ) (fit : B≤j) (leftHead : j^4≤m) (rightHead : m≤(j+1)^4)
    (width : 4*(B+1)*(j+B+1)^3≤H) {D : ℝ} (dn : 0≤D)
    (localBound : ∀ u : ℕ, m-H≤u → u≤m+H → |drift u-drift m|≤D) :
    (∀ i≤B, error ((j-i)^4)≤error m+H*D) ∨
    (∀ i≤B, error ((j+1+i)^4)≤error m+H*D) := by
  rcases good_side m H dn localBound with leftAll|rightAll
  · left
    intro i ib
    have ij:=ib.trans fit
    have gap:=fourth_gap (show j-i≤j+1 by omega)
    have span : j+1-(j-i)=i+1 := by omega
    rw [span] at gap
    have cost := Nat.mul_le_mul
      (show 4*(i+1)≤4*(B+1) by omega)
      (Nat.pow_le_pow_left (show j+1≤j+B+1 by omega) 3)
    exact leftAll _ (by omega) ((Nat.pow_le_pow_left (Nat.sub_le j i) 4).trans leftHead)
  · right
    intro i ib
    have gap:=fourth_gap (show j≤j+1+i by omega)
    rw [show j+1+i-j=i+1 by omega] at gap
    have cost := Nat.mul_le_mul
      (show 4*(i+1)≤4*(B+1) by omega)
      (Nat.pow_le_pow_left (show j+1+i≤j+B+1 by omega) 3)
    exact rightAll _ (rightHead.trans (Nat.pow_le_pow_left (by omega : j+1≤j+1+i) 4)) (by omega)

#print axioms PALRH.QuarticReturnBlocks.step
#print axioms PALRH.QuarticReturnBlocks.good_side
#print axioms PALRH.QuarticReturnBlocks.consecutive
end PALRH.QuarticReturnBlocks
