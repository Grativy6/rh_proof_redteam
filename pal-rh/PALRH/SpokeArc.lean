import PALRH.PhaseBound
import PALRH.ProductBridge

open Finset
open scoped BigOperators

noncomputable section
namespace PALRH.SpokeArc
open ShapeObservation ProductClock ReturnedHorizon

def pulse (j m : ℕ) : ℤ :=
  (tickSum (board j) m:ℤ)-(root j:ℤ)*((m-root j:ℕ):ℤ)
def radius (j : ℕ) : ℤ := (root j:ℤ)*(root j/13:ℕ)
def inArc (j m : ℕ) : Prop :=
  let n:ℤ:=board j
  let r:=pulse j m % n
  r≤radius j ∨ n-radius j≤r

private theorem speed {j i : ℕ} (live : i<16^j) :
    |pulse j (i+1)-pulse j i|+2*radius j<(board j:ℤ) := by
  let x:=root j
  let n:=board j
  have xp : 0<x := by dsimp [x,root];positivity
  have nx : n.sqrt=x := Nat.sqrt_eq' _
  have cap : 2*(4*j+1)≤x := by
    have four : 4≤4^(j+1) := by
      rw [pow_succ]
      have yes : 0<(4:ℕ)^j := by positivity
      omega
    dsimp [x,root]
    nlinarith only [Nat.mul_le_mul_right ((j+1)^2) four,Nat.zero_le (j^2)]
  have bounds : i+1≤2^(4*j) := by
    rw [pow_mul];exact live
  have ticks : tickAt n (i+1)≤(4*j)*x := by
    unfold tickAt
    split_ifs
    · rw [nx];exact TickBoard.bit_price xp bounds
    · omega
  have sumstep : tickSum n (i+1)=tickSum n i+tickAt n (i+1) := by
    unfold tickSum;rw [sum_Icc_succ_top (by omega : 1 ≤ i+1)]
  have diff : |pulse j (i+1)-pulse j i|≤((4*j+1)*x:ℕ) := by
    unfold pulse
    change |(tickSum n (i+1):ℤ)-(x:ℤ)*((i+1-x:ℕ):ℤ)-((tickSum n i:ℤ)-(x:ℤ)*((i-x:ℕ):ℤ))|≤_
    rw [sumstep, Nat.cast_add]
    have fee : (tickAt n (i+1):ℤ)≤(4*(j:ℤ))*(x:ℤ) := by exact_mod_cast ticks
    have xn : 0≤(x:ℤ) := Nat.cast_nonneg _
    by_cases inside : i<x
    · rw [Nat.sub_eq_zero_of_le (show i+1≤x by omega),Nat.sub_eq_zero_of_le inside.le]
      push_cast
      apply abs_le.mpr
      constructor <;> nlinarith only [fee,xn,Nat.cast_nonneg (α:=ℤ) (tickAt n (i+1)),mul_nonneg (Nat.cast_nonneg (α:=ℤ) j) xn]
    · rw [show i+1-x=(i-x)+1 by omega]
      push_cast
      apply abs_le.mpr
      constructor <;> nlinarith only [fee,xn,Nat.cast_nonneg (α:=ℤ) (tickAt n (i+1)),mul_nonneg (Nat.cast_nonneg (α:=ℤ) j) xn]
  have quota:=Nat.mul_div_le x 13
  have nb : (n:ℤ)=(x:ℤ)^2 := by dsimp [n,board,x]
  have rootBound : 2*((4*(j:ℤ)+1)*(x:ℤ))≤(x:ℤ)^2 := by
    exact_mod_cast (by nlinarith only [Nat.mul_le_mul_right x cap] : 2*((4*j+1)*x)≤x^2)
  have pocket : 13*((x:ℤ)*(x/13:ℕ))≤(x:ℤ)^2 := by
    exact_mod_cast (by nlinarith only [Nat.mul_le_mul_left x quota] : 13*(x*(x/13))≤x^2)
  change _+2*((x:ℤ)*(x/13:ℕ))<(n:ℤ)
  rw [nb]
  push_cast at diff
  nlinarith only [diff,rootBound,pocket,sq_pos_of_pos (by exact_mod_cast xp : 0<(x:ℤ))]

/-- Checking the observable residue at all physical cuts forces a coherent, zero-centered
lift of the slow phase because the real tick speed cannot cross the excluded gap. -/
theorem lift_board (j : ℕ) (stays : ∀ m≤16^j, inArc j m) :
    ∀ m≤16^j, |pulse j m|≤radius j := by
  have xp : 0<root j := by unfold root;positivity
  have pp : 0<(board j:ℤ) := by exact_mod_cast (Nat.pow_pos xp : 0<board j)
  apply PhaseBound.arc_lift (by unfold radius;positivity) pp (by simp [pulse,tickSum]) (fun _ => speed)
  intro i inside
  exact PhaseBound.modular_witness pp (stays i inside)

theorem rh_of_residues (stays : ∀ j m : ℕ, m≤16^j → inArc j m) : RiemannHypothesis := by
  apply SignedStrip.one_orientation 1 (Or.inl rfl)
  intro j m mh
  have z:=ProductBridge.weighted_sign mh 1 (by
    intro i im
    rw [one_mul,ProductBridge.row_form]
    have hi:= (le_abs_self _).trans (lift_board j (stays j) i (im.trans mh))
    have hh : ((pulse j i:ℤ):ℝ)≤((radius j:ℤ):ℝ) := Int.cast_le.mpr hi
    unfold pulse radius at hh
    push_cast at hh
    exact hh)
  nlinarith only [z,sq_nonneg ((board j):ℝ)]

#print axioms PALRH.SpokeArc.lift_board
#print axioms PALRH.SpokeArc.rh_of_residues
end PALRH.SpokeArc
