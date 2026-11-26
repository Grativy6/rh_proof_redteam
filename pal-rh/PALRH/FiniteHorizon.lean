import PALRH.ProductBridge

open Finset
open scoped BigOperators

noncomputable section
namespace PALRH.FiniteHorizon
open ShapeObservation PrefixReturn ReturnedHorizon

/-- Local version of the returned strip funding step. M may stop inside a board. -/
theorem through_cut {j M : ℕ} (within : M≤16^j) {D : ℝ} (dn : 0≤D)
    (delta : ∀ i : ℕ, root j < i → i ≤ M → |(Chebyshev.theta i-i)-(Chebyshev.theta (root j)-root j)|≤D)
    (price : 13*(3*(M:ℝ)+(root j:ℝ)*D)≤(board j:ℝ)) :
    ∀ m≤M, fits j m := by
  let n:=board j
  let x:=root j
  have xp : 0<x := by dsimp [x,root];positivity
  have np : 0<n := Nat.pow_pos xp
  have nx : n.sqrt=x := Nat.sqrt_eq' _
  have mn : M≤n := by have h:=covers j;change M≤board j;omega
  have bound (i : ℕ) (large : n.sqrt < i) (small : i≤M) :
      |(Chebyshev.theta i-i)-(Chebyshev.theta n.sqrt-n.sqrt)|≤D := by
    rw [nx] at large ⊢;exact delta i large small
  intro m mh
  have pay:=ReturnedReading.paid_readout n M np mn dn bound mh
  rw [nx] at pay
  obtain ⟨a,b⟩:=abs_sub_le_iff.mp pay
  have fee : (n:ℝ)*(3*(M:ℝ)+(x:ℝ)*D)*13≤(n:ℝ)^2 := by
    nlinarith only [mul_le_mul_of_nonneg_left price (Nat.cast_nonneg (α:=ℝ) n)]
  change 13*(prefixJobs n m+smallReturn n m)≤13*(x*plainArea n m)+n^2 ∧
    13*(x*plainArea n m)≤13*(prefixJobs n m+smallReturn n m)+n^2
  constructor
  · exact_mod_cast (show (13:ℝ)*((prefixJobs n m+smallReturn n m:ℕ):ℝ)≤
      13*((x:ℝ)*plainArea n m)+(n:ℝ)^2 by nlinarith only [a,fee])
  · exact_mod_cast (show (13:ℝ)*((x:ℝ)*plainArea n m)≤
      13*((prefixJobs n m+smallReturn n m:ℕ):ℝ)+(n:ℝ)^2 by nlinarith only [b,fee])

/-- The analytic source needed by this finite comparison is stated explicitly.
The accompanying paper derives it from the finite height and the smoothed explicit formula. -/
theorem board_twenty_two
    (delta : ∀ i : ℕ, root 22 < i → i ≤ 2^88 → |(Chebyshev.theta i-i)-(Chebyshev.theta (root 22)-root 22)| ≤ 160*(2:ℝ)^44) :
    ∀ m≤16^22, fits 22 m := by
  apply through_cut (j:=22) (M:=16^22) le_rfl (D:=160*(2:ℝ)^44) (by positivity)
  · intro i lo hi;apply delta i lo;exact hi
  · norm_num [root,board]

theorem half_of_twenty_three
    (delta : ∀ i : ℕ, root 23 < i → i ≤ 2^91 → |(Chebyshev.theta i-i)-(Chebyshev.theta (root 23)-root 23)| ≤ 177*(2:ℝ)^46) :
    ∀ m≤2^91, fits 23 m := by
  apply through_cut (j:=23) (M:=2^91) (by norm_num) (D:=177*(2:ℝ)^46) (by positivity) delta
  norm_num [root,board]

#print axioms PALRH.FiniteHorizon.board_twenty_two
#print axioms PALRH.FiniteHorizon.half_of_twenty_three
end PALRH.FiniteHorizon
