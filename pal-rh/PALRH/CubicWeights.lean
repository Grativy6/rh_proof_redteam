import PALRH.CubicQuadrature
import Mathlib.Analysis.Convex.Deriv

open Finset Set Filter
open scoped Topology BigOperators Classical
noncomputable section
namespace PALRH.CubicWeights
open CubicWindow CubicQuadrature

def join (d : ℝ) (f : ℝ → ℝ) (x : ℝ) := if d≤x then f x else 0

private theorem joined {d x : ℝ} {f g : ℝ → ℝ} (df : HasDerivAt f (g x) x)
    (f0 : f d=0) (g0 : g d=0) : HasDerivAt (join d f) (join d g x) x := by
  rcases lt_trichotomy x d with h|eq|h
  · rw [join,if_neg (not_le.mpr h)]
    apply (hasDerivAt_const x (0:ℝ)).congr_of_eventuallyEq
    filter_upwards [gt_mem_nhds h] with y hy using (if_neg (not_le.mpr hy))
  · subst x
    rw [join,if_pos le_rfl,g0]
    apply hasDerivWithinAt_univ.mp
    rw [←Iic_union_Ici (a:=d)]
    apply HasDerivWithinAt.union
    · apply (hasDerivWithinAt_const d (Set.Iic d) (0:ℝ)).congr
      · intro y hy
        rcases (show y≤d from hy).lt_or_eq with lt|eq
        · exact if_neg (not_le.mpr lt)
        · simp [eq,join,f0]
      · simp [join,f0]
    · rw [←g0]
      exact df.hasDerivWithinAt.congr (fun y (hy : d≤y) => if_pos hy) (if_pos le_rfl)
  · rw [join,if_pos h.le]
    apply df.congr_of_eventuallyEq
    filter_upwards [lt_mem_nhds h] with y hy using (if_pos hy.le)

def piece (d : ℕ) (x : ℝ) := (x-d)^3/x^3
def speed (d : ℕ) (x : ℝ) := 3*d*(x-d)^2/x^4
def accel (d : ℕ) (x : ℝ) := 3*curvature d x/x^5

private theorem piece_deriv (d : ℕ) {x : ℝ} (xp : 0<x) :
    HasDerivAt (join d (piece d)) (join d (speed d) x) x := by
  apply joined
  · have a := (((hasDerivAt_id x).sub_const (d:ℝ)).pow 3).div
      ((hasDerivAt_id x).pow 3) (pow_ne_zero 3 xp.ne')
    apply a.congr_deriv
    dsimp [speed]
    field_simp
    ring
  · simp [piece]
  · simp [speed]

private theorem speed_deriv (d : ℕ) {x : ℝ} (xp : 0<x) :
    HasDerivAt (join d (speed d)) (join d (accel d) x) x := by
  apply joined
  · have a := ((((hasDerivAt_id x).sub_const (d:ℝ)).pow 2).const_mul (3*(d:ℝ))).div
      ((hasDerivAt_id x).pow 4) (pow_ne_zero 4 xp.ne')
    apply a.congr_deriv
    dsimp [accel,curvature]
    field_simp
    ring
  · simp [speed]
  · simp [accel,curvature]

def terms (M T : ℕ) (f : ℕ → ℝ → ℝ) (x : ℝ) :=
  ∑ d ∈ Finset.Icc 1 T, if M<d then join d (f d) x else 0

private theorem terms_deriv (M T : ℕ) {f g : ℕ → ℝ → ℝ} {x : ℝ}
    (h : ∀ d : ℕ, HasDerivAt (join d (f d)) (join d (g d) x) x) :
    HasDerivAt (terms M T f) (terms M T g x) x := by
  apply HasDerivAt.fun_sum
  intro d _
  by_cases keep : M<d
  · simp only [if_pos keep];exact h d
  · simp only [if_neg keep];exact hasDerivAt_const _ _

private theorem nonnegative_accel (M T : ℕ) {x : ℝ} (xp : 0<x) (last : x<(T:ℝ)+1) :
    0≤terms M T accel x := by
  let k:=⌊x⌋₊
  have before : (k:ℝ)≤x := Nat.floor_le xp.le
  have later : x<(k:ℝ)+1 := Nat.lt_floor_add_one x
  have kt : k≤T := Nat.le_of_lt_succ (by exact_mod_cast (show (k:ℝ)<(T:ℝ)+1 by linarith))
  let f:=fun d : ℕ => if M<d then join d (accel d) x else 0
  have short : terms M T accel x=∑ d ∈ Finset.Icc 1 k, f d := by
    symm
    apply Finset.sum_subset (fun d hd => Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hd).1,((Finset.mem_Icc.mp hd).2).trans kt⟩)
    intro d hd outside
    have kd : k<d := by
      by_contra! no;exact outside (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1,no⟩)
    have dx : x<d := later.trans_le (by exact_mod_cast (show k+1≤d by omega))
    simp [f,join,not_le.mpr dx]
  rw [short]
  have each (d : ℕ) (hd : d∈Finset.Icc 1 k) : f d=
      (3/x^5)*(if M<d then curvature d x else 0) := by
    have dx : (d:ℝ)≤x := (by exact_mod_cast (Finset.mem_Icc.mp hd).2 : (d:ℝ)≤k).trans before
    simp only [f,join,if_pos dx,accel]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl each,←Finset.mul_sum]
  exact mul_nonneg (by positivity) (positive_tail M k before later.le)

theorem convex_profile (M T : ℕ) : ConvexOn ℝ (Set.Ioo 0 ((T:ℝ)+1)) (terms M T piece) := by
  let f:=terms M T piece
  let g:=terms M T speed
  have first {x : ℝ} (xp : 0<x) : HasDerivAt f (g x) x := terms_deriv M T (fun d => piece_deriv d xp)
  have second {x : ℝ} (xp : 0<x) : HasDerivAt (deriv f) (terms M T accel x) x := by
    apply (terms_deriv M T (fun d => speed_deriv d xp)).congr_of_eventuallyEq
    filter_upwards [lt_mem_nhds xp] with y hy using (first hy).deriv
  apply convexOn_of_deriv2_nonneg (convex_Ioo _ _)
  · intro x hx;exact (first hx.1).continuousAt.continuousWithinAt
  · rw [isOpen_Ioo.interior_eq]
    intro x hx;exact (first hx.1).differentiableAt.differentiableWithinAt
  · rw [isOpen_Ioo.interior_eq]
    intro x hx;exact (second hx.1).differentiableAt.differentiableWithinAt
  · rw [isOpen_Ioo.interior_eq]
    intro x hx
    change 0≤deriv (deriv f) x
    rw [(second hx.1).deriv]
    exact nonnegative_accel M T hx.1 hx.2

/-- Cubic averaging gives nonnegative weights on every contributing half-row, even
after removing an arbitrary initial segment of ordinary labels. -/
theorem grid_weight_nonnegative (M T : ℕ) {n : ℕ} (two : 2≤n) (past : n≤T) :
    0≤cost (fun j : ℕ => terms M T piece ((T:ℝ)/j)) n := by
  let f:=terms M T piece
  let z:=fun j : ℕ => (T:ℝ)/j
  have tp : 0<(T:ℝ) := by exact_mod_cast (show 0<T by omega)
  have good {j : ℕ} (jp : 0<j) : z j∈Set.Ioo (0:ℝ) ((T:ℝ)+1) := by
    have jr : 0<(j:ℝ) := by exact_mod_cast jp
    have one : (1:ℝ)≤j := by exact_mod_cast jp
    exact ⟨div_pos tp jr,lt_of_le_of_lt (div_le_self tp.le one) (lt_add_one _)⟩
  have step {j : ℕ} (jp : 0<j) : z (j+1)<z j := by
    have jr : 0<(j:ℝ) := by exact_mod_cast jp
    exact div_lt_div_of_pos_left tp jr (by exact_mod_cast j.lt_succ_self)
  have ns : n-1+1=n := by omega
  have a := step (show 0<n-1 by omega)
  rw [ns] at a
  have mono := (convex_profile M T).slope_mono_adjacent (good (by omega : 0<n+1)) (good (by omega : 0<n-1))
    (step (by omega : 0<n)) a
  have scale (j : ℕ) (jp : 0<j) :
      slope (fun i : ℕ => f (z i)) j=(T/2:ℝ)*((f (z j)-f (z (j+1)))/(z j-z (j+1))) := by
    have jr : 0<(j:ℝ) := by exact_mod_cast jp
    have nz : z j-z (j+1)≠0 := (sub_pos.mpr (step jp)).ne'
    rw [←mul_div_assoc]
    apply (eq_div_iff nz).mpr
    dsimp [CubicQuadrature.slope,z]
    push_cast
    field_simp
    ring
  change 0≤slope (fun i : ℕ => f (z i)) (n-1)-slope (fun i : ℕ => f (z i)) n
  rw [scale (n-1) (by omega),scale n (by omega),ns]
  exact sub_nonneg.mpr (mul_le_mul_of_nonneg_left mono (by positivity))

#print axioms PALRH.CubicWeights.convex_profile
#print axioms PALRH.CubicWeights.grid_weight_nonnegative

def cubic (T n : ℕ) : ℝ := (max 0 (1-(n:ℝ)/T))^3

private theorem at_division {T j : ℕ} (tp : 0<T) (jp : 0<j) (d : ℕ) :
    join d (piece d) ((T:ℝ)/j)=cubic T (d*j) := by
  have tr : 0<(T:ℝ) := by exact_mod_cast tp
  have jr : 0<(j:ℝ) := by exact_mod_cast jp
  by_cases active : (d:ℝ)≤(T:ℝ)/j
  · have small := (le_div_iff₀ jr).mp active
    have pos : 0≤1-(d:ℝ)*j/T := sub_nonneg.mpr ((div_le_one tr).mpr small)
    rw [join,if_pos active,cubic,Nat.cast_mul,max_eq_right pos,piece]
    field_simp
  · have big := (div_lt_iff₀ jr).mp (lt_of_not_ge active)
    rw [join,if_neg active,cubic,Nat.cast_mul,max_eq_left (sub_nonpos.mpr ((one_le_div tr).mpr big.le))]
    norm_num

def samples (M T : ℕ) (j : ℕ) := ∑ d ∈ Finset.Icc 1 T, if M<d then cubic T (d*j) else 0

theorem sampled_profile {M T j : ℕ} (tp : 0<T) (jp : 0<j) :
    terms M T piece ((T:ℝ)/j)=samples M T j := by
  unfold terms samples
  apply Finset.sum_congr rfl
  intro d _
  rw [at_division tp jp]

theorem sampled_weight (M T : ℕ) {n : ℕ} (two : 2≤n) (past : n≤T) :
    0≤cost (samples M T) n := by
  have tp : 0<T := by omega
  have same (j : ℕ) (jp : 0<j) :
      CubicQuadrature.slope (fun i : ℕ => terms M T piece ((T:ℝ)/i)) j=
      CubicQuadrature.slope (samples M T) j := by
    rw [CubicQuadrature.slope,CubicQuadrature.slope,sampled_profile tp jp,sampled_profile tp (by omega : 0<j+1)]
  have h := grid_weight_nonnegative M T two past
  unfold cost at h ⊢
  rwa [same (n-1) (by omega),same n (by omega)] at h

theorem full_samples (T j : ℕ) : samples 0 T j=profile T (cubic T) j := by
  apply Finset.sum_congr rfl
  intro d hd
  simp [(show 0<d from (Finset.mem_Icc.mp hd).1)]

theorem cut_samples {T : ℕ} (tp : 0<T) (j : ℕ) :
    samples 1 T j=profile T (cubic T) j-cubic T j := by
  unfold samples profile
  let I:=Finset.Icc 1 T
  have member : 1∈I := Finset.mem_Icc.mpr ⟨le_rfl,tp⟩
  rw [←Finset.add_sum_erase I (fun d : ℕ => if 1<d then cubic T (d*j) else 0) member,
    ←Finset.add_sum_erase I (fun d : ℕ => cubic T (d*j)) member]
  simp only [lt_irrefl,if_false,zero_add,one_mul,add_sub_cancel_left]
  apply Finset.sum_congr rfl
  intro d hd
  obtain ⟨ne,h⟩ := Finset.mem_erase.mp hd
  have pos := (Finset.mem_Icc.mp h).1
  simp [show 1<d by omega]

theorem cubic_stop {T : ℕ} (tp : 0<T) (j : ℕ) (outside : T≤j) : cubic T j=0 := by
  have tr : 0<(T:ℝ) := by exact_mod_cast tp
  rw [cubic,max_eq_left (sub_nonpos.mpr ((one_le_div tr).mpr (by exact_mod_cast outside)))]
  norm_num

theorem full_positive_read {T : ℕ} (tp : 0<T) :
    (∑ n ∈ Finset.Icc 1 T, cost (samples 0 T) n*RectangleBalance.edge ((n:ℝ)/2))=
      ∑ n ∈ Finset.Icc 1 T, if ∃ b : ℕ, n=3^b then cubic T n else 0 := by
  rw [show samples 0 T=profile T (cubic T) from funext (full_samples T)]
  exact full_grid (cubic_stop tp)

theorem cut_positive_read {T : ℕ} (tp : 0<T) :
    (∑ n ∈ Finset.Icc 1 T, cost (samples 1 T) n*RectangleBalance.edge ((n:ℝ)/2))=
      (∑ n ∈ Finset.Icc 1 T, if ∃ b : ℕ, n=3^b then cubic T n else 0)-
        ∑ d ∈ Finset.Icc 1 T, (TaperedNewton.marks d:ℝ)*(cubic T d-cubic T (2*d)) := by
  rw [show samples 1 T=(fun j => profile T (cubic T) j-cubic T j) from funext (cut_samples tp)]
  exact omitted_grid (cubic_stop tp)

#print axioms PALRH.CubicWeights.sampled_weight
#print axioms PALRH.CubicWeights.full_positive_read
#print axioms PALRH.CubicWeights.cut_positive_read

end PALRH.CubicWeights
