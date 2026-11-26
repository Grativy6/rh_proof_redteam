import PALRH.DyadicShape
import PALRH.TickBoard
import Mathlib.Analysis.SpecificLimits.Normed

open Finset Filter
open scoped BigOperators Topology

noncomputable section
namespace PALRH.ShapeStrip

def plainPrefix (v : ℕ → ℝ) (m : ℕ) := ∑ d ∈ Icc 1 m,v d
def weighted (n : ℕ) (v : ℕ → ℝ) (m : ℕ) := ∑ d ∈ Icc 1 m, ((n:ℝ)-d)*v d

/-- Summation by parts recovers the unweighted prefix on the visible end of the row. -/
theorem prefix_identity (n : ℕ) (v : ℕ → ℝ) (m : ℕ) :
    weighted n v m=((n:ℝ)-m)*plainPrefix v m+∑ j ∈ range m,plainPrefix v j := by
  induction m with
  | zero => simp [weighted,plainPrefix]
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have a : weighted n v (m+1)=weighted n v m+((n:ℝ)-(m+1:ℕ))*v (m+1) := by
      unfold weighted;rw [sum_Icc_succ_top (by omega : 1≤m+1)]
    have b : plainPrefix v (m+1)=plainPrefix v m+v (m+1) := by
      unfold plainPrefix;rw [sum_Icc_succ_top (by omega : 1≤m+1)]
    rw [a,b,ih]
    push_cast
    ring

theorem untilted (n M : ℕ) (np : 0<n) (short : 4*M≤n) (v : ℕ → ℝ) {E : ℝ} (en : 0≤E)
    (observed : ∀ m≤M, |weighted n v m|≤E) : ∀ m≤M, |plainPrefix v m|≤2*E/n := by
  have nr : 0<(n:ℝ) := by exact_mod_cast np
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro mh
    have mid : 4*(m:ℝ)≤n := by exact_mod_cast (Nat.mul_le_mul_left 4 mh).trans short
    have early : (m:ℝ)<n := by
      have mn : 0≤(m:ℝ) := Nat.cast_nonneg _
      linarith only [mid,nr,mn]
    have capped : |∑ j ∈ range m,plainPrefix v j|≤(m:ℝ)*(2*E/n) := by
      calc
        _ ≤ ∑ j ∈ range m, |plainPrefix v j| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _ ∈ range m, (2*E/n) := Finset.sum_le_sum (fun j hj => ih j (mem_range.mp hj) ((mem_range.mp hj).le.trans mh))
        _ = _ := by simp
    have error:=observed m mh
    have at_head : ((n:ℝ)-m)*|plainPrefix v m|≤E+m*(2*E/n) := by
      rw [←abs_of_nonneg (sub_nonneg.mpr early.le),←abs_mul,
        show ((n:ℝ)-m)*plainPrefix v m=weighted n v m-(∑ j ∈ range m,plainPrefix v j) by
          rw [prefix_identity];ring]
      exact (abs_sub _ _).trans (add_le_add error capped)
    apply le_of_mul_le_mul_left (a:=((n:ℝ)-m)) _ (by linarith)
    apply at_head.trans
    apply le_of_mul_le_mul_right (a:=(n:ℝ)) _ nr
    have cancel : (2*E/n)*(n:ℝ)=2*E := div_mul_cancel₀ _ nr.ne'
    have a : (E+(m:ℝ)*(2*E/n))*n=E*n+(m:ℝ)*(2*E) := by rw [add_mul,mul_assoc,cancel]
    have b : ((n:ℝ)-m)*(2*E/n)*n=((n:ℝ)-m)*(2*E) := by rw [mul_assoc,cancel]
    rw [a,b]
    nlinarith only [mul_le_mul_of_nonneg_right mid en]

/-- A polynomial in the number of successive zooms is smaller than any positive exponential. -/
theorem root_price (b : ℝ) (bh : 1/2<b) : ∃ D : ℝ, 0≤D ∧
    ∀ j : ℕ, (4:ℝ)^j*((j:ℝ)+1)^2≤D*((16:ℝ)^b)^j := by
  let q:ℝ:=(16:ℝ)^b/4
  have root : (16:ℝ)^(1/2:ℝ)=4 := by rw [←Real.sqrt_eq_rpow];norm_num
  have big : 1<q := by
    dsimp [q]
    have more:=Real.rpow_lt_rpow_of_exponent_lt (by norm_num : 1<(16:ℝ)) bh
    rw [root] at more
    linarith
  have qp:=zero_lt_one.trans big
  have small : Tendsto (fun j : ℕ => (j:ℝ)^2/q^j) atTop (nhds 0) :=
    tendsto_pow_const_div_const_pow_of_one_lt 2 big
  obtain ⟨J,hJ⟩:=eventually_atTop.mp (small.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1)))
  let D:=max (max q 1) (((J:ℝ)+1)^2)
  have dn : 0≤D := by dsimp [D];positivity
  refine ⟨D,dn,?_⟩
  intro j
  have bound : ((j:ℝ)+1)^2≤D*q^j := by
    by_cases early : j+1<J
    · have jJ : (j:ℝ)+1≤(J:ℝ)+1 := by exact_mod_cast (by omega : j+1≤J+1)
      have sq:=pow_le_pow_left₀ (by positivity : 0≤(j:ℝ)+1) jJ 2
      exact sq.trans ((le_max_right _ _).trans (le_mul_of_one_le_right dn (one_le_pow₀ big.le)))
    · have a:=hJ (j+1) (le_of_not_gt early)
      change ((j+1:ℕ):ℝ)^2/q^(j+1)<1 at a
      have h:((j+1:ℕ):ℝ)^2<q^(j+1) := (div_lt_one (pow_pos qp _)).mp a
      push_cast at h
      have qD : q≤D := (le_max_left q 1).trans (le_max_left _ _)
      rw [pow_succ q j,mul_comm (q^j) q] at h
      exact h.le.trans (mul_le_mul_of_nonneg_right qD (pow_nonneg qp.le _))
  calc
    _ ≤ (4:ℝ)^j*(D*q^j) := mul_le_mul_of_nonneg_left bound (by positivity)
    _ = _ := by
      rw [show (4:ℝ)^j*(D*q^j)=D*(4*q)^j by rw [mul_pow];ring]
      dsimp [q];ring_nf

#print axioms PALRH.ShapeStrip.untilted
end PALRH.ShapeStrip
