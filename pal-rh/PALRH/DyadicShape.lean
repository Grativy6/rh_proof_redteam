import PALRH.UncalibratedPrime
import Mathlib.Analysis.SpecificLimits.Normed

open Finset Filter
open scoped BigOperators Topology

noncomputable section
namespace PALRH.DyadicShape

/-- The reference value inferred from successive measured slopes. -/
def limitingSlope (slope : ℕ → ℝ) :=
  slope 0 + ∑' j : ℕ,(slope (j+1)-slope j)

private theorem tail {slope : ℕ → ℝ} {K r : ℝ} (rn : 0≤r) (rr : r<1)
    (steps : ∀ j : ℕ, |slope (j+1)-slope j|≤K*r^j) (j : ℕ) :
    |limitingSlope slope-slope j|≤K*r^j/(1-r) := by
  let d:=fun i : ℕ => slope (i+1)-slope i
  have major:= (summable_geometric_of_lt_one rn rr).mul_left K
  have sum : Summable d := major.of_norm_bounded (fun i => by simpa [d,Real.norm_eq_abs] using steps i)
  have eq:=sum.sum_add_tsum_nat_add j
  change (∑ i ∈ range j,(slope (i+1)-slope i)) + (∑' k : ℕ,d (k+j))=∑' k : ℕ,d k at eq
  rw [Finset.sum_range_sub] at eq
  have split : limitingSlope slope-slope j=∑' k : ℕ,d (k+j) := by
    change slope 0+(∑' k : ℕ,d k)-slope j=_
    linarith only [eq]
  have bound (i : ℕ) : ‖d (i+j)‖≤(K*r^j)*r^i := by
    rw [Real.norm_eq_abs]
    calc
      _ ≤ _ := steps (i+j)
      _ = _ := by rw [pow_add];ring
  have price:= (summable_geometric_of_lt_one rn rr).mul_left (K*r^j)
  have absSum : Summable (fun i : ℕ => ‖d (i+j)‖) :=
    price.of_norm_bounded (fun i => by simpa using bound i)
  rw [split,←Real.norm_eq_abs]
  calc
    _ ≤ _ := norm_tsum_le_tsum_norm absSum
    _ ≤ _ := absSum.tsum_le_tsum bound price
    _ = _ := by rw [tsum_mul_left,tsum_geometric_of_lt_one rn rr,div_eq_mul_inv]

private theorem exponent_at (b : ℝ) (j : ℕ) :
    ((16:ℝ)^b)^j=((16:ℝ)^j)^b := by
  rw [←Real.rpow_natCast ((16:ℝ)^b) j,←Real.rpow_mul (by norm_num),
    ←Real.rpow_natCast (16:ℝ) j,←Real.rpow_mul (by norm_num),mul_comm b]

/-- Overlapping views at geometric heads pay the discrepancy with one inferred slope.
No calibration constant is assumed. -/
theorem recenter (f : ℕ → ℝ) (slope : ℕ → ℝ) {b C : ℝ} (bp : 0<b) (bl : b<1) (cn : 0≤C)
    (samples : ∀ j m : ℕ, 0<m → m≤16^j → |f m-slope j*m|≤C*((16:ℝ)^b)^j) :
    ∃ D : ℝ, 0≤D ∧ ∀ m : ℕ, 0<m → |f m-limitingSlope slope*m|≤D*(m:ℝ)^b := by
  let q:ℝ:=(16:ℝ)^b
  let r:=q/16
  let K:=C*(1+q)
  have qp : 0<q := Real.rpow_pos_of_pos (by norm_num) _
  have rp : 0<r := by dsimp [r];positivity
  have rl : r<1 := by
    dsimp [r,q]
    have h:=Real.rpow_lt_rpow_of_exponent_lt (by norm_num : 1<(16:ℝ)) bl
    rw [Real.rpow_one] at h
    linarith
  have Kn : 0≤K := by dsimp [K];positivity
  have increments (j : ℕ) : |slope (j+1)-slope j|≤K*r^j := by
    have positive : 0<(16:ℕ)^j := by positivity
    have adjacent : (16:ℕ)^j≤16^(j+1) := by rw [pow_succ];omega
    have small:=samples j (16^j) positive le_rfl
    have big:=samples (j+1) (16^j) positive adjacent
    push_cast at small big
    have joined : |(slope (j+1)-slope j)*(16:ℝ)^j|≤C*q^j+C*q^(j+1) := by
      calc
        _ = |(f (16^j)-slope j*(16:ℝ)^j)-(f (16^j)-slope (j+1)*(16:ℝ)^j)| := by ring_nf
        _ ≤ _ := abs_sub _ _
        _ ≤ _ := add_le_add small big
    rw [abs_mul,abs_of_pos (by positivity : 0<(16:ℝ)^j)] at joined
    apply le_of_mul_le_mul_right (a:=((16:ℝ)^j)) _ (by positivity)
    dsimp [K,r]
    rw [div_pow]
    have eq : C*(1+q)*(q^j/(16:ℝ)^j)*(16:ℝ)^j=C*q^j+C*q^(j+1) := by
      rw [pow_succ];field_simp
    rwa [eq]
  let F:=C+K/(1-r)
  have Fn : 0≤F := by dsimp [F];positivity
  refine ⟨F*q, mul_nonneg Fn qp.le,?_⟩
  intro m mp
  let j:=Nat.log 16 m+1
  have cover : m≤16^j := (Nat.lt_pow_succ_log_self (by decide) m).le
  have immediately : 16^j≤16*m := by
    dsimp [j];rw [pow_succ,mul_comm]
    exact Nat.mul_le_mul_left 16 (Nat.pow_log_le_self 16 mp.ne')
  have bound:=samples j m mp cover
  have corr:=tail rp.le rl increments j
  have floor : (m:ℝ)≤(16:ℝ)^j := by exact_mod_cast cover
  have coarse : K*r^j/(1-r)*(16:ℝ)^j=(K/(1-r))*q^j := by
    dsimp [r];rw [div_pow];field_simp
  have resolution : q^j≤q*(m:ℝ)^b := by
    rw [show q^j=((16:ℝ)^j)^b from exponent_at b j,←Real.mul_rpow (by norm_num : 0≤(16:ℝ)) (Nat.cast_nonneg m)]
    exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast immediately) bp.le
  calc
    _ = |(f m-slope j*m)+(slope j-limitingSlope slope)*m| := by ring_nf
    _ ≤ _ := abs_add_le _ _
    _ ≤ C*q^j+(K/(1-r))*q^j := by
      apply add_le_add bound
      rw [abs_mul,show |(m:ℝ)|=(m:ℝ) from abs_of_nonneg (Nat.cast_nonneg m),abs_sub_comm,←coarse]
      exact mul_le_mul corr floor (Nat.cast_nonneg _) (le_trans (abs_nonneg _) corr)
    _ = F*q^j := by dsimp [F];ring
    _ ≤ (F*q)*(m:ℝ)^b := by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left resolution Fn

theorem infer_density_and_rh (slope : ℕ → ℝ)
    (data : ∀ b : ℝ, 1/2<b → b<1 → ∃ C : ℝ, 0≤C ∧
      ∀ j m : ℕ, 0<m → m≤16^j → |Chebyshev.theta m-slope j*m|≤C*((16:ℝ)^b)^j) :
    limitingSlope slope=1 ∧ RiemannHypothesis := by
  apply UncalibratedPrime.from_unknown_theta
  intro b bh
  obtain ⟨a,apos,ahead⟩:=exists_between (lt_min bh (by norm_num : (1/2:ℝ)<1))
  obtain ⟨C,cn,localData⟩:=data a apos (ahead.trans_le (min_le_right _ _))
  obtain ⟨D,dn,glob⟩:=recenter (fun m : ℕ => Chebyshev.theta m) slope
    (by linarith only [apos]) (ahead.trans_le (min_le_right _ _)) cn localData
  let c:=limitingSlope slope
  refine ⟨D+|c|,by positivity,?_⟩
  intro y large
  let m:=⌊y⌋₊
  have mp : 0<m := Nat.floor_pos.mpr large
  have my : (m:ℝ)≤y := Nat.floor_le (zero_le_one.trans large)
  have far : y<(m:ℝ)+1 := Nat.lt_floor_add_one _
  have ey : Chebyshev.theta y=Chebyshev.theta m := Chebyshev.theta_eq_theta_coe_floor y
  have higher : (m:ℝ)^a≤y^b := (Real.rpow_le_rpow (Nat.cast_nonneg _) my (by linarith only [apos])).trans
    (Real.rpow_le_rpow_of_exponent_le large ((ahead.trans_le (min_le_left _ _)).le))
  have one : (1:ℝ)≤y^b := Real.one_le_rpow large (by linarith only [bh])
  change |Chebyshev.theta y-c*y|≤(D+|c|)*y^b
  rw [ey]
  calc
    _ = |(Chebyshev.theta m-c*m)+c*((m:ℝ)-y)| := by ring_nf
    _ ≤ _ := abs_add_le _ _
    _ ≤ D*y^b+|c| * y^b := by
      apply add_le_add ((glob m mp).trans (mul_le_mul_of_nonneg_left higher dn))
      rw [abs_mul,abs_of_nonpos (sub_nonpos.mpr my)]
      exact mul_le_mul_of_nonneg_left (by linarith only [one,far]) (abs_nonneg _)
    _ = _ := by ring

#print axioms PALRH.DyadicShape.recenter
#print axioms PALRH.DyadicShape.infer_density_and_rh
end PALRH.DyadicShape
