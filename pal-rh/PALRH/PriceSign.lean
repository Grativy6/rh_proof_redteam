import PALRH.ReflectedCells
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Tactic.ComputeDegree

open scoped BigOperators
noncomputable section
namespace PALRH.PriceSign
open ReflectedCells

def difference (X d : ℕ) := residue (2*X) d - residue X d

/-- The sign change for one active quotient occurs at its geometric midpoint. -/
theorem factor (k d r : ℝ) :
    numerator (k*d+r) d r = r*(d-r)*(k*(k+1)*d^2-(k*d+r)^2) := by
  unfold numerator
  ring

private theorem twice_mod {X d : ℕ} (dp : 0<d) :
    (2*X)%d = if 2*(X%d)<d then 2*(X%d) else 2*(X%d)-d := by
  have rem := Nat.mod_lt X dp
  have eq : (2*X)%d=(2*(X%d))%d := by
    simpa only [two_mul] using Nat.add_mod X X d
  rw [eq]
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · rw [Nat.mod_eq_sub_mod (by omega : d≤2*(X%d)),Nat.mod_eq_of_lt (by omega)]

def early (k d r : ℝ) := r*(2*r^3 + k*d*(4*r^2-d^2))
def late (k d v : ℝ) := v*(2*v^3 + (k+1)*d*(d^2-4*v^2))

/-- An integer formula for the sign of the actual two-head measurement. -/
theorem inner {X d : ℕ} (dp : 0<d) (inside : d≤X) :
    4*(X:ℝ)^3*d*difference X d =
      if 2*(X%d)<d then early (X/d:ℕ) d (X%d:ℕ)
      else late (X/d:ℕ) d ((d:ℝ)-(X%d:ℕ)) := by
  have xp : 0<X := by omega
  have dr : (d:ℝ)≠0 := by exact_mod_cast dp.ne'
  have xr : (X:ℝ)≠0 := by exact_mod_cast xp.ne'
  have active : d≤2*X := by omega
  have division := Nat.mod_add_div X d
  have h : (X:ℝ)=((X/d:ℕ):ℝ)*d+((X%d:ℕ):ℝ) := by
    have v : ((X%d:ℕ):ℝ) + (d:ℝ)*(X/d:ℕ) = (X:ℝ) := by exact_mod_cast division
    linarith only [v]
  unfold difference residue
  rw [if_pos active,if_pos inside,twice_mod dp]
  split_ifs with small
  · dsimp [early,numerator]
    push_cast
    field_simp [dr,xr]
    rw [h]
    ring
  · rw [Nat.cast_sub (by omega : d≤2*(X%d))]
    dsimp [late,numerator]
    push_cast
    field_simp [dr,xr]
    rw [h]
    ring

theorem late_positive {k d v : ℝ} (hk : 0≤k) (hd : 0<d) (hv : 0<v) (half : 2*v≤d) :
    0<late k d v := by
  have gap : 0≤d^2-4*v^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr half) (by linarith : 0≤d+2*v)]
  unfold late
  positivity

/-- The root must lie strictly below the half step. -/
theorem early_increasing {k a b : ℝ} (hk : 0<k) (ha : 0≤a) (ab : a<b) :
    2*a^3+k*(4*a^2-1)<2*b^3+k*(4*b^2-1) := by
  have h2 := mul_pos (sub_pos.mpr ab) (by linarith : 0<b+a)
  have h3 := mul_pos (sub_pos.mpr ab)
    (by nlinarith [sq_pos_of_pos (lt_of_le_of_lt ha ab),sq_nonneg a,mul_nonneg ha (lt_of_le_of_lt ha ab).le] : 0<b^2+b*a+a^2)
  nlinarith [mul_pos hk h2]


private theorem gap_of_monic {P : Polynomial ℤ} (hm : P.Monic) {y : ℚ} {n : ℤ}
    (low : (n:ℚ)<y) (high : y<(n:ℚ)+1) : Polynomial.aeval y P ≠ 0 := by
  intro h
  obtain ⟨z,hz,_⟩ := exists_integer_of_is_root_of_monic hm h
  change y=(z:ℚ) at hz
  rw [hz] at low high
  have a : n<z := by exact_mod_cast low
  have b : z<n+1 := by exact_mod_cast high
  omega

theorem no_half_cubic {y : ℚ} (k : ℕ) (yp : 0<y) (yh : y<1) :
    y^3+4*(k:ℚ)*y^2-4*(k:ℚ) ≠ 0 := by
  let P : Polynomial ℤ := .X^3+(.C (4*(k:ℤ))*.X^2-.C (4*(k:ℤ)))
  have hm : P.Monic := by
    dsimp [P]
    apply Polynomial.monic_X_pow_add
    compute_degree!
  have gap := gap_of_monic hm (n:=0) (y:=y) (by simpa using yp) (by simpa using yh)
  intro h
  apply gap
  simpa [P, map_ofNat, sub_eq_add_neg, add_assoc] using h

private theorem early_nonzero {k d r : ℕ} (rp : 0<r) (half : 2*r<d) :
    early k d r ≠ 0 := by
  intro h
  have dr : 0<(d:ℚ) := by exact_mod_cast (show 0<d by omega)
  have rr : (r:ℝ)≠0 := by exact_mod_cast rp.ne'
  have hr : 2*(r:ℝ)^3+(k:ℝ)*d*(4*(r:ℝ)^2-(d:ℝ)^2)=0 :=
    (mul_eq_zero.mp h).resolve_left rr
  have hq : 2*(r:ℚ)^3+(k:ℚ)*d*(4*(r:ℚ)^2-(d:ℚ)^2)=0 := by exact_mod_cast hr
  let y := 2*(r:ℚ)/d
  have hp : 0<y := by dsimp [y]; positivity
  have hh : y<1 := (div_lt_one dr).mpr (by exact_mod_cast half)
  apply no_half_cubic k hp hh
  dsimp [y]
  field_simp [dr.ne']
  linear_combination 4*hq

theorem outer {X d : ℕ} (fromX : X<d) (toX : d≤2*X) :
    16*(d:ℝ)*X^3*difference X d =
      (2*(X:ℝ)-d)*(2*(d:ℝ)-2*X)*(2*(d:ℝ)^2-4*(X:ℝ)^2) := by
  have xp : 0<X := by omega
  have dp : 0<d := by omega
  have dr : (d:ℝ)≠0 := by exact_mod_cast dp.ne'
  have xr : (X:ℝ)≠0 := by exact_mod_cast xp.ne'
  have mod_eq : (2*X)%d=2*X-d := by
    rw [Nat.mod_eq_sub_mod toX,Nat.mod_eq_of_lt (by omega)]
  unfold difference residue
  rw [if_pos toX,if_neg (by omega : ¬ d≤X),sub_zero,mod_eq,Nat.cast_sub toX]
  dsimp [numerator]
  push_cast
  field_simp [dr,xr]
  ring

private theorem outside_square {X d : ℕ} (large : X<d) (stop : d<2*X) :
    2*(d:ℝ)^2-4*(X:ℝ)^2 ≠ 0 := by
  intro hh
  have xp : 0<(X:ℚ) := by exact_mod_cast (show 0<X by omega)
  let y := (d:ℚ)/X
  have low : (1:ℚ)<y := (one_lt_div xp).mpr (by exact_mod_cast large)
  have high : y<(1:ℚ)+1 := (div_lt_iff₀ xp).mpr (by
    norm_num
    exact_mod_cast stop)
  let P : Polynomial ℤ := .X^2-.C 2
  have hm : P.Monic := Polynomial.monic_X_pow_sub_C _ (by decide)
  apply gap_of_monic hm (n:=1) (y:=y) (by simpa using low) (by simpa using high)
  have sq : 2*(d:ℚ)^2-4*(X:ℚ)^2=0 := by exact_mod_cast hh
  simp [P,y,map_ofNat]
  field_simp [xp.ne']
  linarith only [sq]

theorem zero_iff {X d : ℕ} (xp : 0<X) (dp : 0<d) (bound : d≤2*X) :
    difference X d=0 ↔ d∣X ∨ d=2*X := by
  constructor
  · intro zero
    by_cases active : d≤X
    · left
      apply Nat.dvd_of_mod_eq_zero
      by_contra nz
      have rpos : 0<X%d := Nat.pos_of_ne_zero nz
      have eq := inner dp active
      rw [zero,mul_zero] at eq
      split_ifs at eq with small
      · exact early_nonzero rpos small eq.symm
      · have rd := Nat.mod_lt X dp
        have rr : ((X%d:ℕ):ℝ)<(d:ℝ) := by exact_mod_cast rd
        have dpos : 0<(d:ℝ) := by exact_mod_cast dp
        have half : (d:ℝ)≤2*((X%d:ℕ):ℝ) := by exact_mod_cast (le_of_not_gt small)
        exact (late_positive (k:=((X/d:ℕ):ℝ)) (by positivity) dpos (sub_pos.mpr rr)
          (by linarith)).ne' eq.symm
    · right
      by_contra not_end
      have strict := lt_of_le_of_ne bound not_end
      have fromX := lt_of_not_ge active
      have eq := outer fromX bound
      rw [zero,mul_zero] at eq
      have a : (d:ℝ)<2*(X:ℝ) := by exact_mod_cast strict
      have b : (X:ℝ)<(d:ℝ) := by exact_mod_cast fromX
      exact (mul_ne_zero (mul_ne_zero (by linarith) (by linarith)) (outside_square fromX strict)) eq.symm
  · rintro (hd|endpt)
    · have h2 : d∣2*X := dvd_mul_of_dvd_right hd 2
      simp [difference,residue,Nat.mod_eq_zero_of_dvd hd,Nat.mod_eq_zero_of_dvd h2,numerator]
    · subst d
      simp [difference,residue,numerator,if_neg (by omega : ¬2*X≤X)]

#print axioms PALRH.PriceSign.zero_iff
#print axioms PALRH.PriceSign.factor
#print axioms PALRH.PriceSign.inner
#print axioms PALRH.PriceSign.late_positive
end PALRH.PriceSign
