import PALRH.CubicWindow

open Finset Set MeasureTheory Filter
open scoped BigOperators Topology
noncomputable section
namespace PALRH.CubicGaps
open RectangleBalance SquarePass SquarePassBudget TaperedNewton
open SquareSignRows (qReading reading_cast)

def Relative (f : ℝ → ℝ) (C : ℝ) : Prop :=
  ∀ {x y : ℝ}, 0<x → x≤y → |f y-f x|≤C*((y-x)/x)

/-- The full count of admitted coefficients pays for interpolation even when their signs vary. -/
theorem edge_relative : Relative edge 2 := by
  intro x y xp le
  have yp := xp.trans_le le
  let D:=Finset.Icc 1 ⌊2*y⌋₊
  rw [edge_pad_positive (X:=y) yp le_rfl,edge_pad_positive xp le,←Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  have each (n : ℕ) (hn : n∈D) :
      |(marks n:ℝ)/n*taper (n/y)-(marks n:ℝ)/n*taper (n/x)|≤(y-x)/(x*y) := by
    have nr : 0<(n:ℝ) := by exact_mod_cast (show 0<n from (Finset.mem_Icc.mp hn).1)
    have d := FourthAccounts.taper_lip ((n:ℝ)/y) (n/x)
    rw [abs_of_nonpos (sub_nonpos.mpr (div_le_div_of_nonneg_left nr.le xp le))] at d
    rw [←mul_sub,abs_mul,abs_div,abs_of_pos nr]
    have w := div_le_div_of_nonneg_right (FourthAccounts.mark_cap n) nr.le
    apply (mul_le_mul w d (abs_nonneg _) (by positivity)).trans_eq
    field_simp
    ring
  have sum := Finset.sum_le_sum (s:=D) each
  rw [Finset.sum_const,nsmul_eq_mul] at sum
  have count : (D.card:ℝ)≤2*y := by
    simpa [D,Nat.card_Icc] using (Nat.floor_le (by linarith : 0≤2*y))
  exact sum.trans ((mul_le_mul_of_nonneg_right count (div_nonneg (sub_nonneg.mpr le) (mul_pos xp yp).le)).trans_eq
    (by field_simp))

theorem sweep_relative (N : ℕ) {p : ℕ} (pp : 1<p) {f : ℝ → ℝ} {C : ℝ}
    (non : 0≤C) (old : Relative f C) : Relative (sweep N p f) (C/(1-1/(p:ℝ))) := by
  intro x y xp le
  have pr : (1:ℝ)<p := by exact_mod_cast pp
  let r:=1/(p:ℝ)
  let v:=(y-x)/x
  have vn : 0≤v := div_nonneg (sub_nonneg.mpr le) xp.le
  have single (i : ℕ) : |shift (p^i) f y-shift (p^i) f x|≤(C*v)*r^i := by
    let j:=p^i
    have jp : 0<(j:ℝ) := by exact_mod_cast pow_pos (show 0<p by omega) i
    have pos : 0<(j:ℝ)^2 := by positivity
    have op := old (div_pos xp pos) (div_le_div_of_nonneg_right le pos.le)
    have reduce : (y/(j:ℝ)^2-x/(j:ℝ)^2)/(x/(j:ℝ)^2)=v := by dsimp [v];field_simp
    rw [reduce] at op
    change |f (y/(j:ℝ)^2)/j-f (x/(j:ℝ)^2)/j|≤_
    rw [←sub_div,abs_div,abs_of_pos jp]
    have h := div_le_div_of_nonneg_right op jp.le
    exact h.trans_eq (by dsimp [j,r];rw [Nat.cast_pow,one_div,inv_pow,div_eq_mul_inv])
  rw [sweep,sweep,←Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  have total := Finset.sum_le_sum (s:=Finset.range (N+1)) (fun i _ => single i)
  rw [←Finset.mul_sum] at total
  have rp : 0≤r := by dsimp [r];positivity
  have small : r<1 := (div_lt_one (by linarith)).mpr pr
  exact total.trans ((mul_le_mul_of_nonneg_left (finite_geometric rp small N) (mul_nonneg non vn)).trans_eq
    (by dsimp only [v,r];ring))

theorem one_pass_relative (N : ℕ) : Relative (reading N 1) 6 := by
  have a : Relative (sweep N 3 edge) (2/(1-1/(3:ℝ))) := sweep_relative N (by decide : 1<3) (by norm_num : (0:ℝ)≤2) edge_relative
  have b : Relative (reading N 1) ((2/(1-1/(3:ℝ)))/(1-1/(2:ℝ))) := sweep_relative N (by decide : 1<2) (by norm_num : (0:ℝ)≤2/(1-1/(3:ℝ))) a
  norm_num at b
  intro x y hx le
  exact b hx le

/-- Relative distance to a preceding nonnegative rational half-row. The added half-step
covers the real interval that follows the sampled row. -/
def GapBudget : Prop := ∀ e : ℝ, 0<e → e≤1/2 → ∃ A : ℝ, 0≤A ∧
  ∀ N n : ℕ, 0<n → n≤2^(N+1) → ∃ m : ℕ, 0<m ∧ m≤n ∧ 0≤qReading N 1 ((m:ℚ)/2) ∧
    ((n:ℝ)+1-m)/m≤A*(n:ℝ)^(e-1/2)

theorem floor_from_gaps (gaps : GapBudget) {e : ℝ} (ep : 0<e) (small : e≤1/2) :
    ∃ C : ℝ, 0≤C ∧ ∀ N : ℕ, ∀ x ∈ Set.Ioc (0:ℝ) ((2:ℝ)^N), -(C*x^(e-1/2))≤reading N 1 x := by
  obtain ⟨A,an,rows⟩ := gaps e ep small
  refine ⟨6*A,by positivity,?_⟩
  intro N x hx
  by_cases early : x≤1/2
  · rw [(reading_good N 1).2 _ early]
    exact neg_nonpos.mpr (mul_nonneg (by positivity) (Real.rpow_nonneg hx.1.le _))
  let n:=⌊2*x⌋₊
  have lo : (n:ℝ)≤2*x := Nat.floor_le (by linarith [hx.1])
  have hi : 2*x<(n:ℝ)+1 := Nat.lt_floor_add_one _
  have np : 0<n := (Nat.one_le_floor_iff _).mpr (by linarith)
  have nr : (1:ℝ)≤n := by exact_mod_cast np
  have bound : (n:ℝ)≤(2:ℝ)^(N+1) := by rw [pow_succ];linarith [hx.2]
  obtain ⟨m,mp,mn,anchor,dist⟩ := rows N n np (by exact_mod_cast bound)
  have mr : 0<(m:ℝ) := by exact_mod_cast mp
  have mrat : 0<(m:ℚ) := by exact_mod_cast mp
  have mnr : (m:ℝ)≤n := by exact_mod_cast mn
  have inside : (m:ℚ)/2≤(2:ℚ)^N := by
    have w : (m:ℚ)≤(2:ℚ)^(N+1) := by exact_mod_cast mnr.trans bound
    rw [pow_succ] at w
    linarith
  have equal := reading_cast N 1 ((m:ℚ)/2) (by positivity) inside
  push_cast at equal
  have fg : 0≤reading N 1 ((m:ℝ)/2) := by rw [←equal];exact_mod_cast anchor
  have motion := one_pass_relative N (by positivity : 0<(m:ℝ)/2) (by linarith : (m:ℝ)/2≤x)
  have far : (x-(m:ℝ)/2)/(m/2)≤((n:ℝ)+1-m)/m := by
    rw [show (x-(m:ℝ)/2)/(m/2)=(2*x-m)/m by ring]
    exact div_le_div_of_nonneg_right (by linarith) mr.le
  have xn : x≤n := by linarith
  have scale := Real.rpow_le_rpow_of_nonpos hx.1 xn (sub_nonpos.mpr small)
  have allowance := far.trans (dist.trans (mul_le_mul_of_nonneg_left scale an))
  have oppose := neg_le_abs (reading N 1 x-reading N 1 ((m:ℝ)/2))
  linarith [mul_le_mul_of_nonneg_left allowance (by norm_num : (0:ℝ)≤6)]

#print axioms PALRH.CubicGaps.edge_relative
#print axioms PALRH.CubicGaps.one_pass_relative
#print axioms PALRH.CubicGaps.floor_from_gaps

/-- An explicit lower envelope controls the gross area because the signed rectangle weight
is positive and at most one at every sampled dilation. -/
theorem signed_size {f : ℝ → ℝ} (reg : Regular f) (quiet : Before f) {X e C : ℝ}
    (xp : 0<X) (ep : 0<e) (cn : 0≤C)
    (floor : ∀ y ∈ Set.Ioc 0 X, -(C*y^(e-1/2))≤f y) :
    size f X≤5*balanceOf f X+6*C*(X^e/e) := by
  have integr := (intervalIntegral.intervalIntegrable_rpow' (show (-1:ℝ)<e-1 by linarith)
    (a:=0) (b:=X)).1
  have power : (∫ y in Set.Ioc 0 X, y^(e-1))=X^e/e := by
    rw [←intervalIntegral.integral_of_le xp.le,integral_rpow (Or.inl (by linarith : (-1:ℝ)<e-1))]
    rw [show e-1+1=e by ring,Real.zero_rpow ep.ne',sub_zero]
  rw [size,balanceOf,window,window,←power,←integral_const_mul,←integral_const_mul,
    ←integral_add ((balance_int reg quiet X).const_mul (5:ℝ)) (integr.const_mul (6*C))]
  apply setIntegral_mono_on (size_int reg quiet X)
    (((balance_int reg quiet X).const_mul (5:ℝ)).add (integr.const_mul (6*C))) measurableSet_Ioc
  intro y hy
  have inside := (one_le_div hy.1).mpr hy.2
  have low := uniform_floor inside
  have high := ceiling inside
  have extra := mul_nonneg cn (Real.rpow_nonneg hy.1.le (e-1/2))
  have bound : |f y|≤5*f y*gain (X/y)+6*C*y^(e-1/2) := by
    by_cases pos : 0≤f y
    · rw [abs_of_nonneg pos]
      nlinarith [mul_le_mul_of_nonneg_left low pos]
    · rw [abs_of_nonpos (le_of_not_ge pos)]
      have a := mul_le_mul_of_nonpos_left high (le_of_not_ge pos)
      nlinarith [floor y hy]
  have result := div_le_div_of_nonneg_right bound (Real.sqrt_nonneg y)
  have ratio : y^(e-1/2)/Real.sqrt y=y^(e-1) := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_sub hy.1];congr 1;ring
  change |f y| *(1/Real.sqrt y)≤5*(f y*(gain (X/y)/Real.sqrt y))+6*C*y^(e-1)
  rw [←ratio]
  calc
    _ = |f y| / Real.sqrt y := by ring
    _ ≤ (5*f y*gain (X/y)+6*C*y^(e-1/2))/Real.sqrt y := result
    _ = _ := by ring

def FirstPassFloors : Prop := ∀ e : ℝ, 0<e → e≤1/2 → ∃ C : ℝ, 0≤C ∧
  ∀ N : ℕ, ∃ M : ℕ, N≤M ∧ ∀ y ∈ Set.Ioc (0:ℝ) ((2:ℝ)^N), -(C*y^(e-1/2))≤reading M 1 y

theorem rh_of_first_pass_floors (known : FirstPassFloors) : RiemannHypothesis := by
  apply PositiveArea.rh_of_sparse_up
  intro a ap B
  let e:=min (a/2) (1/4)
  have ep : 0<e := lt_min (by linarith) (by norm_num)
  have small : e≤1/2 := (min_le_right _ _).trans (by norm_num)
  have diff : 0<a-e := by linarith [show e≤a/2 from min_le_left _ _]
  obtain ⟨C,cn,lower⟩ := known e ep small
  let K:=4*(5*(16*pairPrice e)*(2:ℝ)^e+6*C/e)
  let t:=(2:ℝ)^(a-e)
  have large : 1<t := Real.one_lt_rpow (by norm_num) diff
  have tends : Tendsto (fun n : ℕ => t^n) atTop atTop := tendsto_pow_atTop_atTop_of_one_lt large
  obtain ⟨M,late⟩ := eventually_atTop.mp (tends.eventually_gt_atTop K)
  let N:=max B M
  let H:=(2:ℝ)^N
  have hp : 0<H := by dsimp [H];positivity
  have cost : K≤H^(a-e) := by
    have eq : H^(a-e)=t^N := by
      dsimp only [H,t]
      rw [←Real.rpow_natCast_mul (by norm_num : (0:ℝ)≤2),←Real.rpow_mul_natCast (by norm_num : (0:ℝ)≤2),mul_comm]
    rw [eq];exact (late _ (le_max_right _ _)).le
  obtain ⟨Khead,nm,here⟩ := lower N
  have gross := signed_size (reading_good Khead 1).1 (reading_good Khead 1).2 hp ep cn here
  have price := balance_bound Khead 1 ep H hp
  rw [pow_one,Real.mul_rpow (by norm_num) hp.le] at price
  have recov := recovered_size Khead 1 hp (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) nm)
  rw [pow_one] at recov
  have up : PositiveArea.up H≤size edge H := by
    apply setIntegral_mono_on (PositiveArea.up_integrable H)
      (size_int edge_continuousOn (fun _ hy => edge_before hy) H) measurableSet_Ioc
    intro y _
    change max (edge y) 0/Real.sqrt y≤|edge y| *(1/Real.sqrt y)
    rw [mul_one_div]
    exact div_le_div_of_nonneg_right (max_le (le_abs_self _) (abs_nonneg _)) (Real.sqrt_nonneg _)
  have bill : PositiveArea.up H≤K*H^e := by
    dsimp only [K]
    nlinarith [show 4*(5*((16*pairPrice e)*((2:ℝ)^e*H^e))+6*C*(H^e/e))=
      4*(5*(16*pairPrice e)*(2:ℝ)^e+6*C/e)*H^e by ring]
  refine ⟨2^N,(le_max_left B M).trans Nat.lt_two_pow_self.le,?_⟩
  push_cast
  change PositiveArea.up H≤H^a
  apply bill.trans
  have result := mul_le_mul_of_nonneg_right cost (Real.rpow_nonneg hp.le e)
  rwa [←Real.rpow_add hp,sub_add_cancel] at result

theorem rh_of_gap_budget (gaps : GapBudget) : RiemannHypothesis := by
  apply rh_of_first_pass_floors
  intro e ep small
  obtain ⟨C,cn,ready⟩ := floor_from_gaps gaps ep small
  exact ⟨C,cn,fun N => ⟨N,le_rfl,ready N⟩⟩

#print axioms PALRH.CubicGaps.signed_size
#print axioms PALRH.CubicGaps.rh_of_gap_budget

/-- A rational sign and one inequality in natural numbers for each requested root-scale gap. -/
def IntegerGaps : Prop := ∀ q : ℕ, 0<q → ∃ A : ℕ, 0<A ∧ ∀ N n : ℕ, 0<n → n≤2^(N+1) →
  ∃ m : ℕ, 0<m ∧ m≤n ∧ 0≤qReading N 1 ((m:ℚ)/2) ∧
    n^q*(n+1-m)^(2*q)≤A*n*m^(2*q)

theorem rh_of_integer_gaps (checks : IntegerGaps) : RiemannHypothesis := by
  apply rh_of_gap_budget
  intro e ep _small
  obtain ⟨r,hr⟩ := exists_nat_one_div_lt ep
  let q:=r+1
  have qp : 0<q := by dsimp [q];omega
  have qr : 0<(q:ℝ) := by exact_mod_cast qp
  have room : 1≤e*(2*q:ℕ) := by
    have less : 1/(q:ℝ)<e := by simpa [q] using hr
    have a := (div_lt_iff₀ qr).mp less
    push_cast
    nlinarith
  obtain ⟨A,ap,rows⟩ := checks q qp
  refine ⟨A,by positivity,?_⟩
  intro N n np inside
  obtain ⟨m,mp,mn,sign,paid⟩ := rows N n np inside
  refine ⟨m,mp,mn,sign,?_⟩
  have mr : 0<(m:ℝ) := by exact_mod_cast mp
  have nr : 0<(n:ℝ) := by exact_mod_cast np
  have unit : (1:ℝ)≤n := by exact_mod_cast np
  have au : (1:ℝ)≤A := by exact_mod_cast ap
  have given : (n:ℝ)^q*((n:ℝ)+1-m)^(2*q)≤(A:ℝ)*n*(m:ℝ)^(2*q) := by
    simpa [Nat.cast_sub (by omega : m≤n+1)] using
      (show ((n^q*(n+1-m)^(2*q):ℕ):ℝ)≤((A*n*m^(2*q):ℕ):ℝ) by exact_mod_cast paid)
  let D:=((n:ℝ)+1-m)/m
  have bill : D^(2*q)*(n:ℝ)^q≤(A:ℝ)*n := by
    apply (le_of_mul_le_mul_right (a:=(m:ℝ)^(2*q)) ?_ (pow_pos mr _))
    dsimp only [D]
    rw [div_pow]
    field_simp at ⊢
    linarith
  have amp : (A:ℝ)≤(A:ℝ)^(2*q) := by simpa using pow_le_pow_right₀ au (show 1≤2*q by omega)
  have power : (n:ℝ)≤(n:ℝ)^(e*(2*q:ℕ)) := by simpa using Real.rpow_le_rpow_of_exponent_le unit room
  have together := bill.trans (mul_le_mul amp power nr.le (by positivity))
  have factor : ((A:ℝ)*(n:ℝ)^(e-1/2))^(2*q)*(n:ℝ)^q=
      (A:ℝ)^(2*q)*(n:ℝ)^(e*(2*q:ℕ)) := by
    rw [mul_pow,mul_assoc,←Real.rpow_natCast ((n:ℝ)^(e-1/2)),←Real.rpow_mul nr.le,
      ←Real.rpow_natCast (n:ℝ) q,←Real.rpow_add nr]
    congr 2
    push_cast
    ring
  rw [←factor] at together
  have compare := le_of_mul_le_mul_right together (pow_pos nr q)
  by_contra! wrong
  exact (not_lt_of_ge compare) (pow_lt_pow_left₀ wrong (by positivity) (show 2*q≠0 by omega))

#print axioms PALRH.CubicGaps.rh_of_integer_gaps

end PALRH.CubicGaps
