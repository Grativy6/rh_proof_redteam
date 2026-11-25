import PALRH.SignedAreas

open Set Finset Complex MeasureTheory Filter
open scoped BigOperators Topology
noncomputable section
namespace PALRH.PositiveArea
open RectangleBalance CensusTransfer SignedAreas

def ordinary := observe (fun _ => 1)
def reader (b v : ℝ) := v^b*∑ n ∈ Finset.Icc 1 ⌊v⌋₊, (n:ℝ)^(-b)

private theorem as_complex (b : ℝ) {v : ℝ} (vp : 0≤v) :
    (reader b v:ℂ)=read (fun _ => 1) b v := by
  unfold reader CensusTransfer.read
  rw [Complex.ofReal_mul,Complex.ofReal_cpow vp,Complex.ofReal_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  rw [Complex.ofReal_cpow (by positivity : 0≤(n:ℝ))]
  simp

private theorem real_transfer (b : ℝ) {X : ℝ} (xp : 0<X) :
    X^b*(∫ x in Set.Ioc 0 X, x^(-b)*ordinary x)=
      ∫ y in Set.Ioc 0 X, edge y*reader b (X/y) := by
  have castInt (g : ℝ → ℝ) : Complex.ofReal (∫ x in Set.Ioc 0 X, g x)=(∫ x in Set.Ioc 0 X, (g x:ℂ)) :=
    (integral_ofReal (𝕜:=ℂ) (μ:=volume.restrict (Set.Ioc 0 X)) (f:=g)).symm
  apply Complex.ofReal_injective
  calc
    _ = measured b X ordinary := by
      rw [Complex.ofReal_mul,Complex.ofReal_cpow xp.le,
        castInt (fun x : ℝ => x^(-b)*ordinary x),measured]
      congr 1
      apply setIntegral_congr_fun measurableSet_Ioc
      intro x hx
      change Complex.ofReal (x^(-b)*ordinary x)=(x:ℂ)^(-(b:ℂ))*(ordinary x:ℂ)
      rw [Complex.ofReal_mul,Complex.ofReal_cpow hx.1.le,Complex.ofReal_neg]
    _ = _ := finite_transfer (fun _ => 1) b xp
    _ = _ := by
      rw [castInt (fun y : ℝ => edge y*reader b (X/y))]
      apply setIntegral_congr_fun measurableSet_Ioc
      intro y hy
      change (edge y:ℂ)*read (fun _ => 1) b (X/y)=Complex.ofReal (edge y*reader b (X/y))
      rw [Complex.ofReal_mul,as_complex b (div_nonneg xp.le hy.1.le)]

theorem rising_source {x y : ℝ} (xp : 0<x) (le : x≤y) : ordinary x≤ordinary y := by
  have yp := xp.trans_le le
  have eq (z : ℝ) (zp : 0<z) : ordinary z=source z := by
    unfold ordinary observe
    simpa only [one_div,inv_mul_eq_div] using dilation zp
  rw [eq x xp,eq y yp,source,source]
  have anti : Antitone taper := fun a b h => max_le_max_left _ (min_le_min_left _ (by linarith))
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 ⌊2*x⌋₊, (divisorMass d:ℝ)/d*taper (d/y) := by
      apply Finset.sum_le_sum
      intro d _
      exact mul_le_mul_of_nonneg_left (anti (div_le_div_of_nonneg_left (Nat.cast_nonneg _) xp le))
        (div_nonneg (by exact_mod_cast source_nonnegative d) (by positivity))
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro d hd
        exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1,(Finset.mem_Icc.mp hd).2.trans
          (Nat.floor_le_floor (by linarith))⟩
      · intro d _ _
        exact mul_nonneg (div_nonneg (by exact_mod_cast source_nonnegative d) (by positivity)) (le_max_left _ _)

private theorem response_int (b : ℝ) {X : ℝ} (xp : 0<X) :
    IntegrableOn (fun y : ℝ => edge y*reader b (X/y)) (Set.Ioc 0 X) := by
  have h := (readout_int (s:=(b:ℂ)) (fun _ => 1) xp).re
  apply (integrableOn_congr_fun (f:=fun y : ℝ => edge y*reader b (X/y))
    (g:=fun y : ℝ => ((edge y:ℂ)*read (fun _ => 1) b (X/y)).re) ?_ measurableSet_Ioc).mpr h
  intro y hy
  change edge y*reader b (X/y)=((edge y:ℂ)*read (fun _ => 1) b (X/y)).re
  rw [←as_complex b (div_nonneg xp.le hy.1.le),←Complex.ofReal_mul,Complex.ofReal_re]

private theorem input_int (b X : ℝ) :
    IntegrableOn (fun y : ℝ => y^(-b)*ordinary y) (Set.Ioc 0 X) := by
  let weight := fun y : ℝ => (max y (1/4))^(-b)
  have cw : Continuous weight := by
    unfold weight
    exact (continuous_id.max continuous_const).rpow_const fun y => Or.inl
      (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/4) (le_max_right y _)).ne'
  have integrable : IntegrableOn (fun y : ℝ => weight y*ordinary y) (Set.Ioc 0 X) := ((cw.continuousOn.mul
    ((observed_cont (fun _ => 1) X).mono (fun _ hx => hx.2))).integrableOn_compact
      (isCompact_Icc (a:=0) (b:=X))).mono_set Set.Ioc_subset_Icc_self
  apply (integrableOn_congr_fun (g:=fun y : ℝ => weight y*ordinary y) ?_ measurableSet_Ioc).mpr integrable
  intro y _
  by_cases hi : 1/4≤y
  · simp only [weight,max_eq_left hi]
  have z : ordinary y=0 := observed_early _ (by linarith)
  simp [z]

private theorem reader_zero {v : ℝ} (_vp : 0<v) : reader 0 v=⌊v⌋₊ := by
  simp [reader,Nat.card_Icc]

private theorem reader_half {v : ℝ} (_vp : 0<v) : reader (1/2) v=Real.sqrt v*harmonics ⌊v⌋₊ := by
  unfold reader harmonics
  rw [←Real.sqrt_eq_rpow]
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  rw [Real.rpow_neg (by positivity),←Real.sqrt_eq_rpow,one_div]

private theorem same_weight {X y : ℝ} (xp : 0<X) (yp : 0<y) :
    (reader 0 (X/y)-reader (1/2) (X/y)/2)/Real.sqrt X = gain (X/y)/Real.sqrt y := by
  rw [reader_zero (div_pos xp yp),reader_half (div_pos xp yp),gain,Real.sqrt_div xp.le]
  have hx := (Real.sqrt_pos.mpr xp).ne'
  have hy := (Real.sqrt_pos.mpr yp).ne'
  field_simp

def balance (X : ℝ) := ∫ y in Set.Ioc 0 X, edge y*(gain (X/y)/Real.sqrt y)
def multiplier (X x : ℝ) := 1/Real.sqrt X-1/(2*Real.sqrt x)

theorem balance_as_source {X : ℝ} (xp : 0<X) :
    balance X=∫ x in Set.Ioc 0 X, multiplier X x*ordinary x := by
  have zero := real_transfer 0 xp
  have half := real_transfer (1/2) xp
  have weights (x : ℝ) (hx : x∈Set.Ioc 0 X) : x^(-(1/2:ℝ))=1/Real.sqrt x := by
    rw [Real.rpow_neg hx.1.le,←Real.sqrt_eq_rpow,one_div]
  have zero' : (∫ x in Set.Ioc 0 X, ordinary x)=∫ y in Set.Ioc 0 X, edge y*reader 0 (X/y) := by
    simpa only [neg_zero,Real.rpow_zero,one_mul] using zero
  have half' : (∫ y in Set.Ioc 0 X, edge y*reader (1/2) (X/y))=
       Real.sqrt X*∫ x in Set.Ioc 0 X, x^(-(1/2:ℝ))*ordinary x := by simpa only [←Real.sqrt_eq_rpow] using half.symm
  let Z := fun y : ℝ => edge y*reader 0 (X/y)
  let T := fun y : ℝ => edge y*reader (1/2) (X/y)
  have left (y : ℝ) (hy : y∈Set.Ioc 0 X) :
      edge y*(gain (X/y)/Real.sqrt y)=(1/Real.sqrt X)*(Z y-(1/2)*T y) := by
    rw [←same_weight xp hy.1]
    dsimp only [Z,T];ring
  have right (x : ℝ) (hx : x∈Set.Ioc 0 X) :
      multiplier X x*ordinary x=(1/Real.sqrt X)*ordinary x-(1/2)*(x^(-(1/2:ℝ))*ordinary x) := by
    rw [weights x hx,multiplier];ring
  have diffInt : (∫ x in Set.Ioc 0 X, (1/Real.sqrt X)*ordinary x-(1/2)*(x^(-(1/2:ℝ))*ordinary x))=
      (∫ x in Set.Ioc 0 X, (1/Real.sqrt X)*ordinary x)-(∫ x in Set.Ioc 0 X, (1/2)*(x^(-(1/2:ℝ))*ordinary x)) := by
    have a : IntegrableOn ordinary (Set.Ioc 0 X) := by simpa using input_int 0 X
    exact integral_sub (a.const_mul (1/Real.sqrt X)) ((input_int (1/2) X).const_mul (1/2:ℝ))
  rw [balance,setIntegral_congr_fun measurableSet_Ioc left,integral_const_mul,
    integral_sub (response_int 0 xp) ((response_int (1/2) xp).const_mul _),integral_const_mul,
    setIntegral_congr_fun measurableSet_Ioc right,
    diffInt,
    integral_const_mul,integral_const_mul]
  rw [←zero',half']
  field_simp [(Real.sqrt_pos.mpr xp).ne']

#print axioms PALRH.PositiveArea.balance_as_source

private theorem multiplier_form {x : ℝ} (xp : 0<x) (X : ℝ) :
    multiplier X x = 1/Real.sqrt X-(1/2)*x^(-(1/2:ℝ)) := by
  rw [multiplier,Real.rpow_neg xp.le,←Real.sqrt_eq_rpow];simp only [div_eq_mul_inv,mul_inv_rev];ring

theorem multiplier_int {X : ℝ} (_xp : 0<X) : IntegrableOn (multiplier X) (Set.Ioc 0 X) := by
  apply (integrableOn_congr_fun (fun _ (hx : _∈Set.Ioc 0 X) => multiplier_form hx.1 X) measurableSet_Ioc).mpr
  have power := (intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1:ℝ)< -(1/2:ℝ))
    (a:=0) (b:=X)).1
  exact ((continuousOn_const.integrableOn_Icc (μ:=volume) (a:=0) (b:=X) (f:=fun _ : ℝ => 1/Real.sqrt X)).mono_set
    Set.Ioc_subset_Icc_self).sub (power.const_mul (1/2:ℝ))

theorem multiplier_zero {X : ℝ} (xp : 0<X) : (∫ x in Set.Ioc 0 X, multiplier X x)=0 := by
  have power := (intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1:ℝ)< -(1/2:ℝ))
    (a:=0) (b:=X)).1
  have constant : IntegrableOn (fun _ : ℝ => 1/Real.sqrt X) (Set.Ioc 0 X) :=
    (continuousOn_const.integrableOn_Icc (μ:=volume)).mono_set Set.Ioc_subset_Icc_self
  rw [setIntegral_congr_fun measurableSet_Ioc (fun x (hx : x∈Set.Ioc 0 X) => multiplier_form hx.1 X),
    integral_sub constant (power.const_mul (1/2:ℝ)),integral_const_mul,setIntegral_const,
    Measure.real,Real.volume_Ioc,sub_zero,ENNReal.toReal_ofReal]
  all_goals try linarith
  rw [←intervalIntegral.integral_of_le xp.le,integral_rpow (Or.inl (by norm_num : (-1:ℝ)< -(1/2:ℝ)))]
  norm_num [←Real.sqrt_eq_rpow]
  field_simp [(Real.sqrt_pos.mpr xp).ne']
  nlinarith [Real.sq_sqrt xp.le]

private theorem weighted_source_int {X : ℝ} (_xp : 0<X) :
    IntegrableOn (fun x : ℝ => multiplier X x*ordinary x) (Set.Ioc 0 X) := by
  have clean : IntegrableOn ordinary (Set.Ioc 0 X) := by
    simpa only [neg_zero,Real.rpow_zero,one_mul] using input_int 0 X
  apply (integrableOn_congr_fun (g:=fun x : ℝ => (1/Real.sqrt X)*ordinary x-
    (1/2)*(x^(-(1/2:ℝ))*ordinary x)) ?_ measurableSet_Ioc).mpr
    ((clean.const_mul _).sub ((input_int (1/2) X).const_mul (1/2:ℝ)))
  intro x hx
  change multiplier X x*ordinary x=_
  rw [multiplier_form hx.1 X];ring

theorem balance_nonnegative {X : ℝ} (xp : 0<X) : 0≤balance X := by
  rw [balance_as_source xp]
  let level := ordinary (X/4)
  have compare (x : ℝ) (hx : x∈Set.Ioc 0 X) :
      multiplier X x*level≤multiplier X x*ordinary x := by
    have xs := Real.sq_sqrt xp.le
    have ys := Real.sq_sqrt hx.1.le
    have xr := Real.sqrt_pos.mpr xp
    have yr := Real.sqrt_pos.mpr hx.1
    by_cases small : x≤X/4
    · have root : 2*Real.sqrt x≤Real.sqrt X := le_of_sq_le_sq (by nlinarith) xr.le
      have sign : multiplier X x≤0 := by
        unfold multiplier
        apply sub_nonpos.mpr
        exact one_div_le_one_div_of_le (by positivity) root
      exact mul_le_mul_of_nonpos_left (rising_source hx.1 small) sign
    · have root : Real.sqrt X≤2*Real.sqrt x := le_of_sq_le_sq (by nlinarith) (by positivity)
      have sign : 0≤multiplier X x := by
        unfold multiplier
        exact sub_nonneg.mpr (one_div_le_one_div_of_le xr root)
      exact mul_le_mul_of_nonneg_left (rising_source (by positivity) (le_of_not_ge small)) sign
  have total := setIntegral_mono_on ((multiplier_int xp).mul_const level) (weighted_source_int xp)
    measurableSet_Ioc compare
  simpa only [integral_mul_const,multiplier_zero xp,zero_mul] using total

theorem weighted_int (p : ℝ → ℝ) (cont : Continuous p) (zero : p 0=0) (X : ℝ) :
    IntegrableOn (fun y : ℝ => p (edge y)/Real.sqrt y) (Set.Ioc 0 X) := by
  let den := fun y : ℝ => Real.sqrt (max y (1/4))
  have cd : Continuous den := Real.continuous_sqrt.comp (continuous_id.max continuous_const)
  have dn (y : ℝ) : den y≠0 := (Real.sqrt_pos.mpr (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/4)
      (le_max_right y _))).ne'
  have cf : ContinuousOn (fun y : ℝ => p (edge y)/den y) (Set.Icc 0 X) :=
    (cont.comp_continuousOn ((edge_continuousOn X).mono (fun _ hx => hx.2))).div cd.continuousOn (fun _ _ => dn _)
  apply (integrableOn_congr_fun (g:=fun y : ℝ => p (edge y)/den y) ?_ measurableSet_Ioc).mpr
    (cf.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
  intro y _
  by_cases hi : 1/4≤y
  · simp only [den,max_eq_left hi]
  · simp only [edge_before (show y≤1/2 by linarith),zero,zero_div]

theorem balance_int {X : ℝ} (xp : 0<X) :
    IntegrableOn (fun y : ℝ => edge y*(gain (X/y)/Real.sqrt y)) (Set.Ioc 0 X) := by
  let R := fun b y : ℝ => edge y*reader b (X/y)
  apply (integrableOn_congr_fun (g:=fun y : ℝ => (1/Real.sqrt X)*(R 0 y-(1/2)*R (1/2) y)) ?_ measurableSet_Ioc).mpr
    (((response_int 0 xp).sub ((response_int (1/2) xp).const_mul (1/2:ℝ))).const_mul _)
  intro y hy
  change edge y*(gain (X/y)/Real.sqrt y)=(1/Real.sqrt X)*(R 0 y-(1/2)*R (1/2) y)
  rw [←same_weight xp hy.1];dsimp only [R];ring

def up (X : ℝ) := ∫ y in Set.Ioc 0 X, max (edge y) 0/Real.sqrt y

def signArea (a X : ℝ) := ∫ y in Set.Ioc 0 X, max (a*edge y) 0/Real.sqrt y

theorem gross_le_oriented {X a d : ℝ} (xp : 0<X) (sign : a=1 ∨ a= -1)
    (floor : -d≤a*balance X) : gross X≤Real.sqrt X*(6*signArea a X+5*d) := by
  let P := fun y : ℝ => max (a*edge y) 0/Real.sqrt y
  let A := fun y : ℝ => |edge y|/Real.sqrt y
  let K := fun y : ℝ => a*(edge y*(gain (X/y)/Real.sqrt y))
  have ip : IntegrableOn P (Set.Ioc 0 X) := weighted_int _ ((continuous_const.mul continuous_id).max continuous_const) (by simp) _
  have ia : IntegrableOn A (Set.Ioc 0 X) := weighted_int _ continuous_abs (by simp) _
  have point (y : ℝ) (hy : y∈Set.Ioc 0 X) : A y≤6*P y-5*K y := by
    have large : 1≤X/y := (one_le_div hy.1).mpr hy.2
    have low := uniform_floor large
    have high := ceiling large
    have den := Real.sqrt_pos.mpr hy.1
    have abs_a : |a|=1 := by rcases sign with h|h <;> simp [h]
    have same : |a*edge y|=|edge y| := by rw [abs_mul,abs_a,one_mul]
    dsimp only [A,P,K]
    rw [←same,show 6*(max (a*edge y) 0/Real.sqrt y)-5*(a*(edge y*(gain (X/y)/Real.sqrt y)))=
      (6*max (a*edge y) 0-5*((a*edge y)*gain (X/y)))/Real.sqrt y by ring]
    apply div_le_div_of_nonneg_right _ den.le
    rcases le_total 0 (a*edge y) with pos|neg
    · rw [abs_of_nonneg pos,max_eq_left pos]
      nlinarith [mul_le_mul_of_nonneg_left high pos]
    · rw [abs_of_nonpos neg,max_eq_right neg]
      nlinarith [mul_le_mul_of_nonpos_right low neg]
  have ik : IntegrableOn K (Set.Ioc 0 X) := (balance_int xp).const_mul a
  have sum := setIntegral_mono_on ia ((ip.const_mul (6:ℝ)).sub (ik.const_mul (5:ℝ)))
    measurableSet_Ioc point
  change (∫ y in Set.Ioc 0 X, A y)≤∫ y in Set.Ioc 0 X, 6*P y-5*K y at sum
  rw [integral_sub (ip.const_mul (6:ℝ)) (ik.const_mul (5:ℝ)),integral_const_mul,integral_const_mul] at sum
  have ksum : (∫ y in Set.Ioc 0 X, K y)=a*balance X := integral_const_mul ..
  rw [ksum] at sum
  have absbound : (∫ y in Set.Ioc 0 X, A y)≤6*signArea a X+5*d := by
    change _≤6*signArea a X-5*(a*balance X) at sum
    linarith
  have physical : gross X≤Real.sqrt X*(∫ y in Set.Ioc 0 X, A y) := by
    rw [gross,←integral_const_mul]
    have integ : IntegrableOn (fun y : ℝ => |edge y|) (Set.Ioc 0 X) :=
      (((edge_continuousOn X).abs.mono (fun _ hx => hx.2)).integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
    apply setIntegral_mono_on integ (ia.const_mul (Real.sqrt X)) measurableSet_Ioc
    intro y hy
    have den := Real.sqrt_pos.mpr hy.1
    dsimp only [A]
    rw [←mul_div_assoc]
    apply (le_div_iff₀ den).mpr
    nlinarith [mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hy.2) (abs_nonneg (edge y))]
  exact physical.trans (mul_le_mul_of_nonneg_left absbound (Real.sqrt_nonneg _))


theorem gross_le_positive {X : ℝ} (xp : 0<X) : gross X≤Real.sqrt X*(6*up X) := by
  have floor : -(0:ℝ)≤1*balance X := by simpa using balance_nonnegative xp
  simpa only [signArea,up,one_mul,mul_zero,add_zero] using gross_le_oriented xp (Or.inl rfl) floor

#print axioms PALRH.PositiveArea.balance_nonnegative
#print axioms PALRH.PositiveArea.gross_le_positive


/-- Subpower cumulative positive area at arbitrarily late cuts. -/
def SparseUp : Prop := ∀ e : ℝ, 0<e → ∀ B : ℕ, ∃ H : ℕ, B≤H ∧ up H≤(H:ℝ)^e

theorem rh_of_sparse_up (budget : SparseUp) : RiemannHypothesis := by
  apply rh_of_sparse_gross
  intro a ha B
  let e := (a-1/2)/2
  have ep : 0<e := by dsimp [e];linarith
  obtain ⟨N,large⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop ep).comp tendsto_natCast_atTop_atTop).eventually_gt_atTop (6:ℝ))
  obtain ⟨H,late,hit⟩ := budget e ep (max (max N B) 1)
  have hp : 0<(H:ℝ) := by exact_mod_cast (show 0<H by omega)
  have room : 6≤(H:ℝ)^e := by
    have tail := large H (show N≤H by omega)
    exact (show 6<(H:ℝ)^e by simpa only [Function.comp_apply] using tail).le
  refine ⟨H,by omega,(gross_le_positive hp).trans ?_⟩
  rw [Real.sqrt_eq_rpow,show a=1/2+(e+e) by dsimp [e];ring,Real.rpow_add hp,Real.rpow_add hp]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact mul_le_mul room hit (by
    exact setIntegral_nonneg measurableSet_Ioc (fun _ _ => div_nonneg (le_max_right _ _) (Real.sqrt_nonneg _)))
    (Real.rpow_nonneg hp.le _)

#print axioms PALRH.PositiveArea.rh_of_sparse_up


theorem up_integrable (X : ℝ) :
    IntegrableOn (fun y : ℝ => max (edge y) 0/Real.sqrt y) (Set.Ioc 0 X) :=
  weighted_int _ (continuous_id.max continuous_const) (by simp) _

end PALRH.PositiveArea
