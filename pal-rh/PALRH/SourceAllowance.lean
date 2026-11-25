import PALRH.PositiveArea

open Finset Set MeasureTheory Filter
open scoped BigOperators
noncomputable section
namespace PALRH.SourceAllowance
open RectangleBalance PositiveArea SignedAreas

private theorem geometric (n : ℕ) : (∑ i ∈ Finset.range n, (3/4:ℝ)^i)≤4 := by
  have eq (n : ℕ) : (∑ i ∈ Finset.range n, (3/4:ℝ)^i)+4*(3/4:ℝ)^n=4 := by
    induction n with
    | zero => norm_num
    | succ n old => rw [Finset.sum_range_succ,pow_succ];linarith
  linarith [eq n,show 0≤(3/4:ℝ)^n by positivity]

private lemma sqrt_power {x : ℝ} (hp : 0≤x) (n : ℕ) :
    Real.sqrt (x^n)=(Real.sqrt x)^n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ,Real.sqrt_mul (pow_nonneg hp n),ih,pow_succ]

private theorem power_price (a b : ℕ) :
    1/Real.sqrt (((2^a*3^b:ℕ):ℝ))≤(3/4:ℝ)^a*(3/4:ℝ)^b := by
  have low : 4/3≤Real.sqrt 2 := le_of_sq_le_sq (by rw [Real.sq_sqrt (by norm_num : (0:ℝ)≤2)];norm_num)
    (Real.sqrt_nonneg _)
  have lower := low.trans (Real.sqrt_le_sqrt (by norm_num : (2:ℝ)≤3))
  have a2 : 1/Real.sqrt 2≤3/4 := (div_le_iff₀ (by positivity)).mpr (by linarith)
  have a3 : 1/Real.sqrt 3≤3/4 := (div_le_iff₀ (by positivity)).mpr (by linarith)
  push_cast
  rw [Real.sqrt_mul (by positivity),sqrt_power (by norm_num),sqrt_power (by norm_num)]
  simp only [one_div,mul_inv_rev,←inv_pow]
  have c2 := pow_le_pow_left₀ (by positivity) a2 a
  have c3 := pow_le_pow_left₀ (by positivity) a3 b
  simpa only [one_div,mul_comm] using mul_le_mul c2 c3 (by positivity) (by positivity)

theorem smooth_budget (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (divisorMass n:ℝ)/Real.sqrt n)≤16 := by
  let I := Finset.Icc 1 N
  let R := Finset.range (N+1)
  let index := fun ab : ℕ×ℕ => 2^ab.1*3^ab.2
  let price := fun ab : ℕ×ℕ => (3/4:ℝ)^ab.1*(3/4:ℝ)^ab.2
  let pairs := (R ×ˢ R).filter (fun t => index t≤N)
  have pos (t : ℕ×ℕ) : 0≤price t := by dsimp [price];positivity
  have reach (t : ℕ×ℕ) (ht : t∈pairs) : index t∈I := Finset.mem_Icc.mpr
    ⟨show 0 < index t by dsimp [index];positivity,(Finset.mem_filter.mp ht).2⟩
  have point (n : ℕ) (hn : n∈I) : (divisorMass n:ℝ)/Real.sqrt n≤
      ∑ t ∈ pairs with index t=n, price t := by
    by_cases zero : divisorMass n=0
    · simpa only [zero,Rat.cast_zero,zero_div] using (Finset.sum_nonneg (fun t _ => pos t) :
        0≤∑ t ∈ pairs with index t=n, price t)
    obtain ⟨a,b,prod⟩ := support_exact (Finset.mem_Icc.mp hn).1 zero
    have na : a≤N := calc
      a ≤ 2^a := Nat.lt_two_pow_self.le
      _ ≤ n := Nat.le_of_dvd (Finset.mem_Icc.mp hn).1 ⟨3^b,prod⟩
      _ ≤ N := (Finset.mem_Icc.mp hn).2
    have nb : b≤N := calc
      b ≤ 2^b := Nat.lt_two_pow_self.le
      _ ≤ 3^b := Nat.pow_le_pow_left (by decide) b
      _ ≤ n := Nat.le_of_dvd (Finset.mem_Icc.mp hn).1 ⟨2^a,by simpa [Nat.mul_comm] using prod⟩
      _ ≤ N := (Finset.mem_Icc.mp hn).2
    have mem : (a,b)∈pairs.filter (fun t => index t=n) := Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),Finset.mem_range.mpr (by omega)⟩,
        (show index (a,b)≤N by simpa only [index,←prod] using (Finset.mem_Icc.mp hn).2)⟩,prod.symm⟩
    apply le_trans _ (Finset.single_le_sum (fun t _ => pos t) mem)
    rw [prod,smooth_source,Rat.cast_one]
    exact power_price a b
  have total := Finset.sum_le_sum point
  rw [Finset.sum_fiberwise_of_maps_to reach price] at total
  apply total.trans
  apply (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun t _ _ => pos t)).trans
  rw [Finset.sum_product]
  dsimp only [price]
  simp_rw [←Finset.mul_sum]
  rw [←Finset.sum_mul]
  have cap := geometric (N+1)
  exact (mul_le_mul cap cap (Finset.sum_nonneg (fun _ _ => by positivity)) (by norm_num)).trans_eq (by norm_num)

private theorem atom_int {X : ℝ} (xp : 0<X) (n : ℕ) :
    IntegrableOn (fun x : ℝ => multiplier X x*atom n x) (Set.Ioc 0 X) := by
  apply (multiplier_int xp).mul_bdd (atom_continuous n).aestronglyMeasurable (c:=1)
  exact Filter.Eventually.of_forall (fun x => by rw [Real.norm_eq_abs,abs_of_nonneg (atom_unit n x).1]; exact (atom_unit n x).2)

private theorem atom_charge {X : ℝ} (xp : 0<X) {n : ℕ} (np : 0<n) :
    (∫ x in Set.Ioc 0 X, multiplier X x*atom n x)≤Real.sqrt n := by
  let Y := min X (n:ℝ)
  let part := fun x : ℝ => multiplier X x*atom n x-multiplier X x
  have ylo : 0<Y := lt_min xp (by positivity)
  have sub : Set.Ioc 0 Y⊆Set.Ioc 0 X := fun _ hx => ⟨hx.1,hx.2.trans (min_le_left ..)⟩
  have eq : (∫ x in Set.Ioc 0 X, multiplier X x*atom n x)=∫ x in Set.Ioc 0 Y, part x := by
    calc
      _ = ∫ x in Set.Ioc 0 X, part x := by
        dsimp [part]
        rw [integral_sub (atom_int xp n) (multiplier_int xp),multiplier_zero xp,sub_zero]
      _ = _ := by
        apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioc sub
        rintro x ⟨hx,out⟩
        have far : (n:ℝ)≤x := by
          by_contra! bad
          exact out ⟨hx.1,le_min hx.2 bad.le⟩
        simp [part,atom_one np far]
  rw [eq]
  let target := fun x : ℝ => (1/2)*x^(-(1/2:ℝ))
  have itr : IntegrableOn target (Set.Ioc 0 Y) :=
    ((intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1:ℝ)< -(1/2:ℝ)) (a:=0) (b:=Y)).1).const_mul _
  have bound (x : ℝ) (hx : x∈Set.Ioc 0 Y) : part x≤target x := by
    dsimp only [target,part,multiplier]
    rw [Real.rpow_neg hx.1.le,←Real.sqrt_eq_rpow]
    obtain ⟨hl,hu⟩ := atom_unit n x
    have plain := mul_nonpos_of_nonneg_of_nonpos (show 0≤1/Real.sqrt X by positivity) (sub_nonpos.mpr hu)
    have other := mul_nonneg (show 0≤1/(2*Real.sqrt x) by positivity) hl
    have frac : 1/(2*Real.sqrt x)=(1/2)*(Real.sqrt x)⁻¹ := by simp [div_eq_mul_inv,mul_comm]
    rw [frac] at other ⊢
    nlinarith
  have step := setIntegral_mono_on (((atom_int xp n).sub (multiplier_int xp)).mono_set sub) itr measurableSet_Ioc bound
  apply step.trans
  dsimp only [target]
  rw [integral_const_mul,←intervalIntegral.integral_of_le ylo.le,
    integral_rpow (Or.inl (by norm_num : (-1:ℝ)< -(1/2:ℝ)))]
  norm_num [←Real.sqrt_eq_rpow]
  calc
    _ = Real.sqrt Y := by ring
    _ ≤ _ := Real.sqrt_le_sqrt (min_le_right ..)

theorem balance_ceiling {X : ℝ} (xp : 0<X) : balance X≤16 := by
  let I := Finset.Icc 1 ⌊2*X⌋₊
  let coeff := fun n : ℕ => (divisorMass n:ℝ)/n
  have non (n : ℕ) : 0≤coeff n := div_nonneg (by exact_mod_cast source_nonnegative n) (by positivity)
  have value (x : ℝ) (hx : x∈Set.Ioc 0 X) : multiplier X x*ordinary x=
      ∑ n ∈ I, coeff n*(multiplier X x*atom n x) := by
    have ord : ordinary x=source x := by unfold ordinary observe;simpa only [one_div,inv_mul_eq_div] using dilation hx.1
    rw [ord,source_pad_positive hx.1 hx.2,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    dsimp only [coeff];ring
  rw [balance_as_source xp,setIntegral_congr_fun measurableSet_Ioc value,
    integral_finsetSum _ (fun n _ => (atom_int xp n).const_mul _)]
  apply le_trans _ (smooth_budget ⌊2*X⌋₊)
  apply Finset.sum_le_sum
  intro n hn
  have np := (Finset.mem_Icc.mp hn).1
  rw [integral_const_mul]
  apply (mul_le_mul_of_nonneg_left (atom_charge xp np) (non n)).trans_eq
  dsimp only [coeff]
  have nr : 0<(n:ℝ) := by exact_mod_cast (show 0<n from np)
  field_simp [(Real.sqrt_pos.mpr nr).ne']
  rw [Real.sq_sqrt nr.le]

#print axioms PALRH.SourceAllowance.smooth_budget
#print axioms PALRH.SourceAllowance.balance_ceiling

/-- Sign convention shared between a sampled rational frame and its real interpolation. -/
def direction (rising : Bool) : ℚ := if rising then 1 else -1
def amount (rising : Bool) (X : ℝ) := signArea (direction rising:ℝ) X

theorem direction_abs (o : Bool) : |direction o|=1 := by cases o <;> norm_num [direction]

theorem amount_int (o : Bool) (X : ℝ) :
    IntegrableOn (fun y : ℝ => max ((direction o:ℝ)*edge y) 0/Real.sqrt y) (Set.Ioc 0 X) :=
  weighted_int _ ((continuous_const.mul continuous_id).max continuous_const) (by simp) _

theorem gross_from_either (o : Bool) {X : ℝ} (xp : 0<X) :
    gross X≤Real.sqrt X*(6*amount o X+80) := by
  have dir : (direction o:ℝ)=1 ∨ (direction o:ℝ)= -1 := by cases o <;> norm_num [direction]
  have ground : -(16:ℝ)≤(direction o:ℝ)*balance X := by
    rcases dir with h|h <;> rw [h] <;> linarith [balance_nonnegative xp,balance_ceiling xp]
  simpa only [amount,show (5:ℝ)*16=80 by norm_num] using gross_le_oriented xp dir ground

/-- The cheaper orientation can change at every checkpoint. -/
def SparseChoice : Prop := ∀ e : ℝ, 0<e → ∀ B : ℕ, ∃ H : ℕ, B≤H ∧
  ∃ rising : Bool, amount rising H≤(H:ℝ)^e

theorem rh_of_sparse_choice (budget : SparseChoice) : RiemannHypothesis := by
  apply rh_of_sparse_gross
  intro a ha B
  let e := (a-1/2)/2
  have ep : 0<e := by dsimp [e];linarith
  obtain ⟨N,large⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop ep).comp tendsto_natCast_atTop_atTop).eventually_gt_atTop (86:ℝ))
  obtain ⟨H,late,o,hit⟩ := budget e ep (max (max N B) 1)
  have hp : 0<(H:ℝ) := by exact_mod_cast (show 0<H by omega)
  have room : 86≤(H:ℝ)^e := by
    have t := large H (show N≤H by omega)
    exact (show 86<(H:ℝ)^e by simpa only [Function.comp_apply] using t).le
  refine ⟨H,by omega,(gross_from_either o hp).trans ?_⟩
  rw [Real.sqrt_eq_rpow,show a=1/2+(e+e) by dsimp [e];ring,Real.rpow_add hp,Real.rpow_add hp]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  nlinarith [mul_nonneg (sub_nonneg.mpr room) (Real.rpow_nonneg hp.le e)]

#print axioms PALRH.SourceAllowance.rh_of_sparse_choice

end PALRH.SourceAllowance
