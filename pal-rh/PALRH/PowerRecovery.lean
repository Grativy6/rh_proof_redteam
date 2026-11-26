import PALRH.OneSidedBoard
import PALRH.DyadicShape

open Finset Set MeasureTheory
open scoped BigOperators Interval

noncomputable section
namespace PALRH.PowerRecovery
open PositivePrimitive LogPrimitive PrimeDivisorPrimitive

/-- Alternating reads of a nondecreasing nonnegative scale have total at most its first value. -/
private theorem scale_telescope {w : ℝ → ℝ} (mono : MonotoneOn w (Ici 0)) {x : ℝ}
    (xp : 0≤x) (N : ℕ) : alternating w N x+w (x/(2*(N:ℝ)+1))≤w x := by
  induction N with
  | zero => simp [alternating]
  | succ k ih =>
    unfold alternating at *
    rw [sum_range_succ]
    have down : w (x/(2*((k:ℝ)+1)+1))≤w (x/(2*(k:ℝ)+2)) :=
      mono (mem_Ici.mpr (by positivity)) (mem_Ici.mpr (by positivity)) (div_le_div_of_nonneg_left xp (by positivity) (by linarith))
    push_cast
    linarith only [ih,down]

/-- A bounded observation horizon may choose its own orientation. All reciprocal
dilations used in the first-pair argument stay within it. -/
theorem local_scale {f w : ℝ → ℝ} {D K q T : ℝ} (dn : 0≤D) (kn : 0≤K)
    (qn : 0≤q) (ql : q<1) (wn : ∀ t : ℝ, 0≤t → 0≤w t)
    (mono : MonotoneOn w (Ici 0)) (zero : w 0=0)
    (half : ∀ t : ℝ, 1≤t → w (t/2)≤q*w t)
    (early : ∀ t : ℝ, 0≤t → t<1 → f t=0)
    (increments : ∀ x y : ℝ, 0≤y → y≤x → x≤T → f x-f y≤D*(w x-w y))
    (readout : ∀ t : ℝ, 1≤t → t≤T → ∃ N : ℕ, 0<N ∧ -(K*w t)≤alternating f N t)
    {x : ℝ} (xp : 0≤x) (within : x≤T) : |f x|≤((D+K)/(1-q))*w x := by
  let p:=fun t => D*w t-f t
  let H:ℝ:=(D+K)/(1-q)
  have denom : 0<1-q := by linarith
  have hn : 0≤H := div_nonneg (add_nonneg dn kn) denom.le
  have recurrence : H*(1-q)=D+K := div_mul_cancel₀ _ denom.ne'
  have dH : D≤H := by nlinarith only [recurrence,mul_nonneg hn qn,kn]
  have mon {a b : ℝ} (an : 0≤a) (ab : a≤b) (bt : b≤T) : p a≤p b := by
    dsimp [p];linarith only [increments b a an ab bt]
  have step (t : ℝ) (large : 1≤t) (tt : t≤T) : p t≤p (t/2)+(D+K)*w t := by
    have tn:=zero_le_one.trans large
    obtain ⟨N,live,obs⟩:=readout t large tt
    have paired (i : ℕ) : 0≤p (t/(2*(i:ℝ)+1))-p (t/(2*(i:ℝ)+2)) := by
      apply sub_nonneg.mpr
      apply mon (by positivity) (div_le_div_of_nonneg_left tn (by positivity) (by linarith))
      exact (div_le_self tn (by linarith only [Nat.cast_nonneg (α:=ℝ) i])).trans tt
    have first:=Finset.single_le_sum (fun i (_ : i∈range N) => paired i) (mem_range.mpr live)
    change _ ≤ alternating p N t at first
    simp only [Nat.cast_zero,mul_zero,zero_add,div_one] at first
    have eq : alternating p N t=D*alternating w N t-alternating f N t := by
      unfold alternating p;rw [mul_sum,←sum_sub_distrib];apply sum_congr rfl;intro _ _;ring
    rw [eq] at first
    have tel:=scale_telescope mono tn N
    have nn:=wn (t/(2*(N:ℝ)+1)) (by positivity)
    have cap:=mul_le_mul_of_nonneg_left (show alternating w N t≤w t by linarith only [tel,nn]) dn
    linarith only [first,cap,obs]
  have bound (n : ℕ) : ∀ t : ℝ, 0≤t → t≤T → ⌊t⌋₊=n → p t≤H*w t := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro t tn tt index
      by_cases low : t<1
      · dsimp [p];rw [early t tn low,sub_zero]
        exact mul_le_mul_of_nonneg_right dH (wn t tn)
      have one:=le_of_not_gt low
      have np : 0<n := index ▸ Nat.floor_pos.mpr one
      have nr : (1:ℝ)≤n := by exact_mod_cast np
      have fence:=Nat.lt_floor_add_one t
      rw [index] at fence
      have ht : 0≤t/2 := by positivity
      have before : t/2≤T := by linarith only [tn,tt]
      have smaller : ⌊t/2⌋₊<n := (Nat.floor_lt ht).mpr (by linarith)
      have old:=ih _ smaller (t/2) ht before rfl
      have eq:=congrArg (fun z : ℝ => z*w t) recurrence
      nlinarith only [old,step t one tt,eq,mul_le_mul_of_nonneg_left (half t one) hn]
  have past:=bound _ x xp within rfl
  dsimp [p] at past
  have top:=increments x 0 le_rfl xp within
  rw [early 0 le_rfl (by norm_num),zero,sub_zero,sub_zero] at top
  change |f x|≤H*w x
  exact abs_le.mpr ⟨by nlinarith only [past,mul_nonneg dn (wn x xp)],
    top.trans (mul_le_mul_of_nonneg_right dH (wn x xp))⟩

/-- The first pair of the dilated readings supplies an upper bound for the barrier
minus the unknown primitive. The scale may be any increasing contracted weight. -/
theorem signed_scale {f w : ℝ → ℝ} {D K : ℝ} (dn : 0≤D) (kn : 0≤K)
    (wn : ∀ t : ℝ, 0≤t → 0≤w t) (mono : MonotoneOn w (Ici 0)) (zero : w 0=0)
    (half : ∀ t : ℝ, 1≤t → 4*w (t/2)≤3*w t)
    (early : ∀ t : ℝ, 0≤t → t<1 → f t=0)
    (increments : ∀ x y : ℝ, 0≤y → y≤x → f x-f y≤D*(w x-w y))
    (readout : ∀ x : ℝ, 1≤x → ∃ N : ℕ, 0<N ∧ -(K*w x)≤alternating f N x)
    {x : ℝ} (xp : 0≤x) : |f x|≤4*(D+K)*w x := by
  have out:=local_scale dn kn (by norm_num : 0≤(3/4:ℝ)) (by norm_num : (3/4:ℝ)<1) wn mono zero
    (fun t ht => by linarith only [half t ht]) early
    (fun a b bn ba _ => increments a b bn ba) (fun t ht _ => readout t ht) xp (le_refl x)
  convert out using 1;ring

theorem half_power {b t : ℝ} (bh : 1/2≤b) (tn : 0≤t) :
    4*(t/2)^b≤3*t^b := by
  have lower : 4/3≤(2:ℝ)^b := by
    have m:=Real.rpow_le_rpow_of_exponent_le (by norm_num : 1≤(2:ℝ)) bh
    rw [←Real.sqrt_eq_rpow] at m
    have sq:=Real.sq_sqrt (by norm_num : 0≤(2:ℝ))
    nlinarith only [m,sq,Real.sqrt_nonneg 2]
  have zp:=Real.rpow_pos_of_pos (by norm_num : 0<(2:ℝ)) b
  rw [Real.div_rpow tn (by norm_num),←mul_div_assoc]
  apply (div_le_iff₀ zp).mpr
  nlinarith only [mul_le_mul_of_nonneg_left lower (Real.rpow_nonneg tn b)]

/-- A one-sided price on a logarithmic density supplies an increment bound in that same scale. -/
theorem local_increment {b C sign T : ℝ} (bp : 0<b) (cn : 0≤C)
    (upper : ∀ t : ℝ, 1≤t → t≤T → sign*value t≤C*t^b)
    {x y : ℝ} (yn : 0≤y) (yx : y≤x) (xt : x≤T) :
    sign*primitive x-sign*primitive y≤(C/b)*(x^b-y^b) := by
  have int:=density_int yn yx
  have from0:=density_int (a:=0) le_rfl yn
  have lower : 0≤x := yn.trans yx
  have eq : sign*primitive x-sign*primitive y=∫ t in y..x,sign*density t := by
    unfold primitive
    rw [←intervalIntegral.integral_add_adjacent_intervals from0 int,intervalIntegral.integral_const_mul]
    ring
  have integrable:=intervalIntegral.intervalIntegrable_rpow' (a:=y) (b:=x) (r:=b-1) (by linarith)
  have bound:=intervalIntegral.integral_mono_on yx (int.const_mul sign) (integrable.const_mul C)
    (fun t ht => by
      have tn:=yn.trans ht.1
      by_cases zero : t=0
      · rw [zero];simp [density];exact mul_nonneg cn (Real.rpow_nonneg (by norm_num) _)
      have tp:=lt_of_le_of_ne tn (Ne.symm zero)
      have pay : sign*value t≤C*t^b := by
        by_cases large : 1≤t
        · exact upper t large (ht.2.trans xt)
        · rw [value_early (lt_of_not_ge large),mul_zero];exact mul_nonneg cn (Real.rpow_nonneg tn _)
      have divide:=div_le_div_of_nonneg_right pay tn
      simpa only [density,mul_div_assoc,Real.rpow_sub_one tp.ne'] using divide)
  rw [eq]
  apply bound.trans
  rw [intervalIntegral.integral_const_mul,integral_rpow (Or.inl (by linarith : (-1:ℝ)<b-1)),
    show b-1+1=b by ring]
  exact le_of_eq (by ring)


theorem scaled_increment {b C sign : ℝ} (bp : 0<b) (cn : 0≤C)
    (upper : ∀ t : ℝ, 1≤t → sign*value t≤C*t^b)
    {x y : ℝ} (yn : 0≤y) (yx : y≤x) :
    sign*primitive x-sign*primitive y≤(C/b)*(x^b-y^b) :=
  local_increment bp cn (fun t ht _ => upper t ht) yn yx (le_refl x)

/-- A one-sided power estimate on the actual integrated von Mangoldt counts transfers in
both possible orientations. The paired divisor readings and their signs are discharged here. -/
theorem rh_of_signed_value (sign : ℝ) (orientation : sign=1 ∨ sign= -1)
    (upper : ∀ b : ℝ, 1/2<b → b<1 → ∃ C : ℝ, 0≤C ∧
      ∀ t : ℝ, 1≤t → sign*value t≤C*t^b) : RiemannHypothesis := by
  apply PrimitiveMellin.rh_of_primitive_powers
  intro b bh bl
  obtain ⟨C,cn,paid⟩:=upper b bh bl
  have bp : 0<b := by linarith only [bh]
  have dn : 0≤C/b := div_nonneg cn bp.le
  refine ⟨4*(C/b+24),by positivity,?_⟩
  intro t ht
  let w:=fun v : ℝ => v^b
  let f:=fun v : ℝ => sign*primitive v
  have mag : |sign|=1 := by rcases orientation with h|h <;> simp [h]
  have wn (v : ℝ) (vn : 0≤v) : 0≤w v := Real.rpow_nonneg vn _
  have mono : MonotoneOn w (Ici 0) := fun _ ha _ _ ab => Real.rpow_le_rpow ha ab bp.le
  have base (v : ℝ) (vn : 0≤v) (early : v<1) : f v=0 := by
    dsimp [f];rw [PrimitiveRecovery.primitive_early vn early,mul_zero]
  have bills (v : ℝ) (one : 1≤v) : ∃ N : ℕ, 0<N ∧ -(24*w v)≤alternating f N v := by
    let N:=⌊v⌋₊+1
    refine ⟨N,Nat.succ_pos _,?_⟩
    have vn:=zero_le_one.trans one
    have root : Real.sqrt v≤w v := by
      dsimp [w];rw [Real.sqrt_eq_rpow];exact Real.rpow_le_rpow_of_exponent_le one bh.le
    have same : alternating f N v=sign*alternating primitive N v := by
      unfold alternating f;rw [mul_sum];apply sum_congr rfl;intro _ _;ring
    rw [same]
    have cover : ⌊v⌋₊≤2*N := by dsimp [N];omega
    rcases orientation with yes|no
    · rw [yes,one_mul];linarith only [root,PrimitiveRecovery.observed_primitive vn cover]
    · rw [no,neg_one_mul];linarith only [root,PrimitiveRecovery.observed_primitive_upper vn cover]
  have bound:=signed_scale dn (by norm_num : 0≤(24:ℝ)) wn mono (Real.zero_rpow bp.ne')
    (fun v one => half_power bh.le (zero_le_one.trans one)) base
    (fun v z zp zv => scaled_increment bp cn paid zp zv) bills (x:=1/t) (one_div_nonneg.mpr ht.1.le)
  dsimp [f,w] at bound
  rw [abs_mul,mag,one_mul] at bound
  rw [OneSidedBoard.reciprocal_read ht,Complex.norm_real,Real.norm_eq_abs]
  simpa only [one_div,Real.inv_rpow ht.1.le,Real.rpow_neg ht.1.le] using bound

#print axioms PALRH.PowerRecovery.rh_of_signed_value

end PALRH.PowerRecovery
