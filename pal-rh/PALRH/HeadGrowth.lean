import PALRH.Protected
import PALRH.Parent
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Filter Set MeasureTheory Complex
open scoped Topology BigOperators
noncomputable section
namespace PALRH.HeadGrowth
open OneTick

private instance : IsFiniteMeasure cellMeasure :=
  isFiniteMeasure_restrict.mpr (by simp [Real.volume_Ioc])

def rowFn (f : ℕ → ℚ) (x : ℝ) : ℂ := f ⌊x⁻¹⌋₊

private theorem rowMem {f : ℕ → ℚ} (hf : bounded f) : MemLp (rowFn f) 2 cellMeasure := by
  obtain ⟨C,hC⟩ := hf
  have meas : Measurable (rowFn f) :=
    (measurable_of_countable (fun k : ℕ => (f k:ℂ))).comp (by fun_prop : Measurable (fun x : ℝ => ⌊x⁻¹⌋₊))
  apply MemLp.of_bound meas.aestronglyMeasurable C (.of_forall ?_)
  intro x
  simpa only [rowFn,Complex.norm_ratCast,Real.norm_eq_abs] using hC ⌊x⁻¹⌋₊

def rowCell (f : ℕ → ℚ) (hf : bounded f) : CellSpace := (rowMem hf).toLp _

theorem rowCell_ae {f : ℕ → ℚ} (hf : bounded f) :
    ⇑(rowCell f hf) =ᵐ[cellMeasure] rowFn f := (rowMem hf).coeFn_toLp

private theorem physical_index {x : ℝ} (hx : x ∈ Ioc (0:ℝ) 1) : 0<⌊x⁻¹⌋₊ :=
  Nat.floor_pos.mpr ((one_le_inv₀ hx.1).mpr hx.2)

theorem occupied_cell (hb : bounded occupied) : rowCell occupied hb=cellConstant := by
  apply Lp.ext
  have h : ⇑cellConstant =ᵐ[cellMeasure] fun _ => (1:ℂ) := (memLp_const (μ:=cellMeasure) (p:=2) (1:ℂ)).coeFn_toLp
  filter_upwards [rowCell_ae hb,h,ae_restrict_mem (μ:=volume) (measurableSet_Ioc (a:=(0:ℝ)) (b:=1))] with x hr hc hx
  rw [hr,hc]
  simp [rowFn,occupied,(physical_index hx).ne']

theorem tick_cell (hb : bounded tick) : rowCell tick hb=cellFirst := by
  apply Lp.ext
  have h : ⇑cellFirst =ᵐ[cellMeasure] fun x : ℝ => if 1/2<x then (1:ℂ) else 0 := MemLp.coeFn_toLp _
  filter_upwards [rowCell_ae hb,h,ae_restrict_mem (μ:=volume) (measurableSet_Ioc (a:=(0:ℝ)) (b:=1))] with x hr hc hx
  rw [hr,hc]
  have pos := physical_index hx
  have iff : ⌊x⁻¹⌋₊=1 ↔ 1/2<x := by
    rw [show ⌊x⁻¹⌋₊=1 ↔ ⌊x⁻¹⌋₊<2 by omega,Nat.floor_lt (inv_nonneg.mpr hx.1.le)]
    rw [inv_lt_iff_one_lt_mul₀ hx.1]
    push_cast
    constructor <;> intro h <;> linarith
  simp only [rowFn,tick,iff]
  split_ifs <;> norm_num

theorem fit_blind {s : ℂ} (hs : 1/2<s.re) (h1 : s≠1) (hz : riemannZeta s=0)
    {f : ℕ → ℚ} (hf : f∈fits) :
    cellMoment hs (rowCell f (fit_properties hf).2)=0 := by
  obtain ⟨N,c,rep⟩ := as_array hf
  let piece := fun i : Fin N => (c i:ℂ) • cellSensor (i.val+2) (by omega)
  have value (i : Fin N) : ⇑(piece i) =ᵐ[cellMeasure] fun x => (c i:ℂ)*sensor (i.val+2) x := by
    have ha : ⇑(cellSensor (i.val+2) (by omega)) =ᵐ[cellMeasure] sensor (i.val+2) := MemLp.coeFn_toLp _
    filter_upwards [ha,Lp.coeFn_smul (c i:ℂ) (cellSensor (i.val+2) (by omega))] with x hr hm
    simp only [piece,hm,Pi.smul_apply,smul_eq_mul,hr]
  have eq : rowCell f (fit_properties hf).2=∑ i, piece i := by
    apply Lp.ext
    filter_upwards [rowCell_ae (fit_properties hf).2,Lp.coeFn_fun_finsetSum Finset.univ piece,
      ae_all_iff.mpr value] with x hr hsum hall
    rw [hr,hsum]
    simp only [hall,rowFn,rep,rowError,sub_sub_cancel,sensor,turn]
    push_cast
    rfl
  rw [eq,map_sum]
  apply Finset.sum_eq_zero
  intro i _
  have hm := moment_sensor hs h1 (by omega : 0 < i.val+2)
  rw [hz,mul_zero] at hm
  have hzero := (mul_eq_zero.mp hm).resolve_left (ne_zero_of_re_pos (by linarith))
  simp [piece,hzero]

private theorem sq_le_loss {T f : ℕ → ℚ} (hT : bounded T) (hf : bounded f) :
    ‖rowCell T hT-rowCell f hf‖^2 ≤ loss T f := by
  let v := rowCell T hT-rowCell f hf
  let q := fun k : ℕ => ((T k:ℝ)-(f k:ℝ))^2
  have hq : (fun x => ‖v x‖^2) =ᵐ[cellMeasure] fun x => q ⌊x⁻¹⌋₊ := by
    filter_upwards [Lp.coeFn_sub (rowCell T hT) (rowCell f hf),rowCell_ae hT,rowCell_ae hf] with x sub a b
    change ‖(rowCell T hT-rowCell f hf) x‖^2=_
    rw [sub,Pi.sub_apply,a,b]
    simp only [rowFn,q,←Rat.cast_sub,Complex.norm_ratCast,sq_abs]
  obtain ⟨A,ha⟩ := hT
  obtain ⟨B,hb⟩ := hf
  let C := (A+B)^2
  have cap (k : ℕ) : q k≤C := by
    dsimp only [q]
    rw [←sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) ((norm_sub_le _ _).trans (add_le_add (ha _) (hb _))) 2
  have positive (n : ℕ) : 0≤rowWeight n*q (n+1) :=
    mul_nonneg (by unfold rowWeight; positivity) (sq_nonneg _)
  have hs : Summable (fun n => rowWeight n*q (n+1)) :=
    Summable.of_nonneg_of_le positive
      (fun n => mul_le_mul_of_nonneg_left (cap _) (by unfold rowWeight; positivity))
      (rowWeight_hasSum.summable.mul_right C)
  let E := ∑' n, rowWeight n*q (n+1)
  have eq : loss T f=E := by simp [E,q,loss,cost]
  have integrable := ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable v)).mp (Lp.memLp v)).congr hq
  have rem : Tendsto (fun M : ℕ => E+C/((M:ℝ)+1)) atTop (𝓝 E) := by
    simpa [div_eq_mul_inv] using tendsto_const_nhds.add
      ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).const_mul C)
  rw [eq]
  change ‖v‖^2 ≤ E
  rw [norm_sq_cells,integral_congr_ae hq]
  apply ge_of_tendsto' rem
  intro M
  apply (cell_integral_bound q C M integrable cap).trans
  apply add_le_add _ (le_refl _)
  simpa only [E,rowWeight,div_eq_mul_inv,one_mul,mul_comm] using
    hs.sum_le_tsum (Finset.range M) (fun n _ => positive n)

/-- The exact head confines the entire surviving observation to the remaining
physical interval. This gives a power cost independently of coefficient width. -/
theorem head_power_floor {s : ℂ} (hs : 1/2<s.re) {T f : ℕ → ℚ} (hT : bounded T)
    (hf : bounded f) (blind : cellMoment hs (rowCell f hf)=0) (H : ℕ)
    (head : ∀ k : ℕ, 0<k → k≤H → f k=T k) :
    ((2*s.re-1)*‖cellMoment hs (rowCell T hT)‖^2)*((H:ℝ)+1)^(2*s.re-1) ≤ loss T f := by
  let u := 1/((H:ℝ)+1)
  let v := rowCell T hT-rowCell f hf
  have hu : 0<u := by dsimp [u]; positivity
  have unit : u≤1 := by dsimp [u]; apply (div_le_iff₀ (by positivity)).mpr; simp
  have vanish : ∀ᵐ x ∂cellMeasure, u<x → v x=0 := by
    filter_upwards [Lp.coeFn_sub (rowCell T hT) (rowCell f hf),rowCell_ae hT,rowCell_ae hf,
      ae_restrict_mem (μ:=volume) (measurableSet_Ioc (a:=(0:ℝ)) (b:=1))] with x sub a b hx
    intro above
    have bound : ⌊x⁻¹⌋₊ < H+1 := by
      apply (Nat.floor_lt (inv_nonneg.mpr hx.1.le)).mpr
      rw [inv_lt_iff_one_lt_mul₀ hx.1]
      have he := (div_lt_iff₀ (show 0<(H:ℝ)+1 by positivity)).mp above
      push_cast
      nlinarith
    have same := head _ (physical_index hx) (by omega)
    change (rowCell T hT-rowCell f hf) x=0
    simp only [sub,Pi.sub_apply,a,b,rowFn,same,sub_self]
  have cap := localized_moment hs hu unit v vanish
  have obs : cellMoment hs v=cellMoment hs (rowCell T hT) := by simp [v,blind]
  rw [obs] at cap
  have hbase : 0<(H:ℝ)+1 := by positivity
  have hp : 0<((H:ℝ)+1)^(2*s.re-1) := Real.rpow_pos_of_pos hbase _
  have eq : u^(2*s.re-1) = (((H:ℝ)+1)^(2*s.re-1))⁻¹ := by dsimp only [u]; rw [one_div,Real.inv_rpow hbase.le]
  rw [eq] at cap
  have he := (le_div_iff₀ hp).mp (show (2*s.re-1)*‖cellMoment hs (rowCell T hT)‖^2 ≤
      ‖v‖^2/((H:ℝ)+1)^(2*s.re-1) by simpa only [div_eq_inv_mul] using cap)
  exact he.trans (sq_le_loss hT hf)


/-- At arbitrarily large exact heads, the total squared loss may grow more
slowly than every positive power. Support and head are independently chosen. -/
def SubpowerHeads (T : ℕ → ℚ) : Prop :=
  ∀ α : ℝ, 0<α → ∀ K : ℕ, ∃ H : ℕ, K≤H ∧ ∃ f ∈ fits,
    (∀ k : ℕ, 0<k → k≤H → f k=T k) ∧ loss T f ≤ ((H:ℝ)+1)^α

private theorem excludes_zero {T : ℕ → ℚ} (hT : bounded T) (can : SubpowerHeads T) {s : ℂ}
    (hs : 1/2<s.re) (h1 : s≠1) (visible : cellMoment hs (rowCell T hT)≠0) : riemannZeta s≠0 := by
  intro hz
  let a := (2*s.re-1)/2
  have apos : 0<a := by dsimp [a]; linarith
  let c := (2*s.re-1)*‖cellMoment hs (rowCell T hT)‖^2
  have cpos : 0<c := mul_pos (by linarith) (sq_pos_of_pos (norm_pos_iff.mpr visible))
  have base : Tendsto (fun H : ℕ => (H:ℝ)+1) atTop atTop :=
    tendsto_atTop_mono (fun n : ℕ => show (n:ℝ)≤(n:ℝ)+1 by linarith) tendsto_natCast_atTop_atTop
  have eventuallyBig := ((tendsto_rpow_atTop apos).comp base).eventually_gt_atTop (1/c)
  obtain ⟨K,hK⟩ := eventually_atTop.mp eventuallyBig
  obtain ⟨H,hH,f,hf,head,price⟩ := can a apos K
  have above : 1 < c*((H:ℝ)+1)^a := by
    have large : 1/c < ((H:ℝ)+1)^a := by simpa only [Function.comp_apply] using hK H hH
    linarith [(div_lt_iff₀ cpos).mp large]
  have paid := (head_power_floor hs hT (fit_properties hf).2 (fit_blind hs h1 hz hf) H head).trans price
  change c*((H:ℝ)+1)^(2*s.re-1) ≤ _ at paid
  rw [show 2*s.re-1=a+a by dsimp [a]; ring,Real.rpow_add (by positivity)] at paid
  have strict := mul_lt_mul_of_pos_right above (Real.rpow_pos_of_pos (show 0<(H:ℝ)+1 by positivity) a)
  nlinarith

/-- Subpolynomial cost for the occupied target is sufficient for the bare Mathlib RH. -/
theorem rh_of_subpower_occupied (can : SubpowerHeads occupied) : RiemannHypothesis := by
  apply rh_of_right
  intro s hs h1
  have hT : bounded occupied := ⟨1,fun k => by by_cases k0:k=0 <;> simp [occupied,k0]⟩
  apply excludes_zero hT can hs h1
  rw [occupied_cell,moment_constant hs]
  exact one_div_ne_zero (ne_zero_of_re_pos (by linarith))

/-- The very same budget on the sole first tick suffices. -/
theorem rh_of_subpower_tick (can : SubpowerHeads tick) : RiemannHypothesis := by
  apply rh_of_right
  intro s hs h1
  have hT : bounded tick := ⟨1,fun k => by by_cases k1:k=1 <;> simp [tick,k1]⟩
  apply excludes_zero hT can hs h1
  rw [tick_cell]
  exact moment_first_ne hs

#print axioms PALRH.HeadGrowth.head_power_floor
#print axioms PALRH.HeadGrowth.rh_of_subpower_occupied
#print axioms PALRH.HeadGrowth.rh_of_subpower_tick

end PALRH.HeadGrowth
