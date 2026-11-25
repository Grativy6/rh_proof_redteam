import PALRH.Cells
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Tactic

noncomputable section
open Complex Filter Set MeasureTheory Asymptotics
open scoped Topology
namespace PALRH

/-- Reciprocal cells (1/(k+1), 1/k] carry the residue of k modulo d. -/
def sensor (d : ℕ) (x : ℝ) : ℂ :=
  ((⌊x⁻¹⌋₊ % d : ℕ) : ℂ) / d

/-- The unbalanced floor, used only where its Mellin integral converges. -/
def stair (x : ℝ) : ℂ := (⌊x⁻¹⌋₊ : ℕ)

theorem sensor_norm_le {d : ℕ} (hd : 0 < d) (x : ℝ) : ‖sensor d x‖ ≤ 1 := by
  have hm := Nat.mod_lt ⌊x⁻¹⌋₊ hd
  rw [sensor, norm_div, Complex.norm_natCast, Complex.norm_natCast, div_le_one (by positivity)]
  exact_mod_cast hm.le

theorem sensor_measurable (d : ℕ) : Measurable (sensor d) := by
  unfold sensor
  fun_prop

theorem sensor_of_one_lt {x : ℝ} (hx : 1 < x) (d : ℕ) : sensor d x = 0 := by
  have hfloor : ⌊x⁻¹⌋₊ = 0 := Nat.floor_eq_zero.mpr (inv_lt_one_of_one_lt₀ hx)
  simp [sensor, hfloor]

theorem sensor_eq {d : ℕ} (hd : 0 < d) (x : ℝ) :
    sensor d x = (d : ℂ)⁻¹ * stair x - stair ((d : ℝ) * x) := by
  have hfloor : ⌊((d : ℝ) * x)⁻¹⌋₊ = ⌊x⁻¹⌋₊ / d := by
    rw [mul_inv_rev, ← div_eq_mul_inv, Nat.floor_div_natCast]
  have hn : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have h := Nat.mod_add_div ⌊x⁻¹⌋₊ d
  have hc : ((⌊x⁻¹⌋₊ % d : ℕ) : ℂ) + (d : ℂ) * ((⌊x⁻¹⌋₊ / d : ℕ) : ℂ) = ⌊x⁻¹⌋₊ := by
    exact_mod_cast h
  simp only [sensor, stair, hfloor]
  field_simp
  simp only [one_div]
  linear_combination hc

/-- Recover the critical line from the right half-plane using the completed
zeta functional equation and the exact poles of the real gamma factor. -/
theorem rh_of_right (h : ∀ s : ℂ, 1/2 < s.re → s ≠ 1 → riemannZeta s ≠ 0) :
    RiemannHypothesis := by
  intro s hs htriv hs1
  rcases lt_trichotomy s.re (1/2) with hlt | he | hgt
  · exfalso
    have hzero : s ≠ 0 := by
      rintro rfl
      rw [riemannZeta_zero] at hs
      norm_num at hs
    have hg : s.Gammaℝ ≠ 0 := by
      intro hγ
      obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp hγ
      cases n with
      | zero => exact hzero (by simpa using hn)
      | succ n =>
        apply htriv ⟨n, ?_⟩
        push_cast at hn ⊢
        linear_combination hn
    have hz : completedRiemannZeta s = 0 := by
      rw [riemannZeta_def_of_ne_zero hzero, div_eq_zero_iff] at hs
      exact hs.resolve_right hg
    have ht : 1/2 < (1-s).re := by rw [sub_re, one_re]; linarith
    have ht0 : (1-s : ℂ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
    have ht1 : (1-s : ℂ) ≠ 1 := by
      intro h'
      apply hzero
      linear_combination -h'
    apply h _ ht ht1
    rw [riemannZeta_def_of_ne_zero ht0, completedRiemannZeta_one_sub, hz, zero_div]
  · exact he
  · exact False.elim (h s hgt hs1 hs)

private lemma eventually_zero_bound {f : ℝ → ℂ} (hf : ∀ x > 1, f x = 0) (a : ℝ) :
    f =O[atTop] fun x => x ^ (-a) := by
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  simp [hf x hx]

private lemma stair_norm (x : ℝ) : ‖stair x‖ ≤ ‖x⁻¹‖ := by
  rw [stair, Complex.norm_natCast, Real.norm_eq_abs]
  by_cases hx : 0 ≤ x⁻¹
  · exact (Nat.floor_le hx).trans (le_abs_self _)
  · simp [Nat.floor_eq_zero.mpr (lt_trans (lt_of_not_ge hx) zero_lt_one)]

private lemma stair_convergent {s : ℂ} (hs : 1 < s.re) : MellinConvergent stair s := by
  apply mellinConvergent_of_isBigO_rpow (a := s.re + 1) (b := 1)
  · have hi : ContinuousOn (fun x : ℝ => x⁻¹) (Ioi 0) :=
      continuousOn_id.inv₀ fun x hx => ne_of_gt hx
    apply (hi.locallyIntegrableOn measurableSet_Ioi).mono
    · have hm : Measurable stair := by unfold stair; fun_prop
      exact hm.aestronglyMeasurable
    · exact .of_forall stair_norm
  · apply eventually_zero_bound
    intro x hx
    simp [stair, Nat.floor_eq_zero.mpr (inv_lt_one_of_one_lt₀ hx)]
  · linarith
  · apply isBigO_of_le _
    intro x
    simpa only [Real.rpow_neg_one] using stair_norm x
  · exact hs

private lemma sensor_differentiable {d : ℕ} (hd : 0 < d) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (mellin (sensor d)) s := by
  apply mellin_differentiableAt_of_isBigO_rpow (a := s.re + 1) (b := 0)
  · apply (locallyIntegrableOn_const (1 : ℝ)).mono (sensor_measurable d).aestronglyMeasurable
    exact .of_forall fun x => by simpa using sensor_norm_le hd x
  · exact eventually_zero_bound (fun x hx => sensor_of_one_lt hx d) _
  · linarith
  · apply isBigO_of_le _
    intro x
    simpa using sensor_norm_le hd x
  · exact hs

private lemma zeta_eq_stair {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = s * mellin stair s := by
  have hsum (n : ℕ) : (∑ k ∈ Finset.Icc 1 n, (1 : ℕ → ℂ) k) = n := by
    simp [Nat.card_Icc]
  have hb : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, (1 : ℕ → ℂ) k)
      =O[atTop] fun n => (n : ℝ) ^ (1 : ℝ) := by
    apply isBigO_of_le _
    intro n
    simp
  rw [← LSeries_one_eq_riemannZeta (s := s) hs,
    LSeries_eq_mul_integral _ zero_le_one hs (LSeriesSummable_one_iff.mpr hs) hb]
  congr 1
  simp only [hsum]
  let f : ℝ → ℂ := fun x => (⌊x⌋₊ : ℕ)
  change _ = mellin (fun x => f x⁻¹) s
  rw [mellin_comp_inv, mellin]
  let g : ℝ → ℂ := fun x => (x : ℂ) ^ (-s - 1) • f x
  change _ = ∫ x in Ioi 0, g x
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (Ici_subset_Ioi.mpr (zero_lt_one : (0 : ℝ) < 1)) (f := g) (by
        intro x hx
        have hlt : x < 1 := lt_of_not_ge hx.2
        simp [g, f, Nat.floor_eq_zero.mpr hlt]), integral_Ici_eq_integral_Ioi]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x _
  simp only [g, f, smul_eq_mul, neg_add_rev, sub_eq_add_neg]
  ring_nf

private lemma mellin_subtract {f g : ℝ → ℂ} {s : ℂ}
    (hf : MellinConvergent f s) (hg : MellinConvergent g s) :
    mellin (fun x => f x - g x) s = mellin f s - mellin g s := by
  simp only [mellin, smul_sub]
  exact integral_sub hf hg

private lemma mellin_sensor_right {d : ℕ} (hd : 0 < d) {s : ℂ} (hs : 1 < s.re) :
    s * mellin (sensor d) s = ((d : ℂ)⁻¹ - (d : ℂ) ^ (-s)) * riemannZeta s := by
  have h : sensor d = fun x => (d : ℂ)⁻¹ • stair x - stair ((d : ℝ)*x) :=
    funext (sensor_eq hd)
  have hc := stair_convergent hs
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  rw [h, mellin_subtract (hc.const_smul _) ((MellinConvergent.comp_mul_left hd').mpr hc),
    mellin_const_smul, mellin_comp_mul_left _ _ hd', zeta_eq_stair hs]
  push_cast
  simp only [smul_eq_mul]
  ring

/-- A zero on the open right half of the strip annihilates every residue sensor. -/
theorem mellin_sensor_zero {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1)
    (hz : riemannZeta s = 0) {d : ℕ} (hd : 0 < d) : mellin (sensor d) s = 0 := by
  let U : Set ℂ := {z | 0 < z.re}
  have hU : IsOpen U := isOpen_lt continuous_const continuous_re
  let F := fun z : ℂ => (z-1) * (z * mellin (sensor d) z)
  let G := fun z : ℂ => ((d : ℂ)⁻¹ - (d : ℂ)^(-z)) * riemannZeta₁ z
  have hD : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hF : AnalyticOnNhd ℂ F U := by
    apply DifferentiableOn.analyticOnNhd _ hU
    intro z hz
    exact (((differentiableAt_id.sub_const 1).mul
      (differentiableAt_id.mul (sensor_differentiable hd hz))).differentiableWithinAt)
  have hG : AnalyticOnNhd ℂ G U := by
    apply DifferentiableOn.analyticOnNhd _ hU
    intro z _
    exact ((differentiableAt_const _).sub
      (differentiableAt_id.neg.const_cpow (Or.inl hD)) |>.mul
      (differentiable_riemannZeta₁ z)).differentiableWithinAt
  have hfactor (z : ℂ) (hz1 : z ≠ 1) : (z-1) * riemannZeta z = riemannZeta₁ z := by
    rw [riemannZeta_eq_inv_sub_mul hz1]
    field_simp [sub_ne_zero.mpr hz1]
  have heq : EqOn F G U :=
    hF.eqOn_of_preconnected_of_eventuallyEq hG (convex_halfSpace_re_gt 0).isPreconnected
      (by norm_num [U] : (2 : ℂ) ∈ U)
      (eventuallyEq_of_mem ((isOpen_lt continuous_const continuous_re).mem_nhds
          (by norm_num : (1 : ℝ) < (2 : ℂ).re)) (by
        intro z (hz : 1 < z.re)
        have h1 : z ≠ 1 := by rintro rfl; norm_num at hz
        dsimp [F, G]
        rw [mellin_sensor_right hd hz, ← hfactor z h1]
        ring))
  have h := heq (show s ∈ U from hs)
  dsimp [F, G] at h
  rw [← hfactor s hs1, hz, mul_zero, mul_zero] at h
  exact (mul_eq_zero.mp ((mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hs1))).resolve_left
    (ne_zero_of_re_pos hs)

/-- Lebesgue length assigns cell k the weight 1/(k(k+1)). -/
abbrev cellMeasure : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)
abbrev CellSpace := Lp ℂ 2 cellMeasure

private instance : IsFiniteMeasure cellMeasure :=
  isFiniteMeasure_restrict.mpr (by simp [Real.volume_Ioc])

private def target : CellSpace := (memLp_const (μ := cellMeasure) (1 : ℂ)).toLp _
private def reading (n : ℕ) : CellSpace :=
  (MemLp.of_bound (μ := cellMeasure) (p := 2)
    (sensor_measurable (n+2)).aestronglyMeasurable 1
    (.of_forall (sensor_norm_le (by omega : 0 < n+2)))).toLp _

/-- Arbitrarily accurate approximation of the constant 1 by finite complex linear
combinations of the integer remainder functions in the squared cell-length norm. -/
def ResidueApproximation : Prop :=
  target ∈ (Submodule.span ℂ (Set.range reading)).topologicalClosure

private def kernelFn (s : ℂ) (x : ℝ) : ℂ := starRingEnd ℂ ((x : ℂ) ^ (s-1))

private theorem kernel_mem {s : ℂ} (hs : 1/2 < s.re) :
    MemLp (kernelFn s) 2 cellMeasure := by
  have hm : Measurable (kernelFn s) := by unfold kernelFn; fun_prop
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).2
  change IntegrableOn _ (Ioc (0 : ℝ) 1)
  have hi : IntegrableOn (fun x : ℝ => x ^ (2*(s.re-1))) (Ioc (0 : ℝ) 1) :=
    (integrableOn_Ioc_iff_integrableOn_Ioo (by finiteness)).mpr
      ((intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).mpr (by linarith))
  apply hi.congr_fun _ measurableSet_Ioc
  intro x hx
  change x ^ (2*(s.re-1)) = ‖starRingEnd ℂ ((x : ℂ)^(s-1))‖ ^ 2
  rw [Complex.norm_conj, norm_cpow_eq_rpow_re_of_pos hx.1, sub_re, one_re,
    mul_comm (2:ℝ), Real.rpow_mul hx.1.le, Real.rpow_two]

private theorem kernel_inner {s : ℂ} (hs : 1/2 < s.re) {f : ℝ → ℂ}
    (hf : MemLp f 2 cellMeasure) :
    inner ℂ ((kernel_mem hs).toLp _) (hf.toLp _) =
      ∫ x in Ioc (0 : ℝ) 1, (x : ℂ)^(s-1) * f x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(kernel_mem hs).coeFn_toLp, hf.coeFn_toLp] with x hx hfx
  rw [RCLike.inner_apply', hx, hfx]
  simp [kernelFn]

private theorem kernel_target {s : ℂ} (hs : 1/2 < s.re) :
    inner ℂ ((kernel_mem hs).toLp _) target = 1/s := by
  rw [target, kernel_inner hs]
  simp only [mul_one]
  rw [← intervalIntegral.integral_of_le zero_le_one, integral_cpow (Or.inl (by
    rw [sub_re, one_re]; linarith)), sub_add_cancel]
  have hs0 : s ≠ 0 := ne_zero_of_re_pos (by linarith)
  simp [Complex.zero_cpow hs0]

private theorem kernel_reading {s : ℂ} (hs : 1/2 < s.re) (n : ℕ) :
    inner ℂ ((kernel_mem hs).toLp _) (reading n) = mellin (sensor (n+2)) s := by
  rw [reading, kernel_inner hs, mellin]
  symm
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self
  intro x hx
  have h : 1 < x := lt_of_not_ge fun hle => hx.2 ⟨hx.1, hle⟩
  simp [sensor_of_one_lt h]

/-- One geometric approximation hypothesis implies Mathlib's RH. -/
theorem rh_of_residue_approximation (h : ResidueApproximation) : RiemannHypothesis := by
  apply rh_of_right
  intro s hs hs1 hz
  let T := innerSL ℂ ((kernel_mem hs).toLp (kernelFn s))
  have hspan : Submodule.span ℂ (Set.range reading) ≤ T.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨n, rfl⟩
    change inner ℂ ((kernel_mem hs).toLp _) (reading n) = 0
    rw [kernel_reading hs, mellin_sensor_zero (by linarith) hs1 hz (by omega)]
  have hz' := (Submodule.span ℂ (Set.range reading)).topologicalClosure_minimal hspan T.isClosed_ker h
  change inner ℂ ((kernel_mem hs).toLp _) target = 0 at hz'
  rw [kernel_target hs] at hz'
  exact (one_div_ne_zero (ne_zero_of_re_pos (by linarith : 0 < s.re))) hz'

#print axioms PALRH.rh_of_residue_approximation

/-- Row error, signed so that the constant target has value one. Entry i has modulus i+2. -/
def rowError {N : ℕ} (c : Fin N → ℚ) (k : ℕ) : ℚ :=
  1 - ∑ i, c i * turn (i.val+2) k

def envelope {N : ℕ} (c : Fin N → ℚ) : ℚ := 1 + ∑ i, |c i|

/-- A rational upper bound on the squared error over every positive integer. -/
def certificateValue {N : ℕ} (c : Fin N → ℚ) (M : ℕ) : ℚ :=
  (∑ i ∈ Finset.range M, rowError c (i+1)^2 / (((i:ℚ)+1)*((i:ℚ)+2))) +
    envelope c ^ 2 / ((M:ℚ)+1)

/-- Every tolerance has one finite rational witness. -/
def FiniteCertificates : Prop :=
  ∀ K : ℕ, ∃ (N M : ℕ) (c : Fin N → ℚ), certificateValue c M < 1/((K:ℚ)+1)

private lemma row_bound {N : ℕ} (c : Fin N → ℚ) (k : ℕ) :
    |rowError c k| ≤ envelope c := by
  have ht (i : Fin N) : |turn (i.val+2) k| ≤ 1 := by
    rw [turn, abs_of_nonneg (by positivity), div_le_one (by positivity)]
    exact_mod_cast (Nat.mod_lt k (by omega : 0 < i.val+2)).le
  calc
    |rowError c k| ≤ |(1 : ℚ)| + |∑ i, c i * turn (i.val+2) k| := abs_sub _ _
    _ ≤ 1 + ∑ i, |c i * turn (i.val+2) k| := by
      rw [abs_one]; gcongr; apply Finset.abs_sum_le_sum_abs
    _ ≤ envelope c := by
      unfold envelope
      apply add_le_add (le_refl (1 : ℚ))
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (ht i)

private def candidate {N : ℕ} (c : Fin N → ℚ) : CellSpace :=
  ∑ i, (c i : ℂ) • reading i

private theorem residual_ae {N : ℕ} (c : Fin N → ℚ) :
    ⇑(target - candidate c) =ᵐ[cellMeasure] fun x => (rowError c ⌊x⁻¹⌋₊ : ℂ) := by
  have ht : ⇑target =ᵐ[cellMeasure] fun _ => (1 : ℂ) := MemLp.coeFn_toLp _
  have pieces (i : Fin N) :
      ⇑((c i : ℂ) • reading i) =ᵐ[cellMeasure] fun x => (c i : ℂ) * sensor (i.val+2) x := by
    have hr : ⇑(reading i) =ᵐ[cellMeasure] sensor (i.val+2) := MemLp.coeFn_toLp _
    filter_upwards [Lp.coeFn_smul (c i : ℂ) (reading i), hr] with x h1 h2
    simp only [h1, Pi.smul_apply, smul_eq_mul, h2]
  filter_upwards [Lp.coeFn_sub target (candidate c), ht, ae_all_iff.mpr pieces,
    Lp.coeFn_fun_finsetSum Finset.univ (fun i : Fin N => (c i : ℂ) • reading i)]
    with x hsub ht' hall hsum
  rw [hsub, Pi.sub_apply, ht']
  simp only [candidate, hsum, hall]
  simp [rowError, sensor, turn]

private theorem norm_sq_cells (v : CellSpace) :
    ‖v‖ ^ 2 = ∫ x, ‖v x‖ ^ 2 ∂cellMeasure := by
  apply Complex.ofReal_injective
  calc
    ((‖v‖ ^ 2 : ℝ) : ℂ) = inner ℂ v v := by simp only [Complex.ofReal_pow, inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal]
    _ = ∫ x, ((‖v x‖ ^ 2 : ℝ) : ℂ) ∂cellMeasure := by
      rw [L2.inner_def]
      simp only [inner_self_eq_norm_sq_to_K, Complex.ofReal_pow, RCLike.ofReal_eq_complex_ofReal]
    _ = _ := integral_ofReal

private lemma certificate_bound {N : ℕ} (c : Fin N → ℚ) (M : ℕ) :
    ‖target - candidate c‖ ^ 2 ≤ (certificateValue c M : ℝ) := by
  let v := target - candidate c
  have hsq : (fun x => ‖v x‖ ^ 2) =ᵐ[cellMeasure] fun x => (rowError c ⌊x⁻¹⌋₊ : ℝ)^2 := by
    filter_upwards [residual_ae c] with x hx
    change ‖(target - candidate c) x‖ ^ 2 = _
    rw [hx, Complex.norm_ratCast, sq_abs]
  have hi := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable v)).mp (Lp.memLp v)
  have hb (k : ℕ) : (rowError c k : ℝ)^2 ≤ (envelope c : ℝ)^2 := by
    have h := row_bound c k
    have h2 : (rowError c k)^2 ≤ (envelope c)^2 := by
      rw [← sq_abs (rowError c k)]
      exact pow_le_pow_left₀ (abs_nonneg _) h _
    exact_mod_cast h2
  rw [norm_sq_cells, integral_congr_ae hsq]
  have he := cell_integral_bound (fun k => (rowError c k : ℝ)^2) ((envelope c : ℝ)^2) M
    (hi.congr hsq) hb
  simpa [certificateValue] using he

/-- The sole premise quantifies over integers and finite lists of rational numbers. -/
theorem rh_of_finite_certificates (h : FiniteCertificates) : RiemannHypothesis := by
  apply rh_of_residue_approximation
  change target ∈ closure ((Submodule.span ℂ (Set.range reading)) : Set CellSpace)
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨K, hK⟩ := exists_nat_one_div_lt (sq_pos_of_pos hε)
  obtain ⟨N, M, c, hc⟩ := h K
  refine ⟨candidate c, ?_, ?_⟩
  · apply Submodule.sum_mem
    intro i _
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i.val, rfl⟩)
  · have hr : (certificateValue c M : ℝ) < 1/((K:ℝ)+1) := by
      have hh : (certificateValue c M : ℝ) < ((1/((K:ℚ)+1) : ℚ) : ℝ) := Rat.cast_lt.mpr hc
      simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_add, Rat.cast_natCast] using hh
    have he := (certificate_bound c M).trans_lt (hr.trans hK)
    rw [dist_eq_norm]
    nlinarith [norm_nonneg (target - candidate c)]

#print axioms PALRH.rh_of_finite_certificates

end PALRH
