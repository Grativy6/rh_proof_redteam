import PALRH.Cells
import PALRH.Gain
import PALRH.SquareShell
import PALRH.Dilation
import Mathlib.Analysis.PSeries
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

/-- Squared error over every physical row, indexed here by its zero-based offset. -/
def actualLoss {N : ℕ} (c : Fin N → ℚ) : ℝ :=
  ∑' n : ℕ, rowWeight n * (rowError c (n+1) : ℝ)^2

private lemma loss_summable {N : ℕ} (c : Fin N → ℚ) :
    Summable (fun n : ℕ => rowWeight n * (rowError c (n+1) : ℝ)^2) := by
  apply Summable.of_norm_bounded (g := fun n => rowWeight n * (envelope c : ℝ)^2)
    (rowWeight_hasSum.summable.mul_right _)
  intro n
  have hr : |(rowError c (n+1) : ℝ)| ≤ (envelope c : ℝ) := by
    simpa only [Rat.cast_abs] using (Rat.cast_le (K := ℝ)).mpr (row_bound c (n+1))
  rw [Real.norm_eq_abs, abs_of_nonneg (by apply mul_nonneg; unfold rowWeight; positivity; positivity)]
  apply mul_le_mul_of_nonneg_left _ (by unfold rowWeight; positivity)
  rw [← sq_abs (rowError c (n+1) : ℝ)]
  exact pow_le_pow_left₀ (abs_nonneg _) hr _

/-- Honest compression: every occupied modulus must be readable on the common frame. -/
theorem actualLoss_eq_frame {N : ℕ} (c : Fin N → ℚ) (L : ℕ) [NeZero L]
    (readable : ∀ i : Fin N, c i ≠ 0 → i.val+2 ∣ L) :
    actualLoss c = energy L (fun r => (rowError c (r.val+1) : ℝ)) := by
  rw [energy_eq_all_rows]
  apply tsum_congr
  intro n
  have he : rowError c ((n:ZMod L).val+1) = rowError c (n+1) := by
    rw [ZMod.val_natCast]
    unfold rowError
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : c i = 0
    · simp [h]
    · rw [turn_shift_recover (readable i h)]
  rw [he]

/-- Every strict all-row bound yields a finite rational head and tail witness. -/
theorem finite_head_of_loss {N K : ℕ} (c : Fin N → ℚ)
    (h : actualLoss c < 1/((K:ℝ)+1)) :
    ∃ M : ℕ, certificateValue c M < 1/((K:ℚ)+1) := by
  have htail : Tendsto (fun M : ℕ => (envelope c : ℝ)^2 / ((M:ℝ)+1)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul ((envelope c : ℝ)^2)
  obtain ⟨M,hM⟩ := (htail.eventually_lt_const (sub_pos.mpr h)).exists
  have hsum := (loss_summable c).sum_le_tsum (Finset.range M)
    (fun n _ => mul_nonneg (by unfold rowWeight; positivity) (sq_nonneg _))
  have he : (certificateValue c M : ℝ) < 1/((K:ℝ)+1) := by
    have hh : (∑ n ∈ Finset.range M, (rowError c (n+1) : ℝ)^2 /
        (((n:ℝ)+1)*((n:ℝ)+2))) ≤ actualLoss c := by
      simpa only [actualLoss, rowWeight, one_div, div_eq_mul_inv, one_mul, mul_comm] using hsum
    simp only [certificateValue, Rat.cast_add, Rat.cast_sum, Rat.cast_div, Rat.cast_pow,
      Rat.cast_mul, Rat.cast_natCast, Rat.cast_one, Rat.cast_ofNat]
    linarith
  refine ⟨M, (Rat.cast_lt (K := ℝ)).mp ?_⟩
  simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_add, Rat.cast_natCast] using he

/-- The four selected rows force the original missing-six floor on any finite rational fit. -/
theorem missing_six_loss {N : ℕ} (c : Fin N → ℚ)
    (omits : ∀ i : Fin N, i.val+2 = 6 → c i = 0) : (1:ℝ)/92 ≤ actualLoss c := by
  have zero : (∑ i, c i * fourReadings (turn (i.val+2))) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [fourReadings_turn (by omega)]
    split_ifs with he
    · rw [omits i he, zero_mul]
    · exact mul_zero _
  have row : fourReadings (rowError c) = -1 := by
    calc
      _ = -1 - ∑ i, c i * fourReadings (turn (i.val+2)) := by
        simp only [fourReadings, rowError, mul_add, mul_sub, Finset.sum_sub_distrib,
          Finset.sum_add_distrib, mul_comm (c _) (-2:ℚ), ← mul_assoc, Finset.mul_sum]
        ring
      _ = _ := by rw [zero]; ring
  let a : ℝ := rowError c 1
  let b : ℝ := rowError c 3
  let d : ℝ := rowError c 5
  let e : ℝ := rowError c 6
  have hr : -2*a+b+d-e = -1 := by
    dsimp [a,b,d,e]
    exact_mod_cast row
  have hfour : a^2/2+b^2/12+d^2/30+e^2/42 ≤ actualLoss c := by
    have hs := (loss_summable c).sum_le_tsum ({0,2,4,5} : Finset ℕ)
      (fun n _ => mul_nonneg (by unfold rowWeight; positivity) (sq_nonneg _))
    change _ ≤ actualLoss c at hs
    norm_num [Finset.sum_insert, rowWeight] at hs
    dsimp [a,b,d,e]
    linarith
  have hid : 92*(a^2/2+b^2/12+d^2/30+e^2/42)-(-2*a+b+d-e)^2 =
      (-4*b-12*a)^2/24 + (-4*d-30*a)^2/60 + (-4*e+42*a)^2/84 +
      (12*d-30*b)^2/360 + (12*e+42*b)^2/504 + (30*e+42*d)^2/1260 := by ring
  have hpos : 0 ≤ 92*(a^2/2+b^2/12+d^2/30+e^2/42)-(-2*a+b+d-e)^2 := by
    rw [hid]; positivity
  rw [hr] at hpos
  linarith

/-- The rational tail guard bounds the same loss used in the finite-frame calculus. -/
theorem actualLoss_le_certificate {N : ℕ} (c : Fin N → ℚ) (M : ℕ) :
    actualLoss c ≤ (certificateValue c M : ℝ) := by
  let f := fun n : ℕ => rowWeight n * (rowError c (n+1) : ℝ)^2
  have hf : Summable f := loss_summable c
  have hweight : Summable (fun n : ℕ => rowWeight (n+M)) :=
    (summable_nat_add_iff M).mpr rowWeight_hasSum.summable
  have ht : (∑' i : ℕ, f (i+M)) ≤ (∑' i : ℕ, rowWeight (i+M)*(envelope c : ℝ)^2) := by
    apply ((summable_nat_add_iff M).mpr hf).tsum_le_tsum _ (hweight.mul_right _)
    intro i
    apply mul_le_mul_of_nonneg_left _ (by unfold rowWeight; positivity)
    have hr : |(rowError c (i+M+1) : ℝ)| ≤ (envelope c : ℝ) := by
      simpa only [Rat.cast_abs] using (Rat.cast_le (K := ℝ)).mpr (row_bound c (i+M+1))
    rw [← sq_abs (rowError c (i+M+1) : ℝ)]
    exact pow_le_pow_left₀ (abs_nonneg _) hr _
  rw [tsum_mul_right, rowWeight_tail] at ht
  change (∑' n, f n) ≤ _
  rw [← hf.sum_add_tsum_nat_add M]
  simp only [certificateValue, Rat.cast_add, Rat.cast_sum, Rat.cast_div, Rat.cast_pow,
    Rat.cast_mul, Rat.cast_natCast, Rat.cast_one, Rat.cast_ofNat]
  have head : (∑ n ∈ Finset.range M, f n) =
      ∑ n ∈ Finset.range M, (rowError c (n+1) : ℝ)^2 / (((n:ℝ)+1)*((n:ℝ)+2)) := by
    apply Finset.sum_congr rfl
    intro n _
    dsimp [f, rowWeight]
    ring
  rw [head]
  apply add_le_add (le_refl _)
  simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm] using ht

theorem mirrored_row_errors {N : ℕ} (c : Fin N → ℚ) (k j L : ℕ)
    (cut : k+j+1=L) (readable : ∀ i : Fin N, i.val+2 ∣ L) :
    rowError c k + rowError c j = 1 + rowError c (L-1) := by
  have h0 : L-1+0+1=L := by omega
  have pair (i : Fin N) : turn (i.val+2) k + turn (i.val+2) j = turn (i.val+2) (L-1) := by
    have h1 := half_tick_mirror (by omega : 0 < i.val+2) k j (cut ▸ readable i)
    have h2 := half_tick_mirror (by omega : 0 < i.val+2) (L-1) 0 (h0 ▸ readable i)
    simpa [turn] using h1.trans h2.symm
  have acc : (∑ i, c i * turn (i.val+2) k) + (∑ i, c i * turn (i.val+2) j) =
      ∑ i, c i * turn (i.val+2) (L-1) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← mul_add, pair]
  unfold rowError
  linarith

/-- For any finite remainder fit, fixing all odd answers at the target one forces
every even prediction to zero. A new fit must be allowed to alter old answers. -/
theorem frozen_odd_forces_even {N : ℕ} (c : Fin N → ℚ)
    (fixed : ∀ a : ℕ, rowError c (2*a+1) = 0) (a : ℕ) : rowError c (2*a) = 1 := by
  let M := (N+1).factorial * (a+1)
  have hM : a+1 ≤ M := by
    dsimp [M]
    have h := Nat.factorial_pos (N+1)
    nlinarith
  have hd (i : Fin N) : i.val+2 ∣ 2*M := by
    have h : i.val+2 ∣ (N+1).factorial := Nat.dvd_factorial (by omega) (by omega)
    exact h.trans ((dvd_mul_right _ (a+1)).trans (dvd_mul_left M 2))
  have h := mirrored_row_errors c (2*a) (2*(M-a-1)+1) (2*M) (by omega) hd
  rw [fixed, show 2*M-1 = 2*(M-1)+1 by omega, fixed] at h
  linarith

theorem frozen_odd_loss {N : ℕ} (c : Fin N → ℚ)
    (fixed : ∀ a : ℕ, rowError c (2*a+1) = 0) : (1:ℝ)/6 ≤ actualLoss c := by
  have he := frozen_odd_forces_even c fixed 1
  have h := (loss_summable c).le_tsum 1
    (fun n _ => mul_nonneg (by unfold rowWeight; positivity) (sq_nonneg _))
  change rowWeight 1 * (rowError c 2 : ℝ)^2 ≤ actualLoss c at h
  norm_num at he
  norm_num [he, rowWeight] at h ⊢
  exact h

/-- The missing even response is the difference of two odd residuals at a common reset. -/
theorem second_row_trace {N : ℕ} (c : Fin N → ℚ) {L : ℕ} (hL : 3 ≤ L)
    (readable : ∀ i : Fin N, i.val+2 ∣ L) :
    rowError c (L-3) - rowError c (L-1) = 1 - rowError c 2 := by
  have h := mirrored_row_errors c 2 (L-3) L (by omega) readable
  linarith

/-- Hitting row two obliges every finite fit to spend half a unit on an odd row. -/
theorem odd_displacement {N : ℕ} (c : Fin N → ℚ) (hit : rowError c 2 = 0) :
    ∃ a : ℕ, (1:ℚ)/2 ≤ |rowError c (2*a+1)| := by
  let M := 2*(N+1).factorial
  have hM : 2 ≤ M := by dsimp [M]; have := Nat.factorial_pos (N+1); omega
  have hd (i : Fin N) : i.val+2 ∣ 2*M := by
    have h : i.val+2 ∣ (N+1).factorial := Nat.dvd_factorial (by omega) (by omega)
    exact h.trans ((dvd_mul_left _ 2).trans (dvd_mul_left M 2))
  have h := second_row_trace c (L := 2*M) (by omega) hd
  rw [hit, sub_zero, show 2*M-3=2*(M-2)+1 by omega, show 2*M-1=2*(M-1)+1 by omega] at h
  by_contra! small
  have h₁ := (abs_lt.mp (small (M-2))).2
  have h₂ := (abs_lt.mp (small (M-1))).1
  linarith

/-- A specific rational pair attains the sharp odd displacement at row two. -/
def reopeningPair (i : Fin 2) : ℚ := if i.val = 0 then 1 else 3/2

theorem reopeningPair_attains :
    rowError reopeningPair 2 = 0 ∧ ∀ a : ℕ, |rowError reopeningPair (2*a+1)| ≤ 1/2 := by
  constructor
  · norm_num [rowError, reopeningPair, Fin.sum_univ_two, turn]
  · intro a
    have hodd : (2*a+1)%2 = 1 := by omega
    have h3 := Nat.mod_lt (2*a+1) (by decide : 0 < 3)
    have cases3 : (2*a+1)%3 = 0 ∨ (2*a+1)%3 = 1 ∨ (2*a+1)%3 = 2 := by omega
    rcases cases3 with h | h | h <;>
      norm_num [rowError, reopeningPair, Fin.sum_univ_two, turn, h, hodd]

/-- Productive cadence. While a requested tolerance remains unmet, actual arithmetic
improvements earning at least a fixed positive amount per harmonic unit force a crossing. -/
theorem rh_of_sustained_gain (width : ℕ → ℕ) (fits : (j : ℕ) → Fin (width j) → ℚ)
    (gain : ∀ K : ℕ, ∃ a : ℝ, 0 < a ∧ ∀ j : ℕ,
      1/((K:ℝ)+1) ≤ actualLoss (fits j) →
      actualLoss (fits (j+1)) + a*(1/((j:ℝ)+1)) ≤ actualLoss (fits j)) :
    RiemannHypothesis := by
  apply rh_of_finite_certificates
  intro K
  have hit : ∃ j : ℕ, actualLoss (fits j) < 1/((K:ℝ)+1) := by
    by_contra! stalled
    obtain ⟨a, ha, step⟩ := gain K
    have budget (m : ℕ) : actualLoss (fits m) +
        a * (∑ i ∈ Finset.range m, 1/((i:ℝ)+1)) ≤ actualLoss (fits 0) := by
      induction m with
      | zero => simp
      | succ m ih =>
        rw [Finset.sum_range_succ, mul_add]
        linarith [step m (stalled m)]
    obtain ⟨m, hm⟩ :=
      (Real.tendsto_sum_range_one_div_nat_succ_atTop.eventually_gt_atTop
        (actualLoss (fits 0)/a)).exists
    have ha' := (div_lt_iff₀ ha).mp hm
    have hn : 0 ≤ actualLoss (fits m) :=
      tsum_nonneg fun n => mul_nonneg (by unfold rowWeight; positivity) (sq_nonneg _)
    nlinarith [budget m]
  obtain ⟨j,hj⟩ := hit
  obtain ⟨M,hM⟩ := finite_head_of_loss (fits j) hj
  exact ⟨width j, M, fits j, hM⟩

/-- A first fully finite instance of the same quantity used in the RH implication. -/
theorem first_earned_precision :
    certificateValue reopeningPair 256 < 1/6 := by
  decide +kernel

theorem reopeningPair_whole_loss : actualLoss reopeningPair < 1/6 := by
  apply (actualLoss_le_certificate reopeningPair 256).trans_lt
  have h := (Rat.cast_lt (K := ℝ)).mpr first_earned_precision
  simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h

#print axioms PALRH.odd_displacement
#print axioms PALRH.reopeningPair_whole_loss
#print axioms PALRH.first_earned_precision
#print axioms PALRH.rh_of_sustained_gain

end PALRH
