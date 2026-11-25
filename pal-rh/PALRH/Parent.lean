import PALRH.OneTick
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Topology.Sequences
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Tactic

open Filter Set Metric Complex MeasureTheory
open scoped Topology BigOperators
noncomputable section
namespace PALRH.Parent

/-- Arbitrarily late simultaneous returns in a finite family of phases. -/
theorem phase_returns {ι : Type*} [Fintype ι] (v : ι → ℝ) :
    ∃ T : ℕ → ℕ, Tendsto T atTop atTop ∧ ∀ i,
      Tendsto (fun n => Complex.exp ((T n:ℂ)*((v i:ℂ)*I))) atTop (𝓝 1) := by
  let w := fun i => Circle.exp (v i)
  let u := fun n : ℕ => fun i => (w i)^n
  obtain ⟨a,φ,hφ,hlim⟩ := CompactSpace.tendsto_subseq u
  let T := fun n => φ (n+n)-φ n
  have hlate : Tendsto T atTop atTop := tendsto_atTop_mono
    (fun n => show n ≤ T n by dsimp [T]; have := hφ.add_le_nat n n; omega) tendsto_id
  have hdouble : Tendsto (fun n : ℕ => n+n) atTop atTop :=
    tendsto_atTop_mono (fun n => show n≤n+n by omega) tendsto_id
  refine ⟨T,hlate,?_⟩
  intro i
  have hi : Tendsto (fun n => (w i)^(φ n)) atTop (𝓝 (a i)) := tendsto_pi_nhds.mp hlim i
  have hi2 := hi.comp hdouble
  have hp : Tendsto (fun n => (w i)^(T n)) atTop (𝓝 1) := by
    have h := hi2.mul hi.inv
    have eq (n : ℕ) : (w i)^(T n) = (w i)^(φ (n+n))*((w i)^(φ n))⁻¹ :=
      pow_sub _ (hφ.monotone (by omega))
    simp_rw [eq]
    simpa [Function.comp_def] using h
  have hc := (continuous_subtype_val.tendsto (1:Circle)).comp hp
  change Tendsto (fun n => ((w i ^ T n : Circle):ℂ)) atTop (𝓝 ((1:Circle):ℂ)) at hc
  simpa only [Function.comp_def,Circle.coe_one,Circle.coe_pow,w,Circle.coe_exp,Complex.exp_nat_mul] using hc

private lemma disk_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f) {r b : ℝ} (hr : 0<r) (hb : 0<b)
    (boundary : ∀ z ∈ sphere (1:ℂ) r, b≤‖f z‖) (small : ‖f 1‖<b) :
    ∃ z ∈ closedBall (1:ℂ) r, f z=0 := by
  by_contra! none
  have inv := (hf.diffContOnCl (s:=ball (1:ℂ) r)).inv (fun z hz => none z (by rwa [closure_ball _ hr.ne'] at hz))
  have onBoundary (z : ℂ) (hz : z ∈ frontier (ball (1:ℂ) r)) : ‖f⁻¹ z‖≤b⁻¹ := by
    rw [frontier_ball _ hr.ne'] at hz
    simpa only [Pi.inv_apply,norm_inv] using inv_anti₀ hb (boundary z hz)
  have h := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball inv onBoundary
    (subset_closure (mem_ball_self hr))
  have nonzero := none 1 (mem_closedBall_self hr.le)
  have hx := inv_strictAnti₀ (norm_pos_iff.mpr nonzero) small
  simp only [Pi.inv_apply,norm_inv] at h
  exact (not_lt_of_ge h) hx

def exponentialSum {ι : Type*} [Fintype ι] (a : ι → ℂ) (v : ι → ℝ) (c z : ℂ) : ℂ :=
  c + ∑ i, a i * Complex.exp ((v i:ℂ)*z)

private lemma sum_diff {ι : Type*} [Fintype ι] (a : ι → ℂ) (v : ι → ℝ) (c : ℂ) :
    Differentiable ℂ (exponentialSum a v c) := by
  unfold exponentialSum
  fun_prop

/-- Uniform control of the translated exponential sum on a whole closed disk.
All frequencies share the return times. -/
private theorem disk_returns {ι : Type*} [Fintype ι] (a : ι → ℂ) (v : ι → ℝ) (c : ℂ)
    {T : ℕ → ℕ} (ret : ∀ i, Tendsto (fun n => Complex.exp ((T n:ℂ)*((v i:ℂ)*I))) atTop (𝓝 1))
    {r : ℝ} (hr : 0≤r) :
    ∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧ ∀ n z, z ∈ closedBall (1:ℂ) r →
      ‖exponentialSum a v c (z+(T n:ℂ)*I)-exponentialSum a v c z‖≤e n := by
  classical
  have bounded (i : ι) : ∃ C : ℝ, ∀ z ∈ closedBall (1:ℂ) r, ‖a i*Complex.exp ((v i:ℂ)*z)‖≤C := by
    obtain ⟨z,hz,h⟩ := (isCompact_closedBall (1:ℂ) r).exists_isMaxOn (nonempty_closedBall.mpr hr)
      (f:=fun z => ‖a i*Complex.exp ((v i:ℂ)*z)‖) (by fun_prop)
    exact ⟨_,fun y hy => h hy⟩
  choose C hC using bounded
  let phase := fun n i => Complex.exp ((T n:ℂ)*((v i:ℂ)*I))
  let e := fun n => ∑ i, C i * ‖phase n i-1‖
  have tend (i : ι) : Tendsto (fun n => C i * ‖phase n i-1‖) atTop (𝓝 0) := by
    have h : Tendsto (fun _ : ℕ => (1:ℂ)) atTop (𝓝 1) := tendsto_const_nhds
    simpa [phase] using (((ret i).sub h).norm.const_mul (C i))
  refine ⟨e, by simpa [e] using tendsto_finsetSum Finset.univ (fun i _ => tend i),?_⟩
  intro n z hz
  have term (i : ι) : a i*Complex.exp ((v i:ℂ)*(z+(T n:ℂ)*I))-a i*Complex.exp ((v i:ℂ)*z) =
      (a i*Complex.exp ((v i:ℂ)*z))*(phase n i-1) := by
    simp only [mul_add, Complex.exp_add,phase,mul_comm (v i:ℂ) (T n),←mul_assoc]
    ring_nf
  rw [exponentialSum,exponentialSum,add_sub_add_left_eq_sub,←Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [term i,norm_mul]
  exact mul_le_mul_of_nonneg_right (hC i z hz) (norm_nonneg _)


/-- Every zero of a finite real-frequency exponential sum at one has nonreal
returns at arbitrarily large heights and at real parts arbitrarily close to one. -/
theorem return_zero {ι : Type*} [Fintype ι] (a : ι → ℂ) (v : ι → ℝ) (c : ℂ)
    (origin : exponentialSum a v c 1=0) {η : ℝ} (width : 0<η) (height : ℝ) :
    ∃ s : ℂ, |s.re-1|<η ∧ height<s.im ∧ exponentialSum a v c s=0 := by
  let P := exponentialSum a v c
  have hD : Differentiable ℂ P := sum_diff a v c
  have hA : AnalyticOnNhd ℂ P univ := hD.differentiableOn.analyticOnNhd isOpen_univ
  rcases (hA 1 (mem_univ _)).eventually_eq_zero_or_eventually_ne_zero with nearZero|away
  · have everywhere := hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (mem_univ (1:ℂ)) nearZero
    refine ⟨1+((height+1:ℝ):ℂ)*I,by simpa,?_,everywhere (mem_univ _)⟩
    simp
  · obtain ⟨δ,hδ,near⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp away)
    let r := min δ η / 2
    have hr : 0<r := by dsimp [r]; positivity
    have hrδ : r<δ := by dsimp [r]; linarith [min_le_left δ η]
    have hrη : r<η := by dsimp [r]; linarith [min_le_right δ η]
    have no (z : ℂ) (hz : z ∈ sphere (1:ℂ) r) : P z≠0 := by
      have dist := Metric.mem_sphere.mp hz
      apply near (lt_of_eq_of_lt dist hrδ)
      intro eq
      have z1 : z=1 := eq
      simp [z1] at dist
      linarith
    have point : (sphere (1:ℂ) r).Nonempty := by
      refine ⟨1+(r:ℂ),?_⟩
      simp [Real.norm_eq_abs,abs_of_nonneg hr.le]
    obtain ⟨w,hw,least⟩ := (isCompact_sphere (1:ℂ) r).exists_isMinOn point hD.continuous.norm.continuousOn
    let b := ‖P w‖/2
    have hb : 0<b := half_pos (norm_pos_iff.mpr (no w hw))
    obtain ⟨T,hT,returns⟩ := phase_returns v
    obtain ⟨err,herr,bound⟩ := disk_returns a v c returns hr.le
    have small := herr.eventually_lt_const hb
    have large : ∀ᶠ n : ℕ in atTop, height+r < (T n:ℝ) :=
      (tendsto_natCast_atTop_atTop.comp hT).eventually_gt_atTop _
    obtain ⟨n,he,ht⟩ := (small.and large).exists
    let g := fun z : ℂ => P (z+(T n:ℂ)*I)
    have gd : Differentiable ℂ g := hD.comp (differentiable_id.add_const _)
    have bound' (z : ℂ) (hz : z ∈ closedBall (1:ℂ) r) : ‖g z-P z‖≤err n := bound n z hz
    have ct := bound' 1 (mem_closedBall_self hr.le)
    have hzero : P 1=0 := origin
    rw [hzero,sub_zero] at ct
    obtain ⟨z,hz,hgz⟩ := disk_zero gd hr hb (fun y hy => by
      have le := bound' y (sphere_subset_closedBall hy)
      have comp := norm_sub_norm_le (P y) (g y)
      rw [norm_sub_rev] at comp
      have low : ‖P w‖≤‖P y‖ := least hy
      dsimp [b] at he ⊢
      linarith) (ct.trans_lt he)
    have dist := mem_closedBall_iff_norm.mp hz
    have re : |z.re-1|≤r := by simpa using (Complex.abs_re_le_norm (z-1)).trans dist
    have im : |z.im|≤r := by simpa using (Complex.abs_im_le_norm (z-1)).trans dist
    refine ⟨z+(T n:ℂ)*I,by simpa using re.trans_lt hrη,?_,hgz⟩
    simp only [Complex.add_im,Complex.mul_im,Complex.natCast_re,Complex.I_im,mul_one,
      Complex.natCast_im,Complex.I_re,zero_mul,add_zero]
    linarith [(abs_le.mp im).1]

#print axioms PALRH.Parent.return_zero


private def modulus {N : ℕ} (i : Fin N) : ℕ := i.val+2
private lemma modulus_pos {N : ℕ} (i : Fin N) : 0<modulus i := by dsimp [modulus]; omega

/-- The exact finite factor contributed by the chosen (possibly complex) parent coefficients. -/
def factor {N : ℕ} (c : Fin N → ℂ) (s : ℂ) : ℂ :=
  ∑ i, c i*(((modulus i:ℕ):ℂ)⁻¹-((modulus i:ℕ):ℂ)^(-s))

theorem factor_returns {N : ℕ} (c : Fin N → ℂ) {η : ℝ} (width : 0<η) (height : ℝ) :
    ∃ s : ℂ, |s.re-1|<η ∧ height<s.im ∧ factor c s=0 := by
  let v := fun i : Fin N => -Real.log (modulus i)
  let a := fun i => -c i
  let A := ∑ i, c i*((modulus i:ℕ):ℂ)⁻¹
  have same (z : ℂ) : exponentialSum a v A z=factor c z := by
    unfold exponentialSum factor
    dsimp only [A,a,v]
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (modulus_pos i).ne')]
    simp only [Complex.ofReal_neg,Complex.natCast_log,neg_mul,mul_neg]
    ring
  have atOne : exponentialSum a v A 1=0 := by
    rw [same]
    simp [factor,Complex.cpow_neg_one]
  simpa only [same] using return_zero a v A atOne width height

/-- Daughter number m uses the physical scale m+1, including the undilated parent at m=0. -/
def daughter {N : ℕ} (c : Fin N → ℂ) (m : ℕ) : CellSpace :=
  ∑ i, c i • (cellSensor ((m+1)*modulus i) (Nat.mul_pos (Nat.succ_pos _) (modulus_pos _)) -
    ((modulus i:ℕ):ℂ)⁻¹ • cellSensor (m+1) (Nat.succ_pos _))

/-- On actual rows the daughter uses the original parent's quotient clock. -/
theorem daughter_rows {N : ℕ} (c : Fin N → ℂ) (m k : ℕ) :
    (∑ i, c i*((turn ((m+1)*modulus i) k:ℂ)-((modulus i:ℕ):ℂ)⁻¹*(turn (m+1) k:ℂ))) =
    ∑ i, c i*(turn (modulus i) (k/(m+1)):ℂ) := by
  apply Finset.sum_congr rfl
  intro i _
  rw [quotient_signal (Nat.succ_pos _) (modulus_pos _)]
  push_cast
  ring

theorem daughter_moment {N : ℕ} (c : Fin N → ℂ) (m : ℕ) {s : ℂ} (hs : 1/2<s.re) (h1 : s≠1) :
    s*cellMoment hs (daughter c m)=((m+1:ℕ):ℂ)^(-s)*factor c s*riemannZeta s := by
  let p := m+1
  have hp : 0<p := Nat.succ_pos _
  unfold daughter factor
  simp only [map_sum,map_smul,map_sub,smul_eq_mul,Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  let d := modulus i
  have hd : 0<d := modulus_pos i
  change s*(c i*(cellMoment hs (cellSensor (p*d) _) -
    (d:ℂ)⁻¹*cellMoment hs (cellSensor p _))) = _
  rw [show s*(c i*(cellMoment hs (cellSensor (p*d) _) -
    (d:ℂ)⁻¹*cellMoment hs (cellSensor p _))) =
      c i*(s*cellMoment hs (cellSensor (p*d) _) - (d:ℂ)⁻¹*(s*cellMoment hs (cellSensor p _))) by ring,
    moment_sensor hs h1 (Nat.mul_pos hp hd),moment_sensor hs h1 hp]
  simp only [Nat.cast_mul,Complex.natCast_mul_natCast_cpow,mul_inv_rev]
  dsimp only [p,d]
  ring

/-- Neither physical target is in the closed span of arbitrarily many, arbitrarily
refitted scaled copies of any fixed finite parent. -/
theorem single_parent_misses {N : ℕ} (c : Fin N → ℂ) :
    cellConstant ∉ (Submodule.span ℂ (Set.range (daughter c))).topologicalClosure ∧
    cellFirst ∉ (Submodule.span ℂ (Set.range (daughter c))).topologicalClosure := by
  obtain ⟨s,close,up,hf⟩ := factor_returns c (by norm_num : (0:ℝ)<1/4) 1
  have hs : 1/2<s.re := by have := (abs_lt.mp close).1; linarith
  have h1 : s≠1 := by intro eq; simp [eq] at up; linarith
  let T := cellMoment hs
  have hspan : Submodule.span ℂ (Set.range (daughter c)) ≤ T.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨m,rfl⟩
    change cellMoment hs (daughter c m)=0
    have h := daughter_moment c m hs h1
    rw [hf,mul_zero,zero_mul] at h
    exact (mul_eq_zero.mp h).resolve_left (ne_zero_of_re_pos (by linarith))
  have closed := (Submodule.span ℂ (Set.range (daughter c))).topologicalClosure_minimal hspan T.isClosed_ker
  constructor
  · intro yes
    have h : cellMoment hs cellConstant=0 := closed yes
    rw [moment_constant hs] at h
    exact (one_div_ne_zero (ne_zero_of_re_pos (by linarith : 0<s.re))) h
  · intro yes
    exact moment_first_ne hs (closed yes)

#print axioms PALRH.Parent.single_parent_misses


private theorem sensor_rows (d : ℕ) (hd : 0<d) :
    ⇑(cellSensor d hd) =ᵐ[cellMeasure] fun x => (turn d ⌊x⁻¹⌋₊:ℂ) := by
  have h : ⇑(cellSensor d hd) =ᵐ[cellMeasure] sensor d := MemLp.coeFn_toLp _
  filter_upwards [h] with x hx
  simp [hx,sensor,turn]

theorem daughter_ae {N : ℕ} (c : Fin N → ℂ) (m : ℕ) :
    ⇑(daughter c m) =ᵐ[cellMeasure] fun x => ∑ i, c i*(turn (modulus i) (⌊x⁻¹⌋₊/(m+1)):ℂ) := by
  let p := m+1
  let read := fun i : Fin N => cellSensor (p*modulus i) (Nat.mul_pos (Nat.succ_pos _) (modulus_pos _))
  let slow := cellSensor p (Nat.succ_pos _)
  let delta := fun i : Fin N => read i - ((modulus i:ℕ):ℂ)⁻¹ • slow
  have coord (i : Fin N) : ⇑(c i • delta i) =ᵐ[cellMeasure] fun x =>
      c i*((turn (p*modulus i) ⌊x⁻¹⌋₊:ℂ)-((modulus i:ℕ):ℂ)⁻¹*(turn p ⌊x⁻¹⌋₊:ℂ)) := by
    have ha := sensor_rows (p*modulus i) (Nat.mul_pos (Nat.succ_pos _) (modulus_pos _))
    have hb := sensor_rows p (Nat.succ_pos _)
    filter_upwards [Lp.coeFn_smul (c i) (delta i),Lp.coeFn_sub (read i) (((modulus i:ℕ):ℂ)⁻¹ • slow),
      Lp.coeFn_smul ((modulus i:ℕ):ℂ)⁻¹ slow,ha,hb] with x sm sub sc a b
    change read i x=_ at a
    change slow x=_ at b
    change delta i x=_ at sub
    simp only [sm,Pi.smul_apply,smul_eq_mul,sub,Pi.sub_apply,sc,a,b]
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun i : Fin N => c i • delta i),
    ae_all_iff.mpr coord] with x felt fibers
  change (∑ i, c i • delta i) x = _
  rw [felt]
  simp only [fibers]
  exact daughter_rows c m _

theorem single_parent_gap {N : ℕ} (c : Fin N → ℂ) :
    ∃ ε : ℝ, 0<ε ∧ ∀ g ∈ Submodule.span ℂ (Set.range (daughter c)),
      ε≤‖cellConstant-g‖ ∧ ε≤‖cellFirst-g‖ := by
  let S := Submodule.span ℂ (Set.range (daughter c))
  obtain ⟨hc,ht⟩ := single_parent_misses c
  change cellConstant ∉ closure (S:Set CellSpace) at hc
  change cellFirst ∉ closure (S:Set CellSpace) at ht
  rw [Metric.mem_closure_iff] at hc ht
  push Not at hc ht
  obtain ⟨a,ha,head⟩ := hc
  obtain ⟨b,hb,tail⟩ := ht
  refine ⟨min a b,lt_min ha hb,fun g hg => ?_⟩
  exact ⟨by simpa [dist_eq_norm] using (min_le_left a b).trans (head g hg),
    by simpa [dist_eq_norm] using (min_le_right a b).trans (tail g hg)⟩

private lemma independent_logs {n m : ℤ}
    (mark : (n:ℝ)*Real.log 3=(m:ℝ)*Real.log 2) : n=0 ∧ m=0 := by
  have l3 : 0<Real.log 3 := Real.log_pos (by norm_num)
  have l2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have mag : (n.natAbs:ℝ)*Real.log 3=(m.natAbs:ℝ)*Real.log 2 := by
    simpa only [abs_mul,abs_of_pos l3,abs_of_pos l2,Nat.cast_natAbs,Int.cast_abs] using congrArg abs mark
  have logs : Real.log ((3:ℝ)^n.natAbs)=Real.log ((2:ℝ)^m.natAbs) := by
    simpa only [Real.log_pow] using mag
  have vals := congrArg Real.exp logs
  rw [Real.exp_log (by positivity),Real.exp_log (by positivity)] at vals
  have eq : 3^n.natAbs=2^m.natAbs := by exact_mod_cast vals
  have cp : (3^n.natAbs).Coprime (2^m.natAbs) := ((by decide : Nat.Coprime 3 2).pow_left _).pow_right _
  rw [eq,Nat.coprime_self] at cp
  have hmn : m.natAbs=0 := by
    by_contra h
    have big := Nat.one_lt_pow (n:=m.natAbs) h (by decide : 1<2)
    omega
  have hm : m=0 := Int.natAbs_eq_zero.mp hmn
  rw [hm,Int.cast_zero,zero_mul] at mark
  have hn := (mul_eq_zero.mp mark).resolve_right l3.ne'
  exact ⟨by exact_mod_cast hn,hm⟩

private lemma phase_mark {d : ℕ} (hd : 0<d) {s : ℂ}
    (zero : (d:ℂ)⁻¹-(d:ℂ)^(-s)=0) :
    ∃ n : ℤ, (Real.log d:ℂ)*(1-s)=(n:ℂ)*(2*Real.pi*I) := by
  have nz : (d:ℂ)≠0 := by exact_mod_cast hd.ne'
  apply Complex.exp_eq_one_iff.mp
  rw [Complex.natCast_log,←Complex.cpow_def_of_ne_zero nz,sub_eq_add_neg,
    Complex.cpow_add _ _ nz,Complex.cpow_one,←sub_eq_zero.mp zero]
  exact mul_inv_cancel₀ nz

/-- The independent 2 and 3 factors have no shared nonreal return. -/
theorem two_three_factor {s : ℂ} (h2 : (2:ℂ)⁻¹-(2:ℂ)^(-s)=0)
    (h3 : (3:ℂ)⁻¹-(3:ℂ)^(-s)=0) : s=1 := by
  obtain ⟨n,hn⟩ := phase_mark (d:=2) (by decide) (by exact_mod_cast h2)
  obtain ⟨m,hm⟩ := phase_mark (d:=3) (by decide) (by exact_mod_cast h3)
  have nz : (2*(Real.pi:ℂ)*I)≠0 := mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) I_ne_zero
  have eq : (n:ℝ)*Real.log 3=(m:ℝ)*Real.log 2 := by
    apply Complex.ofReal_injective
    apply mul_right_cancel₀ nz
    push_cast
    push_cast at hn hm
    linear_combination (Real.log 2:ℂ)*hm - (Real.log 3:ℂ)*hn
  have zero := (independent_logs eq).1
  rw [zero,Int.cast_zero,zero_mul] at hn
  have ln : (Real.log (2:ℕ):ℂ)≠0 := by exact_mod_cast (Real.log_pos (by norm_num : (1:ℝ)<2)).ne'
  exact (sub_eq_zero.mp ((mul_eq_zero.mp hn).resolve_left ln)).symm

/-- Away from the zeta pole, common blind Mellin waves for the two separately
adjustable parents coincide exactly with the zeta zeros in the relevant half-plane. -/
theorem independent_waves {s : ℂ} (hs : 1/2<s.re) (h1 : s≠1) :
    (cellMoment hs (cellSensor 2 (by decide))=0 ∧ cellMoment hs (cellSensor 3 (by decide))=0) ↔
      riemannZeta s=0 := by
  have a := moment_sensor hs h1 (by decide : 0<2)
  have b := moment_sensor hs h1 (by decide : 0<3)
  norm_num only [Nat.cast_ofNat] at a b
  have nz : s≠0 := ne_zero_of_re_pos (by linarith)
  constructor
  · rintro ⟨p,q⟩
    rw [p,mul_zero] at a
    rw [q,mul_zero] at b
    by_contra hz
    exact h1 (two_three_factor (by simpa only [one_div] using (mul_eq_zero.mp a.symm).resolve_right hz)
      (by simpa only [one_div] using (mul_eq_zero.mp b.symm).resolve_right hz))
  · intro hz
    rw [hz,mul_zero] at a b
    exact ⟨(mul_eq_zero.mp a).resolve_left nz,(mul_eq_zero.mp b).resolve_left nz⟩

#print axioms PALRH.Parent.daughter_ae
#print axioms PALRH.Parent.single_parent_gap
#print axioms PALRH.Parent.independent_waves

end PALRH.Parent
