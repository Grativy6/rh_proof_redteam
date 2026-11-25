import PALRH
import PALRH.Dilation
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

open Finset Filter Set
open scoped Topology BigOperators

noncomputable section
namespace PALRH.OneTick

/-- The admissible operations are rational linear combinations of the existing turns. -/
def fits : Submodule ℚ (ℕ → ℚ) :=
  Submodule.span ℚ (Set.range fun n : ℕ => turn (n+2))

def tick (k : ℕ) : ℚ := if k=1 then 1 else 0
def occupied (k : ℕ) : ℚ := if k=0 then 0 else 1
def dilate (p : ℕ) (f : ℕ → ℚ) (k : ℕ) : ℚ := f (k/p)

theorem turn_mem {d : ℕ} (hd : 2 ≤ d) : turn d ∈ fits := by
  apply Submodule.subset_span
  refine ⟨d-2, ?_⟩
  change turn (d-2+2) = turn d
  rw [Nat.sub_add_cancel hd]

theorem dilate_mem {p : ℕ} (hp : 2 ≤ p) {f : ℕ → ℚ} (hf : f ∈ fits) :
    dilate p f ∈ fits := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a,rfl⟩ := hx
    have eq : dilate p (turn (a+2)) =
        turn (p*(a+2)) - ((a+2 : ℕ) : ℚ)⁻¹ • turn p := by
      funext k
      simpa [dilate, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
        using quotient_signal (by omega : 0<p) (by omega : 0<a+2) k
    rw [eq]
    exact fits.sub_mem (turn_mem (by nlinarith)) (fits.smul_mem _ (turn_mem hp))
  | zero => exact fits.zero_mem
  | add x y _ _ hx hy => exact fits.add_mem hx hy
  | smul a x _ hx => exact fits.smul_mem a hx

/-- Convert a span witness back to the finite coefficient array the public RH bridge consumes. -/
theorem as_array {f : ℕ → ℚ} (hf : f ∈ fits) :
    ∃ N : ℕ, ∃ c : Fin N → ℚ, ∀ k, f k = 1-rowError c k := by
  obtain ⟨v,hs⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hf
  let N := v.support.sup id + 1
  have hsub : v.support ⊆ Finset.range N := by
    intro i hi
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hi))
  refine ⟨N,fun i => v i.val,?_⟩
  intro k
  rw [← hs, v.sum_of_support_subset hsub (fun i a => a • turn (i+2))
    (by intro i _; exact zero_smul _ _), Finset.sum_apply, rowError]
  simp only [Pi.smul_apply, smul_eq_mul, sub_sub_cancel]
  exact (Fin.sum_univ_eq_sum_range (fun i => v i * turn (i+2) k) N).symm

def bounded (f : ℕ → ℚ) : Prop := ∃ C : ℝ, ∀ k, ‖(f k : ℝ)‖ ≤ C

private lemma bounded_sub {f g : ℕ → ℚ} (hf : bounded f) (hg : bounded g) :
    bounded (f-g) := by
  obtain ⟨C,hC⟩ := hf
  obtain ⟨D,hD⟩ := hg
  exact ⟨C+D,fun k => by simpa only [Pi.sub_apply, Rat.cast_sub] using
    (norm_sub_le (f k : ℝ) (g k : ℝ)).trans (add_le_add (hC k) (hD k))⟩

theorem fit_properties {f : ℕ → ℚ} (hf : f ∈ fits) : f 0 = 0 ∧ bounded f := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨n,rfl⟩ := hx
    refine ⟨by simp [turn],1,?_⟩
    intro k
    simp only [turn, Rat.cast_div, Rat.cast_natCast, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (↑(k%(n+2)):ℝ)/↑(n+2:ℕ))]
    apply (div_le_one (by positivity)).mpr
    exact_mod_cast (Nat.mod_lt k (by omega : 0<n+2)).le
  | zero => exact ⟨rfl,0,fun k => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨hx0,C,hC⟩ := hx
    obtain ⟨hy0,D,hD⟩ := hy
    refine ⟨by simp [hx0,hy0],C+D,fun k => ?_⟩
    simpa only [Pi.add_apply,Rat.cast_add] using (norm_add_le (x k:ℝ) (y k:ℝ)).trans
      (add_le_add (hC k) (hD k))
  | smul a x _ hx =>
    obtain ⟨hx0,C,hC⟩ := hx
    refine ⟨by simp [hx0],‖(a:ℝ)‖*C,fun k => ?_⟩
    simpa only [Pi.smul_apply,smul_eq_mul,Rat.cast_mul,norm_mul] using
      mul_le_mul_of_nonneg_left (hC k) (norm_nonneg (a:ℝ))

private lemma tick_bounded : bounded tick := ⟨1,fun k => by
  by_cases h : k=1 <;> simp [tick,h]⟩
private lemma occupied_bounded : bounded occupied := ⟨1,fun k => by
  by_cases h : k=0 <;> simp [occupied,h]⟩

theorem occupied_step (k : ℕ) : occupied k = tick k + occupied (k/2) := by
  unfold occupied tick
  split_ifs <;> norm_num <;> omega

def cost (e : ℕ → ℚ) : ℝ := ∑' n : ℕ, rowWeight n * (e (n+1) : ℝ)^2
def loss (target f : ℕ → ℚ) : ℝ := cost (target-f)

private theorem weighted_summable {f : ℕ → ℚ} (hf : bounded f) (addr : ℕ → ℕ) :
    Summable (fun n : ℕ => rowWeight n * (f (addr n) : ℝ)^2) := by
  obtain ⟨C,hC⟩ := hf
  apply Summable.of_norm_bounded (g := fun n => rowWeight n*C^2) (rowWeight_hasSum.summable.mul_right _)
  intro n
  have hw : 0 ≤ rowWeight n := by unfold rowWeight; positivity
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hw (sq_nonneg _)), ←sq_abs (f _ : ℝ)]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) (hC _) _) hw

theorem loss_triangle (x y z : ℕ → ℚ) (hx : bounded x) (hy : bounded y) (hz : bounded z) :
    loss x z ≤ 2*loss x y+2*loss y z := by
  let addr := fun n : ℕ => n+1
  have a := weighted_summable (bounded_sub hx hy) addr
  have b := weighted_summable (bounded_sub hy hz) addr
  have c := weighted_summable (bounded_sub hx hz) addr
  have term (n : ℕ) : rowWeight n * ((x-z) (addr n) : ℝ)^2 ≤
      2*(rowWeight n *((x-y) (addr n) : ℝ)^2)+2*(rowWeight n *((y-z) (addr n) : ℝ)^2) := by
    simp only [Pi.sub_apply, Rat.cast_sub]
    have hw : 0 ≤ rowWeight n := by unfold rowWeight; positivity
    nlinarith [mul_nonneg hw (sq_nonneg ((x (addr n):ℝ)-2*(y (addr n):ℝ)+(z (addr n):ℝ)))]
  have h := c.tsum_le_tsum term ((a.mul_left 2).add (b.mul_left 2))
  rw [(a.mul_left 2).tsum_add (b.mul_left 2),a.tsum_mul_left,b.tsum_mul_left] at h
  exact h

theorem fit_row_lower {f : ℕ → ℚ} (hf : f ∈ fits) (n : ℕ) :
    rowWeight n * ((1 - f (n+1) : ℚ) : ℝ)^2 ≤ loss occupied f := by
  have h := (weighted_summable (bounded_sub occupied_bounded (fit_properties hf).2)
    (fun k => k+1)).le_tsum n
    (fun k _ => mul_nonneg (by unfold rowWeight; positivity) (sq_nonneg _))
  change rowWeight n * ((occupied (n+1) - f (n+1):ℚ):ℝ)^2 ≤ loss occupied f at h
  simpa only [occupied, Nat.succ_ne_zero, if_false] using h

private lemma zero_bounded : bounded 0 := ⟨0,fun k => by simp⟩

private lemma bounded_add {f g : ℕ → ℚ} (hf : bounded f) (hg : bounded g) :
    bounded (f+g) := by
  obtain ⟨C,hC⟩ := hf
  obtain ⟨D,hD⟩ := hg
  exact ⟨C+D,fun k => by simpa only [Pi.add_apply, Rat.cast_add] using
    (norm_add_le (f k : ℝ) (g k : ℝ)).trans (add_le_add (hC k) (hD k))⟩

private lemma bounded_dilate {v : ℕ → ℚ} (hv : bounded v) (d : ℕ) : bounded (dilate d v) := by
  obtain ⟨C,hC⟩ := hv
  exact ⟨C, fun k => hC (k/d)⟩

private theorem cost_nonneg (f : ℕ → ℚ) : 0 ≤ cost f :=
  tsum_nonneg fun n => mul_nonneg (by unfold rowWeight; positivity) (sq_nonneg _)

/-- One copied half-scale error costs enough less to give a genuine contraction. -/
private theorem cost_step {u v : ℕ → ℚ} (hu : bounded u) (hv : bounded v) (hv0 : v 0 = 0) :
    cost (u+dilate 2 v) ≤ 3*cost u+(3/4)*cost v := by
  have hsu := weighted_summable hu (fun n => n+1)
  have hsv := weighted_summable hv (fun n => (n+1)/2)
  have hss := weighted_summable (bounded_add hu (bounded_dilate hv 2)) (fun n => n+1)
  have term (n : ℕ) :
      rowWeight n * ((u+dilate 2 v) (n+1) : ℝ)^2 ≤
        3*(rowWeight n*(u (n+1):ℝ)^2) + (3/2)*(rowWeight n*(v ((n+1)/2):ℝ)^2) := by
    simp only [Pi.add_apply, dilate, Rat.cast_add]
    have hw : 0 ≤ rowWeight n := by unfold rowWeight; positivity
    nlinarith [mul_nonneg hw (sq_nonneg (2*(u (n+1):ℝ) - (v ((n+1)/2) : ℝ)))]
  have hsc := hss.tsum_le_tsum term ((hsu.mul_left 3).add (hsv.mul_left (3/2)))
  rw [(hsu.mul_left 3).tsum_add (hsv.mul_left (3/2)), hsu.tsum_mul_left, hsv.tsum_mul_left] at hsc
  obtain ⟨C,hC⟩ := hv
  have scaled := dilated_all_rows (by decide : 0 < 2) (fun k => (v k : ℝ)^2)
    (by simp [hv0]) (C := C^2) (fun k => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ←sq_abs (v k : ℝ)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hC k) _)
  change _ ≤ 3*cost u+(3/2)*_ at hsc
  rw [scaled] at hsc
  change cost (u+dilate 2 v) ≤ 3*cost u+(3/2)*(cost v/(2:ℝ)) at hsc
  linarith

private def extendFit (g : ℕ → ℚ) : ℕ → ℕ → ℚ
  | 0 => 0
  | j+1 => g + dilate 2 (extendFit g j)

private theorem extend_mem {g : ℕ → ℚ} (hg : g ∈ fits) (j : ℕ) : extendFit g j ∈ fits := by
  induction j with
  | zero => exact fits.zero_mem
  | succ j ih => exact fits.add_mem hg (dilate_mem (by decide : 2≤2) ih)

/-- Explicit finite assembly. A single pulse approximation can be copied to every dyadic band. -/
theorem extend_loss {g : ℕ → ℚ} (hg : g ∈ fits) (j : ℕ) :
    loss occupied (extendFit g j) ≤ 12*loss tick g + (3/4 : ℝ)^j := by
  induction j with
  | zero =>
    have hzero : loss occupied (extendFit g 0) = 1 := by
      simpa [loss, cost, occupied, extendFit] using rowWeight_hasSum.tsum_eq
    rw [hzero,pow_zero]
    have nonneg : 0 ≤ loss tick g := cost_nonneg _
    linarith
  | succ j ih =>
    let f := extendFit g j
    have hf := fit_properties (extend_mem hg j)
    have ident : occupied - extendFit g (j+1) = (tick-g) + dilate 2 (occupied-f) := by
      funext k
      change occupied k - (g k + f (k/2)) = tick k - g k + (occupied (k/2) - f (k/2))
      rw [occupied_step k]; ring
    have ht := cost_step (bounded_sub tick_bounded (fit_properties hg).2)
      (bounded_sub occupied_bounded hf.2) (by simp [occupied, hf.1])
    change loss occupied (extendFit g (j+1)) ≤ _
    rw [loss, ident, pow_succ]
    change _ ≤ 3*loss tick g + (3/4)*loss occupied (extendFit g j) at ht
    change _ ≤ 12*loss tick g + (3/4 : ℝ)^j * (3/4)
    linarith

/-- The only object to isolate is the first positive row. -/
def Approximable : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ g ∈ fits, loss tick g < ε

/-- Turn a first-tick witness at any tolerance into a finite rational certificate for one. -/
theorem certificates_of_first_tick (can : Approximable) : FiniteCertificates := by
  intro K
  let τ := 1/((K:ℝ)+1)
  have ht : 0<τ := by dsimp [τ]; positivity
  obtain ⟨g,hg,herr⟩ := can (τ/24) (by positivity)
  have hdecay := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤3/4)
    (by norm_num : (3/4:ℝ)<1)
  obtain ⟨j,hj⟩ := (hdecay.eventually_lt_const (half_pos ht)).exists
  have bound := extend_loss hg j
  obtain ⟨N,c,hc⟩ := as_array (extend_mem hg j)
  have eq : actualLoss c = loss occupied (extendFit g j) := by
    unfold actualLoss loss cost
    apply tsum_congr
    intro n
    simp [occupied, hc (n+1)]
  obtain ⟨M,hM⟩ := finite_head_of_loss (K := K) c (by rw [eq]; change _ < τ; linarith)
  exact ⟨N,M,c,hM⟩

/-- The reverse construction subtracts the same fit opened on the doubled clock. -/
theorem first_tick_of_certificates (certificates : FiniteCertificates) : Approximable := by
  intro ε hε
  obtain ⟨K,hK⟩ := exists_nat_one_div_lt (show 0 < ε/4 by positivity)
  obtain ⟨N,M,c,hc⟩ := certificates K
  let f : ℕ → ℚ := ∑ i, c i • turn (i.val+2)
  have hf : f ∈ fits := by
    apply Submodule.sum_mem
    intro i _
    exact fits.smul_mem _ (turn_mem (by omega))
  have eq : actualLoss c = loss occupied f := by
    unfold actualLoss loss cost
    apply tsum_congr
    intro n
    simp [occupied,f,rowError,Finset.sum_apply]
  have hsmall : loss occupied f < ε/4 := by
    rw [←eq]
    have hcast : (certificateValue c M : ℝ) < 1/((K:ℝ)+1) := by
      simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_add,Rat.cast_natCast] using
        (Rat.cast_lt (K := ℝ)).mpr hc
    exact (actualLoss_le_certificate c M).trans_lt (hcast.trans hK)
  let r := occupied - f
  have hb : bounded r := bounded_sub occupied_bounded (fit_properties hf).2
  have hnb : bounded (-r) := by simpa only [zero_sub] using bounded_sub zero_bounded hb
  have h0 : (-r) 0 = 0 := by simp [r,occupied,(fit_properties hf).1]
  have heq : tick - (f - dilate 2 f) = r + dilate 2 (-r) := by
    funext k
    change tick k - (f k - f (k/2)) = (occupied k - f k) + -(occupied (k/2) - f (k/2))
    rw [occupied_step k]; ring
  have hneg : cost (-r) = cost r := by
    unfold cost
    apply tsum_congr
    intro n
    simp
  refine ⟨f-dilate 2 f, fits.sub_mem hf (dilate_mem (by decide) hf), ?_⟩
  rw [loss,heq]
  have hcost := cost_step hb hnb h0
  rw [hneg] at hcost
  change cost r < ε/4 at hsmall
  linarith

theorem first_tick_iff_certificates : Approximable ↔ FiniteCertificates :=
  ⟨certificates_of_first_tick, first_tick_of_certificates⟩

/-- A rational, admissible localization of the very first tick implies the fixed RH target. -/
theorem rh_of_first_tick (can : Approximable) : RiemannHypothesis :=
  rh_of_finite_certificates (certificates_of_first_tick can)

def fourth (f : ℕ → ℚ) : ℚ := -f 1 + f 2 + f 3 - f 4

theorem fourth_turn {d : ℕ} (hd : 2≤d) :
    fourth (turn d) = if d=4 then 1 else 0 := by
  by_cases h : d≤4
  · interval_cases d <;> norm_num [fourth,turn]
  · simp only [fourth,turn,Nat.mod_eq_of_lt (by omega : 1<d),Nat.mod_eq_of_lt (by omega : 2<d),
      Nat.mod_eq_of_lt (by omega : 3<d),Nat.mod_eq_of_lt (by omega : 4<d),if_neg (by omega : d≠4)]
    push_cast
    ring

theorem omit_four_blind {f : ℕ → ℚ}
    (hf : f ∈ Submodule.span ℚ (Set.range fun i : {d : ℕ // 2≤d ∧ d≠4} => turn i.val)) :
    fourth f = 0 := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a,rfl⟩ := hx
    rw [fourth_turn a.property.1, if_neg a.property.2]
  | zero => simp [fourth]
  | add x y _ _ hx hy => unfold fourth at *; simp only [Pi.add_apply]; linarith
  | smul a x _ hx =>
    unfold fourth at *
    simp only [Pi.smul_apply,smul_eq_mul]
    linear_combination a * hx

theorem blind_tick_floor {f : ℕ → ℚ} (hf : f ∈ fits) (blind : fourth f=0) :
    (1:ℝ)/40 ≤ loss tick f := by
  let r := tick-f
  have h : fourth r = -1 := by
    unfold fourth at blind ⊢
    simp [r,tick]
    linarith
  let a : ℝ := r 1
  let b : ℝ := r 2
  let c : ℝ := r 3
  let d : ℝ := r 4
  have hr : -a+b+c-d = -1 := by dsimp [a,b,c,d]; exact_mod_cast h
  have hs := (weighted_summable (bounded_sub tick_bounded (fit_properties hf).2)
      (fun n => n+1)).sum_le_tsum ({0,1,2,3} : Finset ℕ)
    (fun n _ => mul_nonneg (by unfold rowWeight; positivity) (sq_nonneg _))
  change _ ≤ loss tick f at hs
  have hsubset : a^2/2+b^2/6+c^2/12+d^2/20 ≤ loss tick f := by
    change (∑ i ∈ ({0,1,2,3} : Finset ℕ), rowWeight i*(r (i+1):ℝ)^2) ≤ _ at hs
    norm_num [Finset.sum_insert,rowWeight] at hs
    dsimp [a,b,c,d]
    linarith
  have hid : 40*(a^2/2+b^2/6+c^2/12+d^2/20)-(-a+b+c-d)^2 =
      (-2*b-6*a)^2/12 + (-2*c-12*a)^2/24 + (-2*d+20*a)^2/40 +
      (6*c-12*b)^2/72 + (6*d+20*b)^2/120 + (12*d+20*c)^2/240 := by ring
  have hpos : 0 ≤ 40*(a^2/2+b^2/6+c^2/12+d^2/20)-(-a+b+c-d)^2 := by
    rw [hid]; positivity
  rw [hr] at hpos
  linarith

#print axioms PALRH.OneTick.first_tick_of_certificates
#print axioms PALRH.OneTick.blind_tick_floor

#print axioms PALRH.OneTick.rh_of_first_tick

end PALRH.OneTick
