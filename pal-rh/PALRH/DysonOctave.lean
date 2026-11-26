import PALRH
import Mathlib.Analysis.Analytic.Order
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Nonvanishing

open Complex Filter Set
open scoped Topology

noncomputable section
namespace PALRH.DysonOctave

def octave (z : ℂ) : ℂ := Complex.exp ((Real.log 2:ℝ)*z)

/-- Bilateral Mellin multiplier of the triangular window in log scale, away from zero. -/
def kernel (z : ℂ) : ℂ := (octave z-1)^2/(octave z*z^2)

theorem kernel_ne_zero {z : ℂ} (right : 0<z.re) : kernel z≠0 := by
  have l : 0<Real.log 2 := Real.log_pos (by norm_num)
  have big : 1<‖octave z‖ := by
    rw [octave,Complex.norm_exp]
    apply Real.one_lt_exp_iff.mpr
    rw [Complex.re_ofReal_mul]
    exact mul_pos l right
  have off : octave z≠1 := by intro h;rw [h,norm_one] at big;exact (lt_irrefl _ big)
  have zn : z≠0 := by intro h;simp [h] at right
  exact div_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr off))
    (mul_ne_zero (Complex.exp_ne_zero _) (pow_ne_zero _ zn))

private def U := {s : ℂ | 1/2<s.re}
private theorem open_U : IsOpen U := isOpen_lt continuous_const continuous_re

private def shifted (s : ℂ) := kernel (s-1/2)

private theorem shifted_good : AnalyticOnNhd ℂ shifted U := by
  intro s hs
  have pp : 0<(s-1/2).re := by
    change 1/2<s.re at hs
    rw [sub_re];norm_num;linarith
  have nn : s-1/2≠0 := by intro h;rw [h,zero_re] at pp;exact lt_irrefl _ pp
  unfold shifted kernel octave
  fun_prop (disch := first | exact nn | positivity | exact mul_ne_zero (Complex.exp_ne_zero _) (pow_ne_zero _ nn))

def primeSeries (s : ℂ) := LSeries (fun n => (ArithmeticFunction.vonMangoldt n:ℂ)) s

/-- The analytic continuation can be tested against the ordinary, absolutely convergent
prime-power series to the right of one. Its centered window cannot cancel an off-line zero. -/
theorem calibrate_response (r : ℂ) (H : ℂ → ℂ) (regular : DifferentiableOn ℂ H {s : ℂ | 1/2<s.re})
    (overlap : ∀ s : ℂ, 1<s.re → H s=kernel (s-1/2)*primeSeries s-r/(s-1)) :
    r=kernel (1/2) ∧ RiemannHypothesis := by
  let f:=riemannZeta₁
  let A:=fun s : ℂ => (s-1)*shifted s
  let B:=fun s : ℂ => shifted s-r-(s-1)*H s
  have af : AnalyticOnNhd ℂ f U := differentiable_riemannZeta₁.differentiableOn.analyticOnNhd open_U
  have dd : AnalyticOnNhd ℂ (deriv f) U := fun s hs => (af s hs).deriv
  have gH : AnalyticOnNhd ℂ H U := regular.analyticOnNhd open_U
  have aa : AnalyticOnNhd ℂ A U := by
    intro s hs
    exact (analyticAt_id.sub analyticAt_const).mul (shifted_good s hs)
  have bb : AnalyticOnNhd ℂ B U := by
    intro s hs
    exact ((shifted_good s hs).sub analyticAt_const).sub
      ((analyticAt_id.sub analyticAt_const).mul (gH s hs))
  have relation : EqOn (A*deriv f) (B*f) U := by
    apply (aa.mul dd).eqOn_of_preconnected_of_eventuallyEq (bb.mul af)
      (convex_halfSpace_re_gt _).isPreconnected (by norm_num [U] : (2:ℂ)∈U)
    apply eventuallyEq_of_mem ((isOpen_lt continuous_const continuous_re).mem_nhds
      (by norm_num : (1:ℝ)<(2:ℂ).re))
    intro s (rs : 1<s.re)
    have so : s≠1 := by rintro rfl;norm_num at rs
    have zs:=riemannZeta_ne_zero_of_one_le_re rs.le
    have reg := deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add so
    have zz:=riemannZeta_eq_inv_sub_mul so
    have fn : riemannZeta₁ s≠0 := by intro h;rw [h,mul_zero] at zz;exact zs zz
    have ls : primeSeries s = -deriv riemannZeta s/riemannZeta s :=
      ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div rs
    simp only [A,B,f,overlap s rs,shifted,ls]
    rw [reg,zz]
    field_simp [sub_ne_zero.mpr so,fn]
    ring
  refine ⟨?_,?_⟩
  · have at_one:=relation (show (1:ℂ)∈U by norm_num [U])
    have half : (1:ℂ)-1/2=1/2 := by norm_num
    have eq : (0:ℂ)=kernel ((1:ℂ)-1/2)-r := by
      simpa [A,B,f,shifted] using at_one
    rw [half] at eq
    exact (sub_eq_zero.mp eq.symm).symm
  apply rh_of_right
  intro s hs so zero
  have code : f s=0 := by
    rw [riemannZeta_eq_inv_sub_mul so] at zero
    exact (mul_eq_zero.mp zero).resolve_left (inv_ne_zero (sub_ne_zero.mpr so))
  have un : s∈U := hs
  have not_top : analyticOrderAt f s≠⊤ := by
    intro top
    have eq : EqOn f (fun _ => (0:ℂ)) U := af.eqOn_of_preconnected_of_eventuallyEq
      analyticOnNhd_const (convex_halfSpace_re_gt _).isPreconnected un (analyticOrderAt_eq_top.mp top)
    have no := eq (show (1:ℂ)∈U by norm_num [U])
    simp [f] at no
  have off : A s≠0 := by
    apply mul_ne_zero (sub_ne_zero.mpr so)
    apply kernel_ne_zero
    rw [sub_re];norm_num;linarith
  have local_eq : (A*deriv f)=ᶠ[𝓝 s] (B*f) := eventuallyEq_of_mem (open_U.mem_nhds un) relation
  have orders:=analyticOrderAt_congr local_eq
  rw [analyticOrderAt_mul (aa s un) (dd s un),analyticOrderAt_mul (bb s un) (af s un),
    ((aa s un).analyticOrderAt_eq_zero.mpr off),zero_add] at orders
  cases v : analyticOrderAt f s with
  | top => exact not_top v
  | coe n =>
    cases n with
    | zero => exact ((af s un).analyticOrderAt_eq_zero.mp (by simpa using v)) code
    | succ k =>
      have pos : analyticOrderAt f s=(k:ℕ∞)+1 := by simpa using v
      rw [analyticOrderAt_deriv_of_pos (af s un) pos,pos] at orders
      have bad : (k:ℕ∞)+1≤k := (le_add_self : (k:ℕ∞)+1≤analyticOrderAt B s+((k:ℕ∞)+1)).trans_eq orders.symm
      have impossible : k+1≤k := by exact_mod_cast bad
      omega

/-- The analytic continuation can be tested against the ordinary, absolutely convergent
prime-power series to the right of one. Its centered window cannot cancel an off-line zero. -/
theorem rh_of_centered_response (H : ℂ → ℂ) (regular : DifferentiableOn ℂ H {s : ℂ | 1/2<s.re})
    (overlap : ∀ s : ℂ, 1<s.re → H s=kernel (s-1/2)*primeSeries s-kernel (1/2)/(s-1)) :
    RiemannHypothesis :=
  (calibrate_response (kernel (1/2)) H regular overlap).2

def fullReading (j : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc (1:ℕ) (2*j^2),
    ArithmeticFunction.vonMangoldt n / Real.sqrt n *
      max 0 (Real.log 2 - |Real.log ((n:ℝ)/(j:ℝ)^2)|)

def primeReading (j : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc (1:ℕ) (2*j^2), if n.Prime then
    Real.log n / Real.sqrt n * max 0 (Real.log 2 - |Real.log ((n:ℝ)/(j:ℝ)^2)|) else 0

def referenceSlope : ℝ := 4*(Real.sqrt 2+1/Real.sqrt 2-2)

def offCenter : ℝ := Real.log (9/8:ℝ) / Real.log 2
def height : ℝ := 2*Real.pi/Real.log 2
def packet (a u : ℝ) : ℝ := 2*(Real.exp (a*u)+Real.exp (-(a*u)))*Real.cos (height*u)

theorem model_centers : 0<offCenter ∧ offCenter<1/2 := by
  have lp : 0<Real.log 2:=Real.log_pos (by norm_num)
  constructor
  · exact div_pos (Real.log_pos (by norm_num)) lp
  · unfold offCenter
    apply (div_lt_iff₀ lp).mpr
    have h:=Real.log_lt_log (by norm_num : (0:ℝ)<(9/8:ℝ)^2)
      (by norm_num : (9/8:ℝ)^2<2)
    rw [Real.log_pow] at h
    push_cast at h
    linarith only [h]

theorem model_one_turn :
    packet 0 (Real.log 2)=4 ∧ packet offCenter 0=4 ∧ packet offCenter (Real.log 2)=145/36 := by
  have lp:= (Real.log_pos (by norm_num : (1:ℝ)<2)).ne'
  have ht : height*Real.log 2 = 2*Real.pi := by unfold height; exact div_mul_cancel₀ _ lp
  have st : offCenter*Real.log 2=Real.log (9/8:ℝ) := by unfold offCenter; exact div_mul_cancel₀ _ lp
  unfold packet
  rw [ht,Real.cos_two_pi,st,Real.exp_neg,Real.exp_log (by norm_num : (0:ℝ)<9/8)]
  norm_num [Real.exp_neg,Real.exp_log (by norm_num : (0:ℝ)<9/8)]

/-- Positive energy for every pair of real observing amplitudes has one exact cost. -/
theorem two_observer (d r : ℝ) :
    (∀ a b : ℝ, 0≤d*(a^2+b^2)+2*r*a*b) ↔ |r|≤d := by
  constructor
  · intro h
    have plus:=h 1 1
    have minus:=h 1 (-1)
    apply abs_le.mpr
    constructor <;> nlinarith only [plus,minus]
  · intro h a b
    obtain ⟨lo,hi⟩:=abs_le.mp h
    nlinarith only [mul_nonneg (show 0≤d+r by linarith) (sq_nonneg (a+b)),
      mul_nonneg (sub_nonneg.mpr hi) (sq_nonneg (a-b))]

/-- A phase pair returns at one doubling. Splitting its line gives a negative eigenvalue
on the difference of the two observing frames. -/
theorem split_pair_quadratic :
    (4:ℚ)+4-2*(2*(9/8+8/9))= -1/18 := by norm_num

#print axioms PALRH.DysonOctave.two_observer
#print axioms PALRH.DysonOctave.model_centers
#print axioms PALRH.DysonOctave.model_one_turn
#print axioms PALRH.DysonOctave.kernel_ne_zero
#print axioms PALRH.DysonOctave.rh_of_centered_response
#print axioms PALRH.DysonOctave.split_pair_quadratic
end PALRH.DysonOctave
