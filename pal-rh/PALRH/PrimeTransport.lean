import PALRH.ReflectedCarry
import PALRH.EvenWindows

open Finset
open scoped BigOperators Classical
noncomputable section
namespace PALRH.PrimeTransport

/-- Signed moments on physical arithmetic labels. Fractional coefficients represent
the actual portion of each label spent by a transport. -/
def balanced (I : Finset ℕ) (w : ℕ → ℝ) : Prop :=
  (∑ d ∈ I, w d / d) = 0 ∧ (∑ d ∈ I, w d) = 0 ∧
  (∑ d ∈ I, w d * d) = 0 ∧ (∑ d ∈ I, w d * (d:ℝ)^2) = 0 ∧
  (∑ d ∈ I, w d * (d:ℝ)^3) = 0

def form (a b c e f x : ℝ) := a/x + b + c*x + e*x^2 + f*x^3

theorem price_zero {I : Finset ℕ} {w : ℕ → ℝ} (h : balanced I w) (a b c e f : ℝ) :
    (∑ d ∈ I, w d * form a b c e f d) = 0 := by
  obtain ⟨h0,h1,h2,h3,h4⟩ := h
  calc
    _ = a*(∑ d ∈ I, w d/d) + b*(∑ d ∈ I, w d) + c*(∑ d ∈ I, w d*d) +
        e*(∑ d ∈ I, w d*(d:ℝ)^2) + f*(∑ d ∈ I, w d*(d:ℝ)^3) := by
      simp only [Finset.mul_sum, ←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro d _
      simp only [form, div_eq_mul_inv]
      ring
    _ = 0 := by rw [h0,h1,h2,h3,h4]; ring

/-- Five equal differences kill the quartic obtained by clearing the physical label. -/
theorem six_labels (a b c e f x h : ℝ) (xp : 0<x) (hp : 0≤h) :
    let g := fun z : ℝ => z*form a b c e f z;
    (-(g x)) + 5*g (x+h) - 10*g (x+2*h) + 10*g (x+3*h) -
      5*g (x+4*h) + g (x+5*h) = 0 := by
  have clear (z : ℝ) (nz : 0<z) :
      z*form a b c e f z = a+b*z+c*z^2+e*z^3+f*z^4 := by
    unfold form
    field_simp [nz.ne']
  dsimp only
  rw [clear x xp, clear (x+h) (by positivity), clear (x+2*h) (by positivity),
    clear (x+3*h) (by positivity), clear (x+4*h) (by positivity),
    clear (x+5*h) (by positivity)]
  ring

private theorem rest_eq {T d k : ℕ} (hk : T/d=k) :
    ((T%d:ℕ):ℝ) = (T:ℝ)-(k:ℝ)*d := by
  have h := Nat.mod_add_div T d
  rw [hk] at h
  have h' : ((T%d:ℕ):ℝ) + (d:ℝ)*(k:ℝ) = (T:ℝ) := by exact_mod_cast h
  linarith only [h']

private def slope (k : ℕ) : ℝ := 2*(k:ℝ)+1
private def product (k : ℕ) : ℝ := (k:ℝ)*(k+1)

private theorem point_form {T d k : ℕ} (ht : 0<T) (hd : 0<d) (active : d≤T) (hk : T/d=k) :
    ReflectedCells.residue T d =
    form ((T:ℝ)^4) (-(slope k)*T^3) 0 (slope k*product k*T) (-(product k)^2) d /
      (2*(T:ℝ)^3) := by
  rw [ReflectedCells.residue, if_pos active, ReflectedCells.numerator, rest_eq hk]
  have dt : (d:ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have tt : (T:ℝ) ≠ 0 := by exact_mod_cast ht.ne'
  dsimp [form, slope, product]
  field_simp [dt,tt]
  ring

private theorem energy_form {T d k : ℕ} (ht : 0<T) (hd : 0<d) (active : d≤T) (hk : T/d=k) :
    EvenWindows.energy T d =
    form ((T:ℝ)^4) (-2*slope k*T^3) (((slope k)^2+2*product k)*T^2)
      (-2*slope k*product k*T) ((product k)^2) d / (4*(T:ℝ)^2) := by
  rw [EvenWindows.energy, if_pos active, rest_eq hk]
  have dt : (d:ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have tt : (T:ℝ) ≠ 0 := by exact_mod_cast ht.ne'
  dsimp [form, slope, product]
  field_simp [dt,tt]
  ring

/-- The same transport pays the actual oriented residue and the even window potential
at every head at which the labels share one active quotient. -/
theorem both_prices {I : Finset ℕ} {w : ℕ → ℝ} (h : balanced I w)
    {T k : ℕ} (ht : 0<T) (cell : ∀ d ∈ I, 0<d ∧ d≤T ∧ T/d=k) :
    (∑ d ∈ I, w d * ReflectedCells.residue T d) = 0 ∧
    (∑ d ∈ I, w d * EvenWindows.energy T d) = 0 := by
  constructor
  · calc
      _ = (∑ d ∈ I, w d * form ((T:ℝ)^4) (-(slope k)*T^3) 0
          (slope k*product k*T) (-(product k)^2) d) / (2*(T:ℝ)^3) := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro d hd
        obtain ⟨dp,dt,dk⟩ := cell d hd
        rw [point_form ht dp dt dk]; ring
      _ = 0 := by rw [price_zero h]; simp
  · calc
      _ = (∑ d ∈ I, w d * form ((T:ℝ)^4) (-2*slope k*T^3)
          (((slope k)^2+2*product k)*T^2) (-2*slope k*product k*T)
          ((product k)^2) d) / (4*(T:ℝ)^2) := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro d hd
        obtain ⟨dp,dt,dk⟩ := cell d hd
        rw [energy_form ht dp dt dk]; ring
      _ = 0 := by rw [price_zero h]; simp

def spent (w : ℕ → ℝ) (T : ℕ) :=
  ∑ d ∈ Finset.Icc 1 T, w d*(ReflectedCells.residue T d-ReflectedCells.residue T (2*d))

def remaining (w : ℕ → ℝ) (T N : ℕ) :=
  ReflectedCarry.source T N + ReflectedCarry.charge (fun _ => True) T N - spent w T

/-- An already funded physical substream can be removed from the fourth-power test. -/
theorem rh_after_transport (w : ℕ → ℝ) {C : ℝ} (cn : 0≤C)
    (test : ∃ B : ℕ, ∀ N j : ℕ, B≤j → 0<j → j^4≤2^N →
      |spent w (2*j^4)|≤C*(j:ℝ)^2 ∧ 0≤remaining w (2*j^4) N) :
    RiemannHypothesis := by
  obtain ⟨B,later⟩ := test
  apply CubicFourth.rh_of_fourth_floor (A:=2*C) (by positivity)
  refine ⟨B,?_⟩
  intro N j late jp inside
  obtain ⟨cost,rest⟩ := later N j late jp inside
  have id := ReflectedCarry.identity N (j^4) (pow_pos jp _)
  unfold remaining at rest
  rw [←id] at rest
  push_cast at rest
  have jr : 0<(j:ℝ) := by exact_mod_cast jp
  have paid : -(C*(j:ℝ)^2) ≤ (j:ℝ)^4/2*SquarePass.reading N 1 ((j:ℝ)^4) := by
    linarith only [(abs_le.mp cost).1,rest]
  apply le_of_mul_le_mul_left (a:=(j:ℝ)^4/2) _ (by positivity)
  calc
    (j:ℝ)^4/2 * (-(2*C/(j:ℝ)^2)) = -(C*(j:ℝ)^2) := by field_simp
    _ ≤ _ := paid

#print axioms PALRH.PrimeTransport.six_labels
#print axioms PALRH.PrimeTransport.both_prices
#print axioms PALRH.PrimeTransport.rh_after_transport
end PALRH.PrimeTransport
