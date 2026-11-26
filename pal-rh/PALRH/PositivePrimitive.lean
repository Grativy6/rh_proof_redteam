import PALRH.LinearPrimeIntegral
import Mathlib.Analysis.SumIntegralComparisons

open Finset Set
open scoped BigOperators

noncomputable section
namespace PALRH.PositivePrimitive

/-- Consecutive reciprocal dilations, paired in their physical order. -/
def alternating (f : ℝ → ℝ) (N : ℕ) (x : ℝ) :=
  ∑ j ∈ range N, (f (x/(2*(j:ℝ)+1))-f (x/(2*(j:ℝ)+2)))

private theorem pair_pos {f : ℝ → ℝ} (mono : MonotoneOn f (Ici 0))
    {x : ℝ} (xp : 0≤x) (j : ℕ) : 0≤f (x/(2*(j:ℝ)+1))-f (x/(2*(j:ℝ)+2)) := by
  apply sub_nonneg.mpr
  apply mono (Set.mem_Ici.mpr (by positivity)) (Set.mem_Ici.mpr (by positivity))
  apply div_le_div_of_nonneg_left xp (by positivity)
  linarith

theorem first_pair {f : ℝ → ℝ} (mono : MonotoneOn f (Ici 0)) {x : ℝ} (xp : 0≤x)
    {N : ℕ} (np : 0<N) : f x-f (x/2)≤alternating f N x := by
  have h:=Finset.single_le_sum (fun j (_ : j∈range N) => pair_pos mono xp j) (mem_range.mpr np)
  simpa [alternating] using h

private theorem root_telescope {x : ℝ} (xp : 0≤x) (N : ℕ) :
    alternating Real.sqrt N x + Real.sqrt (x/(2*(N:ℝ)+1))≤Real.sqrt x := by
  induction N with
  | zero => simp [alternating]
  | succ k ih =>
    unfold alternating at *
    rw [sum_range_succ]
    have down : Real.sqrt (x/(2*((k:ℝ)+1)+1))≤Real.sqrt (x/(2*(k:ℝ)+2)) := by
      apply Real.sqrt_le_sqrt
      exact div_le_div_of_nonneg_left xp (by positivity) (by linarith)
    push_cast
    linarith only [ih,down]

private theorem root_half {x : ℝ} (xp : 0≤x) : 4*Real.sqrt (x/2)≤3*Real.sqrt x := by
  have p:=Real.sqrt_nonneg x
  have q:=Real.sqrt_nonneg (x/2)
  nlinarith only [p,q,Real.sq_sqrt xp,Real.sq_sqrt (show 0≤x/2 by positivity),
    mul_self_le_mul_self_iff (by positivity : 0≤4*Real.sqrt (x/2)) (by positivity : 0≤3*Real.sqrt x)]

/-- The first dilation pair pays a fixed fraction of the trip down to the base interval. -/
theorem halve_to_base {f : ℝ → ℝ} {K : ℝ} (kn : 0≤K)
    (early : ∀ x : ℝ, 0≤x → x<1 → f x≤K*Real.sqrt x)
    (step : ∀ x : ℝ, 1≤x → f x≤f (x/2)+K*Real.sqrt x)
    {x : ℝ} (xp : 0≤x) : f x≤4*K*Real.sqrt x := by
  suffices all : ∀ n : ℕ, ∀ t : ℝ, 0≤t → ⌊t⌋₊=n → f t≤4*K*Real.sqrt t by
    exact all _ x xp rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro t tp index
    by_cases small : t<1
    · nlinarith only [early t tp small,mul_nonneg kn (Real.sqrt_nonneg t)]
    have one:=le_of_not_gt small
    have np : 0<n := index ▸ Nat.floor_pos.mpr one
    have real_one : (1:ℝ)≤n := by exact_mod_cast np
    have upper := Nat.lt_floor_add_one t
    rw [index] at upper
    have half : 0≤t/2 := by positivity
    have smaller : ⌊t/2⌋₊<n := (Nat.floor_lt half).mpr (by linarith)
    have past:=ih _ smaller (t/2) half rfl
    have decay:=mul_le_mul_of_nonneg_left (root_half tp) kn
    nlinarith only [step t one,past,decay]

/-- One upper bound on increments, together with a bounded alternate reading of the
same primitive, controls the primitive in both orientations at the exact square-root scale. -/
theorem signed_recovery {f : ℝ → ℝ} {D K : ℝ} (dn : 0≤D) (kn : 0≤K)
    (early : ∀ x : ℝ, 0≤x → x<1 → f x=0)
    (upper : ∀ x y : ℝ, 0≤y → y≤x → f x-f y≤D*(Real.sqrt x-Real.sqrt y))
    (reading : ∀ x : ℝ, 1≤x → ∃ N : ℕ, 0<N ∧ -(K*Real.sqrt x)≤alternating f N x)
    {x : ℝ} (xp : 0≤x) : |f x|≤4*(D+K)*Real.sqrt x := by
  let p:=fun t : ℝ => D*Real.sqrt t-f t
  have mono : MonotoneOn p (Ici 0) := by
    intro t ht v _ tv
    dsimp [p]
    linarith only [upper v t ht tv]
  have one_step (t : ℝ) (large : 1≤t) : p t≤p (t/2)+(D+K)*Real.sqrt t := by
    have tp : 0≤t := by linarith
    obtain ⟨N,np,observed⟩:=reading t large
    have eq : alternating p N t=D*alternating Real.sqrt N t-alternating f N t := by
      unfold alternating p
      rw [Finset.mul_sum,←Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    have first:=first_pair mono tp np
    rw [eq] at first
    have lim:=root_telescope tp N
    have last:=Real.sqrt_nonneg (t/(2*(N:ℝ)+1))
    nlinarith only [first,observed,mul_le_mul_of_nonneg_left (show alternating Real.sqrt N t≤Real.sqrt t by linarith only [lim,last]) dn]
  have base (t : ℝ) (tn : 0≤t) (small : t<1) : p t≤(D+K)*Real.sqrt t := by
    dsimp [p]
    rw [early t tn small]
    nlinarith only [mul_nonneg kn (Real.sqrt_nonneg t)]
  have bound:=halve_to_base (add_nonneg dn kn) base one_step xp
  have fzero:=early 0 le_rfl (by norm_num)
  have top:=upper x 0 le_rfl xp
  rw [fzero,Real.sqrt_zero,sub_zero,sub_zero] at top
  dsimp [p] at bound
  apply abs_le.mpr
  constructor <;> nlinarith only [bound,top,mul_nonneg dn (Real.sqrt_nonneg x),
    mul_nonneg kn (Real.sqrt_nonneg x)]

#print axioms PALRH.PositivePrimitive.first_pair
#print axioms PALRH.PositivePrimitive.halve_to_base
#print axioms PALRH.PositivePrimitive.signed_recovery
end PALRH.PositivePrimitive
