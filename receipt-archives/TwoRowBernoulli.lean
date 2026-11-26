import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Tactic

/-!
# Two short Bernoulli rows and the conductor-64 obstruction

Christopher Daniel Pang and Hearthline (Codex), 25 November 2026.
Companion to `proofs/two-rows-halve-the-bernoulli-conductor-cutoff.md`.

`two_row_progression` starts after the paper's Fourier reduction and proves the normalized
row identity over a field. `character64_isPrimitive` and `character64_bernoulli_sum` check
the lower boundary from an explicit Dirichlet character and the original weighted sum.
-/

namespace TwoRowBernoulli

open Finset

private theorem shift_sum {K : Type*} [CommRing K] (γ : K) (u : ℕ → K) (f : ℕ) :
    γ * (∑ b ∈ range f, u (b + 1) * γ ^ b) - (∑ b ∈ range f, u b * γ ^ b) =
      u f * γ ^ f - u 0 := by
  induction f with
  | zero => simp
  | succ f ih =>
    rw [sum_range_succ, sum_range_succ, pow_succ]
    linear_combination ih

/-- The short Fourier row with denominator `1 - γ ^ f`. -/
def normalizedRow {K : Type*} [Field K] (γ : K) (f : ℕ) (u : ℕ → K) : K :=
  -2 / (1 - γ ^ f) * ∑ b ∈ range f, u b * γ ^ b

/-- Subtract a row from the shifted row multiplied by `γ`. Periodicity of the coefficient
at the two endpoints leaves exactly twice the initial coefficient. -/
theorem two_row_certificate {K : Type*} [Field K] (γ : K) (f : ℕ) (u : ℕ → K)
    (hperiod : u f = u 0) (hγ : γ ^ f ≠ 1) :
    γ * normalizedRow γ f (fun b ↦ u (b + 1)) - normalizedRow γ f u = 2 * u 0 := by
  unfold normalizedRow
  rw [mul_left_comm γ, ← mul_sub, shift_sum, hperiod]
  field_simp [sub_ne_zero.mpr hγ.symm]
  ring

/-- Two arithmetic progressions in the residue labels modulo the odd conductor differ by one
step. The identity holds for any coefficient function on those labels. -/
theorem two_row_progression {K : Type*} [Field K] {f : ℕ} [NeZero f] (φ : ZMod f → K)
    (a h : ZMod f) (γ : K) (hγ : γ ^ f ≠ 1) :
    γ * normalizedRow γ f (fun b ↦ φ (a + h + (b : ZMod f) * h)) -
      normalizedRow γ f (fun b ↦ φ (a + (b : ZMod f) * h)) = 2 * φ a := by
  simpa [add_mul, add_assoc, add_left_comm, add_comm] using
    two_row_certificate γ f (fun b ↦ φ (a + (b : ZMod f) * h)) (by simp) hγ

/-- Values at the 32 odd residues in increasing order. The table is obtained by sending
`±5^j` to `±11^j` for `0 ≤ j < 16`. The character laws are checked on the whole residue ring. -/
private def value64 (x : ZMod 64) : ZMod 17 :=
  if x.val % 2 = 0 then 0 else
    (([1, 12, 11, 2, 8, 7, 14, 13, 13, 14, 7, 8, 2, 11, 12, 1,
       16, 5, 6, 15, 9, 10, 3, 4, 4, 3, 10, 9, 15, 6, 5, 16] : List ℕ).getD (x.val / 2) 0 : ℕ)

set_option maxRecDepth 8192 in
/-- A Dirichlet character of level 64 with values in the field of 17 elements. -/
def character64 : DirichletCharacter (ZMod 17) 64 where
  toFun := value64
  map_one' := by decide
  map_mul' := by decide
  map_nonunit' := by
    have h : ∀ x : ZMod 64, ¬ x.val.Coprime 64 → value64 x = 0 := by decide
    intro x hx
    exact h x (fun hc ↦ hx (by simpa using (ZMod.isUnit_iff_coprime x.val 64).mpr hc))

theorem character64_generators : character64 (-1) = -1 ∧ character64 5 = 11 := by decide

/-- The residues 1 and 33 agree at level 32 but have different character values. -/
private theorem character64_does_not_factor_at_32 : ¬ character64.FactorsThrough 32 := by
  rintro ⟨hd, ψ, hχ⟩
  have h_cop : IsCoprime (33 : ℤ) 64 := ⟨-31, 16, by norm_num⟩
  have h_one : character64 33 = 1 := calc
    character64 33 = (DirichletCharacter.changeLevel hd ψ) (33 : ℤ) := by rw [hχ]; norm_num
    _ = ψ (33 : ℤ) := DirichletCharacter.changeLevel_eq_cast_of_dvd' ψ hd h_cop
    _ = 1 := by rw [show ((33 : ℤ) : ZMod 32) = 1 by decide, map_one]
  exact (by decide : character64 33 ≠ 1) h_one

theorem character64_isPrimitive : character64.IsPrimitive := by
  by_contra h
  have hd := character64.conductor_dvd_level
  have hbound := Nat.le_of_dvd (by decide : 0 < 64) hd
  have hproper : ∀ k : Fin 65, k.val ∣ 64 → k.val ≠ 64 → k.val ∣ 32 := by decide
  have h32 := hproper ⟨character64.conductor, by omega⟩ hd h
  exact character64_does_not_factor_at_32
    (DirichletCharacter.FactorsThrough.mono character64 character64.factorsThrough_conductor h32
      (by decide))

private instance : Fact (Nat.Prime 17) := ⟨by decide⟩

/-- The first generalized Bernoulli sum at this nontrivial character reduces to zero.
The denominator 64 is invertible modulo 17. -/
theorem character64_bernoulli_sum :
    (∑ a ∈ range 64, (a : ZMod 17) * character64 (a : ZMod 64)) / (64 : ZMod 17) = 0 := by
  have hsum : (∑ a ∈ range 64, (a : ZMod 17) * character64 (a : ZMod 64)) = 0 := by
    decide +kernel
  rw [hsum, zero_div]

end TwoRowBernoulli
