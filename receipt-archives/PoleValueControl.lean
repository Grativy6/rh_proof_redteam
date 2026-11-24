import Mathlib.Analysis.Meromorphic.Order
import Mathlib.NumberTheory.LSeries.Nonvanishing
import APCILeanAudit.Interface

namespace Hearthline.PoleValue

noncomputable section
open Filter Topology
open scoped Classical

def fill (c : ℂ) : ℂ → ℂ := Function.update riemannZeta 1 c

def regularize (f : ℂ → ℂ) : ℂ → ℂ := Function.update (fun s => (s - 1) * f s) 1 1

theorem poleOrderInvariant (c : ℂ) :
    meromorphicOrderAt (fill c) (1 : ℂ) = meromorphicOrderAt riemannZeta 1 := by
  apply meromorphicOrderAt_congr
  filter_upwards [self_mem_nhdsWithin] with s hs
  simp [fill, show s ≠ 1 from hs]

theorem commonRegularization (c : ℂ) : regularize (fill c) = regularize riemannZeta := by
  funext s
  by_cases hs : s = 1
  · subst s; simp [regularize]
  · simp [regularize, fill, hs]

/-- The exact nonvanishing comparison used in the principal branch of poleData_char. -/
theorem sameZeros_iff (c : ℂ) :
    (∀ s, regularize riemannZeta s ≠ 0 ↔ fill c s ≠ 0) ↔ c ≠ 0 := by
  constructor
  · intro h
    have hn := (h 1).mp (by simp [regularize])
    simpa [fill] using hn
  · intro hc s
    by_cases hs : s = 1
    · subst s; simp [regularize, fill, hc]
    · simp [regularize, fill, hs, sub_ne_zero.mpr hs]

def onLine (f : ℂ → ℂ) : Prop :=
  ∀ (s : ℂ), f s = 0 → (¬ ∃ n : ℕ, s = -2 * (n + 1)) → s ≠ 1 → s.re = 1 / 2

theorem headlineInvariant (c : ℂ) : onLine (fill c) ↔ RiemannHypothesis := by
  constructor
  · intro h s hz hn hs
    exact h s (by simpa [fill, hs] using hz) hn hs
  · intro h s hz hn hs
    exact h s (by simpa [fill, hs] using hz) hn hs

/-- Test a region where Mathlib's nonvanishing theorem is unconditional. -/
theorem closedRightHalf_iff (c : ℂ) :
    (∀ s : ℂ, 1 ≤ s.re → fill c s ≠ 0) ↔ c ≠ 0 := by
  constructor
  · intro h
    simpa [fill] using h 1 (by simp)
  · intro hc s hs
    by_cases h : s = 1
    · subst s; simpa [fill] using hc
    · simpa [fill, h] using riemannZeta_ne_zero_of_one_le_re hs

def punctured (c : ℂ) (s : {z : ℂ // z ≠ 1}) : ℂ := fill c s.1

theorem punctured_does_not_decide_pole :
    ¬ APCILeanAudit.ExactCertificate punctured (fun c => fill c 1 = 0) := by
  intro certificate
  have trace_eq : punctured 0 = punctured 1 := by
    funext s
    simp [punctured, fill, s.property]
  have answers := APCILeanAudit.exactCertificate_implies_fiberConstant certificate
    (x := 0) (y := 1) trace_eq
  have wrong : fill 1 1 = 0 := answers.mp (by simp [fill])
  simp [fill] at wrong

end
end Hearthline.PoleValue
