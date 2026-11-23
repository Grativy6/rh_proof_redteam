import Mathlib.Data.ENat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
Algebraic controls for the public RH audit. These theorems use Mathlib and do
not import the RH release. The report identifies the release hypotheses to
which each control applies.
-/

namespace RHRedteam

/-- Eliminate the single height shared by the two nonzero-map inequalities. -/
theorem height_exists_iff (lower mu fo rhs : ℝ) :
    (∃ h : ℝ, lower ≤ h ∧ mu + h - fo ≤ rhs) ↔ mu + lower - fo ≤ rhs := by
  constructor
  · rintro ⟨h, hl, hu⟩
    linarith
  · intro hu
    exact ⟨lower, le_rfl, hu⟩

/-- Exactly which shifts of the reported height preserve both endpoint tests? -/
theorem allowed_height_shifts (lower h mu fo rhs shift : ℝ) :
    (lower ≤ h + shift ∧ mu + (h + shift) - fo ≤ rhs) ↔
      (lower - h ≤ shift ∧ shift ≤ rhs + fo - mu - h) := by
  constructor <;> rintro ⟨hl, hu⟩ <;> constructor <;> linarith

/-- The zero case of a conditional lower bound really can accept a bad endpoint.
The two cases use the same scalar endpoints. Only the nonzero premise changes. -/
theorem zero_gate :
    (∃ h : ℝ, (((0 : ℝ) ≠ 0) → 1 ≤ h) ∧ h ≤ 0) ∧
      ¬ (∃ h : ℝ, (((1 : ℝ) ≠ 0) → 1 ≤ h) ∧ h ≤ 0) := by
  constructor
  · exact ⟨0, fun hn => (hn rfl).elim, le_rfl⟩
  · rintro ⟨h, low, high⟩
    have one_le : (1 : ℝ) ≤ h := low one_ne_zero
    linarith

/-- Allowing a different constant at every scale destroys uniformity. -/
theorem pointwise_not_uniform :
    (∀ x : ℕ, ∃ c : ℕ, x ≤ c) ∧ ¬ (∃ c : ℕ, ∀ x : ℕ, x ≤ c) := by
  constructor
  · exact fun x => ⟨x, le_rfl⟩
  · rintro ⟨c, hc⟩
    exact Nat.not_succ_le_self c (hc (c + 1))

/-- Separately inhabited acceptable-witness sets can be disjoint. -/
theorem incompatible_witnesses :
    (∃ w : Bool, w = false) ∧ (∃ w : Bool, w = true) ∧
      ¬ (∃ w : Bool, w = false ∧ w = true) := by
  refine ⟨⟨false, rfl⟩, ⟨true, rfl⟩, ?_⟩
  rintro ⟨w, rfl, hw⟩
  cases hw

/-- Any finite prefix admits both a bounded and an unbounded continuation. -/
theorem finite_prefix (cutoff : ℕ) :
    ∃ f g : ℕ → ℕ, (∀ n ≤ cutoff, f n = g n) ∧
      (∃ c, ∀ n, f n ≤ c) ∧ ¬ (∃ c, ∀ n, g n ≤ c) := by
  refine ⟨fun _ => 0, fun n => n - cutoff, ?_, ⟨0, fun _ => le_rfl⟩, ?_⟩
  · intro n hn
    exact (Nat.sub_eq_zero_of_le hn).symm
  · rintro ⟨c, hc⟩
    have h := hc (c + cutoff + 1)
    dsimp at h
    omega

/-- The zero and infinite lengths collide after projection to a natural number. -/
theorem projection_loses_finiteness :
    ¬ (∃ decode : ℕ → Prop, ∀ a : ℕ∞, decode a.toNat ↔ a ≠ ⊤) := by
  rintro ⟨decode, h⟩
  have at_zero : decode 0 := by simpa using (h 0).2 (by simp)
  have at_infinity := (h ⊤).1 (by simpa using at_zero)
  exact at_infinity rfl

/-- A separately supplied finiteness witness restores the original length. -/
theorem length_recovered (a : ℕ∞) (finite : a ≠ ⊤) :
    (a.toNat : ℕ∞) = a :=
  ENat.coe_toNat finite

#print axioms height_exists_iff
#print axioms allowed_height_shifts
#print axioms zero_gate
#print axioms pointwise_not_uniform
#print axioms incompatible_witnesses
#print axioms finite_prefix
#print axioms projection_loses_finiteness
#print axioms length_recovered

end RHRedteam
