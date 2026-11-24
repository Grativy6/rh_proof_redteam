import Formalism.GammaFactorNonvanishing.RhOfRight

namespace HearthlineComparison

def ZetaRightHalf : Prop :=
  ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → riemannZeta s ≠ 0

/-- Reverse the exact hypothesis of the released final reflection lemma. -/
theorem rightHalfOfRH (h : RiemannHypothesis) : ZetaRightHalf := by
  intro s hs hs1 hz
  have htriv : ¬ ∃ n : ℕ, s = -2 * (n + 1) := by
    rintro ⟨n, hn⟩
    have hre := congrArg Complex.re hn
    norm_num [Complex.mul_re] at hre
    have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
    linarith
  exact (ne_of_gt hs) (h s hz htriv hs1)

theorem rightHalf_iff_RH : ZetaRightHalf ↔ RiemannHypothesis :=
  ⟨Formalism.VW.rh_of_right, rightHalfOfRH⟩

#print axioms Formalism.VW.rh_of_right
#print axioms rightHalfOfRH
#print axioms rightHalf_iff_RH

end HearthlineComparison
