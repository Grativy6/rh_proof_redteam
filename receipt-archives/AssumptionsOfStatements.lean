import Mathlib.NumberTheory.LSeries.RiemannZeta
import SpectralFrameControls

namespace HearthlineComparison

/-- The exact field proposition read by the two matrix proofs. -/
def FieldFrameStatement : Prop :=
  ∀ {F : Type} [Field F] {n d : Nat} {C : Matrix (Fin n) (Fin d) F}
    {L : Matrix (Fin d) (Fin n) F}, L * C = 1 → Function.Injective C.mulVec

theorem fieldFrameGiven (h : FieldFrameStatement) : FieldFrameStatement := h

theorem fieldFrameFromSemiring : FieldFrameStatement := by
  intro F _ n d C L h
  exact frame_injective_over_semiring h

/-- A positive control for the assumption report: the conclusion is an explicit premise. -/
theorem riemannGiven (h : RiemannHypothesis) : RiemannHypothesis := h

#print axioms RiemannHypothesis
#print axioms riemannGiven
#print axioms FieldFrameStatement
#print axioms fieldFrameGiven
#print axioms fieldFrameFromSemiring
#print axioms APCILeanAudit.ExactCertificate
#print axioms APCILeanAudit.exactCertificate_implies_fiberConstant
#print axioms quotient_denominator_collision

end HearthlineComparison
