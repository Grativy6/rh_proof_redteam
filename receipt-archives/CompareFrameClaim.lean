import FrameByAPCI
import Formalism.LocalToGlobal.Divisibility.FramesLemmas

namespace HearthlineComparison

abbrev FrameClaim : Prop := ∀ {F : Type} [Field F] {n d : ℕ} {C : Matrix (Fin n) (Fin d) F}
    {L : Matrix (Fin d) (Fin n) F}, L * C = 1 → Function.Injective C.mulVec

example : FrameClaim := @Formalism.L2.DIV.inj_of_left_inv
example : FrameClaim := @frame_mulVec_injective

#print axioms Formalism.L2.DIV.inj_of_left_inv
#print axioms HearthlineComparison.frame_mulVec_injective
#print axioms APCILeanAudit.leftInverse_implies_injective

end HearthlineComparison
