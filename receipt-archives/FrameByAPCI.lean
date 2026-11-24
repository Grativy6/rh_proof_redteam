import Mathlib
import APCILeanAudit.Interface

namespace HearthlineComparison

theorem frame_mulVec_injective {F : Type} [Field F] {n d : ℕ} {C : Matrix (Fin n) (Fin d) F}
    {L : Matrix (Fin d) (Fin n) F} (h : L * C = 1) : Function.Injective C.mulVec := by
  apply APCILeanAudit.leftInverse_implies_injective (decode := L.mulVec)
  intro x
  simp [Matrix.mulVec_mulVec, h]

end HearthlineComparison
