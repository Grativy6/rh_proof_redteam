import Mathlib.Algebra.Field.Defs
import Mathlib.Data.Matrix.Mul
import APCILeanAudit.Interface

namespace HearthlineComparison

theorem frame_injective_over_semiring {R : Type} [Semiring R] {n d : ℕ} {C : Matrix (Fin n) (Fin d) R}
    {L : Matrix (Fin d) (Fin n) R} (h : L * C = 1) : Function.Injective C.mulVec := by
  apply APCILeanAudit.leftInverse_implies_injective (decode := L.mulVec)
  intro x
  simp [Matrix.mulVec_mulVec, h]

-- Specialize to the original field statement and, separately, to the non-field ℕ.
example {F : Type} [Field F] {n d : ℕ} {C : Matrix (Fin n) (Fin d) F}
    {L : Matrix (Fin d) (Fin n) F} (h : L * C = 1) : Function.Injective C.mulVec :=
  frame_injective_over_semiring h

example {n d : ℕ} {C : Matrix (Fin n) (Fin d) ℕ} {L : Matrix (Fin d) (Fin n) ℕ}
    (h : L * C = 1) : Function.Injective C.mulVec := frame_injective_over_semiring h

-- A report of t mod 5 cannot decide whether the orthogonal denominator 1+t² is 0 mod 25.
theorem quotient_denominator_collision :
    ¬ APCILeanAudit.ExactCertificate (fun t : Nat => t % 5)
        (fun t => (1 + t * t) % 25 == 0) := by
  intro certificate
  have same := APCILeanAudit.exactCertificate_implies_fiberConstant certificate (x := 2) (y := 7) rfl
  contradiction

#print axioms frame_injective_over_semiring
#print axioms quotient_denominator_collision

end HearthlineComparison
