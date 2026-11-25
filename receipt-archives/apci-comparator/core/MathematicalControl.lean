import APCI

open APCILeanAudit

namespace MathematicalControl

/-- Distinct Boolean inputs collide under this constant trace. -/
theorem constant_trace_collision :
    (fun _ : Bool => ()) false = (fun _ : Bool => ()) true := rfl

/-- The unchanged identity answer needs a distinction the trace has erased. -/
theorem identity_cannot_decode :
    ¬ ExactCertificate (fun _ : Bool => ()) (fun b : Bool => b) := by
  intro h
  have hft : (false : Bool) = true :=
    exactCertificate_implies_fiberConstant h
      (x := false) (y := true) rfl
  cases hft

/-- A constant answer factors through exactly the same constant trace. -/
theorem constant_answer_decodes :
    ExactCertificate (fun _ : Bool => ()) (fun _ : Bool => false) :=
  ⟨fun _ => false, fun _ => rfl⟩

#print axioms constant_trace_collision
#print axioms identity_cannot_decode
#print axioms constant_answer_decodes

end MathematicalControl

