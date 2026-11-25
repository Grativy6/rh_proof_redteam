import APCI

open APCILeanAudit

def trace : Bool → Unit := fun _ => ()
def answer : Bool → Bool := sorry

-- This variation deliberately permits the solver to choose `answer`.
-- It is an open-definition control, not the identity-answer challenge.
theorem claim : ExactCertificate trace answer := by sorry
