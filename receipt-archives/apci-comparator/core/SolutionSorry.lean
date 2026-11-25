import APCI

open APCILeanAudit

def trace : Bool → Unit := fun _ => ()
def answer : Bool → Bool := fun b => b

-- Deliberate invalid submission: records the sorryAx rejection control.
theorem claim : ExactCertificate trace answer := by sorry

#print axioms claim

