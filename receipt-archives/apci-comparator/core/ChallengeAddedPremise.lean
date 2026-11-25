import APCI

open APCILeanAudit

def trace : Bool → Unit := fun _ => ()
def answer : Bool → Bool := fun b => b

theorem claim : ExactCertificate trace answer := by sorry

