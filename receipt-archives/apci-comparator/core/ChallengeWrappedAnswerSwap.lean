import APCI

open APCILeanAudit

def trace : Bool → Unit := fun _ => ()
def answer : Bool → Bool := fun b => b

def Target : Prop := ExactCertificate trace answer

theorem claim : Target := by sorry

