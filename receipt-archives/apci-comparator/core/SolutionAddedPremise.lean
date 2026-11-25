import APCI

open APCILeanAudit

def trace : Bool → Unit := fun _ => ()
def answer : Bool → Bool := fun b => b

theorem claim (h : ExactCertificate trace answer) : ExactCertificate trace answer := h

#print axioms claim

