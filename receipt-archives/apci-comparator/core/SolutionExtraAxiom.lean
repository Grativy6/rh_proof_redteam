import APCI

open APCILeanAudit

def trace : Bool → Unit := fun _ => ()
def answer : Bool → Bool := fun b => b

-- Deliberately outside the configured permitted-axiom set.
axiom assumedCertificate : ExactCertificate trace answer

theorem claim : ExactCertificate trace answer := assumedCertificate

#print axioms claim

