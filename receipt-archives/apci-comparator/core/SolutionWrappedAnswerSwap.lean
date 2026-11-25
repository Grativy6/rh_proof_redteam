import APCI

open APCILeanAudit

def trace : Bool → Unit := fun _ => ()
def answer : Bool → Bool := fun _ => false

def Target : Prop := ExactCertificate trace answer

theorem claim : Target :=
  ⟨fun _ => false, fun _ => rfl⟩

#print axioms claim

