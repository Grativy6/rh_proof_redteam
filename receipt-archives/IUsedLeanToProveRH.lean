import APCILeanAudit.Interface
import Mathlib.NumberTheory.LSeries.RiemannZeta

namespace Hearthline.Punchline

/-- The decoder prints the proposition placed in its answer slot. -/
theorem certificate (P : Prop) :
    APCILeanAudit.ExactCertificate (fun _ : Bool => ()) (fun _ => P) :=
  ⟨fun _ => P, fun _ => rfl⟩

/-- Both switches print the same answer. This is APCI's axiom-free implication. -/
theorem bothSwitchesAgree (P : Prop) : P = P :=
  APCILeanAudit.exactCertificate_implies_fiberConstant (certificate P)
    (x := false) (y := true) rfl

-- I used Lean to prove RH. The equals sign would like a coauthor credit.
theorem iUsedLeanToProveRH : RiemannHypothesis = RiemannHypothesis :=
  bothSwitchesAgree RiemannHypothesis

example : False = False := bothSwitchesAgree False

-- The joke only passes if offering that result as a proof of RH fails.
example : True := by
  fail_if_success
    have _ : RiemannHypothesis := iUsedLeanToProveRH
  trivial

#check iUsedLeanToProveRH
#print axioms certificate
#print axioms bothSwitchesAgree
#print axioms iUsedLeanToProveRH

end Hearthline.Punchline
