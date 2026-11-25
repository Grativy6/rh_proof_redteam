import Mathlib.NumberTheory.LSeries.RiemannZeta

-- Minimal extract of Pang's APCI interface and the prior RH control.
namespace APCIControl

def FiberConstant {W T A : Type} (trace : W → T) (answer : W → A) : Prop :=
  ∀ ⦃x y⦄, trace x = trace y → answer x = answer y

def ExactCertificate {W T A : Type} (trace : W → T) (answer : W → A) : Prop :=
  ∃ decode : T → A, ∀ x, decode (trace x) = answer x

theorem exactCertificate_implies_fiberConstant {W T A : Type}
    {trace : W → T} {answer : W → A}
    (h : ExactCertificate trace answer) : FiberConstant trace answer := by
  rcases h with ⟨decode, hdecode⟩
  intro x y hxy
  calc
    answer x = decode (trace x) := (hdecode x).symm
    _ = decode (trace y) := congrArg decode hxy
    _ = answer y := hdecode y

theorem certificate (P : Prop) :
    ExactCertificate (fun _ : Bool => ()) (fun _ => P) :=
  ⟨fun _ => P, fun _ => rfl⟩

theorem bothSwitchesAgree (P : Prop) : P = P :=
  exactCertificate_implies_fiberConstant (certificate P)
    (x := false) (y := true) rfl
end APCIControl

def AnswerSlot : Prop := RiemannHypothesis

theorem claim : RiemannHypothesis ↔ AnswerSlot :=
  Iff.of_eq (APCIControl.bothSwitchesAgree RiemannHypothesis)

#print axioms claim
