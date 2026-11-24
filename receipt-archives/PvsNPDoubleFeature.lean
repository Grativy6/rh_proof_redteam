import FormalConjecturesForMathlib.Computability.Complexity
import IUsedLeanToProveRH

namespace Hearthline.Punchline

open ComplexityTheory

theorem iProvedPEqualsNP : (P = NP) = (P = NP) :=
  bothSwitchesAgree (P = NP)

theorem iProvedPNotEqualsNP : (P ≠ NP) = (P ≠ NP) :=
  bothSwitchesAgree (P ≠ NP)

-- On the unwrapped propositions, classical logic gives precisely one winner.
theorem atLeastOneHeadline : P = NP ∨ P ≠ NP :=
  Classical.em (P = NP)

theorem noDoublePrize : ¬ (P = NP ∧ P ≠ NP) :=
  fun ⟨yes, no⟩ => no yes

example : True := by
  fail_if_success
    have _ : P = NP := iProvedPEqualsNP
  fail_if_success
    have _ : P ≠ NP := iProvedPNotEqualsNP
  fail_if_success
    have _ : P = NP ∧ P ≠ NP := ⟨iProvedPEqualsNP, iProvedPNotEqualsNP⟩
  trivial

#check iProvedPEqualsNP
#check iProvedPNotEqualsNP
#check atLeastOneHeadline
#check noDoublePrize
#print axioms ComplexityTheory.P
#print axioms ComplexityTheory.NP
#print axioms iProvedPEqualsNP
#print axioms iProvedPNotEqualsNP
#print axioms atLeastOneHeadline
#print axioms noDoublePrize

end Hearthline.Punchline
