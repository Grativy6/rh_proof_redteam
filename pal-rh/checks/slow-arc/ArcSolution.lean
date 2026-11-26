import PALRH.SpokeArc

open Finset
open scoped BigOperators

def arcRoot (j : ℕ) := 4^(j+1)*(j+1)^2
def arcBoard (j : ℕ) := (arcRoot j)^2
def markTicks (n d : ℕ) := if 2≤d ∧ d.gcd n.sqrt.factorial=1 then
  ((range (n*n.sqrt)).filter (fun t => (n.sqrt+1)^t<d*n.sqrt^t)).card else 0
def movement (j m : ℕ) : ℤ :=
  ((∑ d ∈ Icc 1 m,markTicks (arcBoard j) d:ℕ):ℤ)-
  (arcRoot j:ℤ)*((m-arcRoot j:ℕ):ℤ)
def arcTest (j m : ℕ) : Prop :=
  let n:ℤ:=arcBoard j
  let a:ℤ:=(arcRoot j:ℤ)*(arcRoot j/13:ℕ)
  let r:=movement j m%n
  r≤a ∨ n-a≤r

theorem riemannHypothesis (observations : ∀ j m : ℕ, m≤16^j → arcTest j m) :
    RiemannHypothesis := PALRH.SpokeArc.rh_of_residues observations

theorem sameLift (j : ℕ) (observations : ∀ m≤16^j, arcTest j m) :
    ∀ m≤16^j, |movement j m|≤(arcRoot j:ℤ)*(arcRoot j/13:ℕ) := PALRH.SpokeArc.lift_board j observations

#print axioms riemannHypothesis
#print axioms sameLift
