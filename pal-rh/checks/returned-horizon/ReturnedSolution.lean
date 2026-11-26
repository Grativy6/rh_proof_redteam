import PALRH.ReturnedHorizon

open Finset
open scoped BigOperators

def stripRoot (j : ℕ) := 4^(j+1)*(j+1)^2
def stripBoard (j : ℕ) := (stripRoot j)^2

def countedTicks (n d : ℕ) := if 2≤d ∧ d.gcd n.sqrt.factorial=1 then
  ((range (n*n.sqrt)).filter (fun t => (n.sqrt+1)^t<d*n.sqrt^t)).card else 0

def prefixDemand (n m : ℕ) := ∑ d ∈ Icc 1 m,(n-d)*countedTicks n d
def stripArea (n m : ℕ) := ∑ d ∈ Icc 1 m,(n-d)

def returnedError (j m : ℕ) :=
  let n:=stripBoard j
  let actual:=prefixDemand n m+n.sqrt*stripArea n (min m n.sqrt)
  let reference:=stripRoot j*stripArea n m
  (actual-reference)+(reference-actual)

def worstCut (j : ℕ) := (range (16^j+1)).sup (returnedError j)

theorem riemannHypothesis (allBoards : ∀ j : ℕ, 13*worstCut j≤(stripBoard j)^2) :
    RiemannHypothesis := PALRH.ReturnedHorizon.rh_of_one_thirteenth allBoards

theorem missingStrip {x : ℕ} (two : 2≤x) :
    prefixDemand (x^2) x=0 ∧ (x^2)^2<13*(x*stripArea (x^2) x) := PALRH.ReturnedHorizon.unreturned_root two

#print axioms riemannHypothesis
#print axioms missingStrip
