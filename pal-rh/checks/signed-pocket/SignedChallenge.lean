import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Algebra.BigOperators.Intervals

open Finset
open scoped BigOperators

def stripRoot (j : ℕ) := 4^(j+1)*(j+1)^2
def stripBoard (j : ℕ) := (stripRoot j)^2

def countedTicks (n d : ℕ) := if 2≤d ∧ d.gcd n.sqrt.factorial=1 then
  ((range (n*n.sqrt)).filter (fun t => (n.sqrt+1)^t<d*n.sqrt^t)).card else 0

def prefixDemand (n m : ℕ) := ∑ d ∈ Icc 1 m,(n-d)*countedTicks n d
def stripArea (n m : ℕ) := ∑ d ∈ Icc 1 m,(n-d)

def returnedJobs (j m : ℕ) :=
  let n:=stripBoard j
  prefixDemand n m+n.sqrt*stripArea n (min m n.sqrt)

def referenceJobs (j m : ℕ) := stripRoot j*stripArea (stripBoard j) m

def due (n p : ℕ) := (n-p)*countedTicks n p

def available (n m : ℕ) := n^2/13+∑ d ∈ Icc 1 m, if n.sqrt<d then n.sqrt*(n-d) else 0

def timelyAssignment (j : ℕ) : Prop :=
  let n:=stripBoard j
  ∃ put : ℕ → ℕ → ℕ, (∀ p≤16^j, ∀ t<due n p, put p t<available n p) ∧
    (∀ p≤16^j, ∀ q≤16^j, ∀ t<due n p, ∀ u<due n q, put p t=put q u → p=q ∧ t=u)

theorem riemannHypothesis (excess : ∀ j m : ℕ, m≤16^j →
    13*(returnedJobs j m-referenceJobs j m)≤(stripBoard j)^2) : RiemannHypothesis := by sorry

theorem shortageAlone (deficit : ∀ j m : ℕ, m≤16^j →
    13*(referenceJobs j m-returnedJobs j m)≤(stripBoard j)^2) : RiemannHypothesis := by sorry

theorem physicalAssignment (maps : ∀ j : ℕ, timelyAssignment j) : RiemannHypothesis := by sorry
