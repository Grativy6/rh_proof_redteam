import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Algebra.BigOperators.Intervals

open Finset
open scoped BigOperators

def rowHeight (j : ℕ) := 4^(j+1)*(j+1)^2
def retained (x m : ℕ) := ∏ d ∈ Icc 1 m, if 2≤d ∧ d.gcd x.factorial=1 then d else 1

def upperExponent (j m : ℕ) :=
  let x:=rowHeight j
  x*((m-x)+(x/13-(16^j+x-1)/x))

def lowerExponent (j m : ℕ) :=
  let x:=rowHeight j
  x*((m-x)-x/13)

def below (j m q : ℕ) := q*(rowHeight j)^(upperExponent j m)≤(rowHeight j+1)^(upperExponent j m)
def above (j m q : ℕ) := (rowHeight j+1)^(lowerExponent j m)≤q*(rowHeight j)^(lowerExponent j m)

def leastTicks (x q : ℕ) := ((range (q*x)).filter (fun t => (x+1)^t<q*x^t)).card

theorem riemannHypothesis (boards : ∀ j : ℕ,
    (∀ m≤16^j, below j m (retained (rowHeight j) m)) ∨
    (∀ m≤16^j, above j m (retained (rowHeight j) m))) : RiemannHypothesis := by sorry

theorem eachCutMayChoose (j m q : ℕ) : below j m q ∨ above j m q := by sorry

theorem oneTickPerJoin {x a b : ℕ} (xp : 0<x) (ap : 0<a) (bp : 0<b) :
    leastTicks x (a*b)≤leastTicks x a+leastTicks x b ∧
    leastTicks x a+leastTicks x b≤leastTicks x (a*b)+1 := by sorry
