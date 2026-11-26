import PALRH.BoardOrientation

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

private theorem same_product (j m : ℕ) :
    retained (rowHeight j) m=PALRH.ProductClock.product (PALRH.ReturnedHorizon.board j) m := by
  unfold retained PALRH.ProductClock.product PALRH.ProductClock.label
  rw [show (PALRH.ReturnedHorizon.board j).sqrt=rowHeight j from Nat.sqrt_eq' _]

theorem riemannHypothesis (boards : ∀ j : ℕ,
    (∀ m≤16^j, below j m (retained (rowHeight j) m)) ∨
    (∀ m≤16^j, above j m (retained (rowHeight j) m))) : RiemannHypothesis := by
  apply PALRH.BoardOrientation.rh_of_product_direction
  intro j
  rcases boards j with up|down
  · left;intro m mh
    have h:=up m mh
    rw [same_product] at h
    exact h
  · right;intro m mh
    have h:=down m mh
    rw [same_product] at h
    exact h

theorem eachCutMayChoose (j m q : ℕ) : below j m q ∨ above j m q := PALRH.ProductBridge.per_cut_choice j m q

theorem oneTickPerJoin {x a b : ℕ} (xp : 0<x) (ap : 0<a) (bp : 0<b) :
    leastTicks x (a*b)≤leastTicks x a+leastTicks x b ∧
    leastTicks x a+leastTicks x b≤leastTicks x (a*b)+1 := PALRH.ProductClock.concatenate xp ap bp

#print axioms riemannHypothesis
#print axioms eachCutMayChoose
#print axioms oneTickPerJoin
