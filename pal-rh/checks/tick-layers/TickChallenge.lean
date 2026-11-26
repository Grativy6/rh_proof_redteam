import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Intervals

open Finset
open scoped BigOperators

def levelsFor (n x m : ℕ) := ((range (n*x)).filter (fun t => (x+1)^t<m*x^t)).card
def forwardCells (k : ℕ) := ∑ m ∈ Icc 2 (k^4),
  if m.gcd (k^2).factorial=1 then (k^4-m)*levelsFor (k^4) (k^2) m else 0
def subsetsAt (n : ℕ) := ∏ a ∈ range (n+1),n.choose a

theorem riemannHypothesis (eventualFit : ∃ K : ℕ, ∀ k : ℕ, K≤k →
    2*forwardCells k≤(k^4)^2*(k^2-2)) : RiemannHypothesis := by sorry

theorem sharedFiveChoices : (subsetsAt 2)^4*subsetsAt 3*(subsetsAt 5)^3=(subsetsAt 4)^2*5^12 := by sorry

theorem reversibleInnerTrips {n x p b i t : ℕ} (bp : 0<b) (height : 2*b+2≤x)
    (prime : p.Prime) (large : n.sqrt<p) (bits : p≤2^b)
    (room : 4*(b+1)*p≤n) (start : i<n-p) (layer : t<levelsFor n x p) :
    let h:=x-2
    let a:=(n+1)/2
    let d:=(2*(t/h)+i/a+1)*p
    let v:=d/p-1
    i%a+d<n ∧ d≤n/2 ∧ t%h<h ∧ (v%2*a+i%a,v/2*h+t%h)=(i,t) ∧
      (∀ q : ℕ, q.Prime → n.sqrt<q → q∣d → q=p) := by sorry

theorem localMapsShareAState {A B I : Type} [Fintype A] [Fintype B]
    (live : I → A → Prop) (slot : I → A → B)
    (see : ∀ a b : A, ∃ i, live i a ∧ live i b)
    (injects : ∀ i, Set.InjOn (slot i) {a | live i a})
    (agrees : ∀ a i j, live i a → live j a → slot i a=slot j a) :
    Fintype.card A≤Fintype.card B := by sorry
