import PALRH.OneSidedBoard

open Finset
open scoped BigOperators

def tripSettings (k : ℕ) : ℕ :=
  ∏ m ∈ Icc 2 (k^4), if m.gcd (k^2).factorial=1 then m^(k^4-m) else 1

def subsetSettings (k : ℕ) : ℕ :=
  ∏ a ∈ range (k^4+1),(k^4).choose a

theorem riemannHypothesis
    (eventualFit : ∃ K : ℕ, ∀ k : ℕ, K≤k → tripSettings k≤subsetSettings k) :
    RiemannHypothesis := by
  obtain ⟨K,fits⟩:=eventualFit
  exact PALRH.OneSidedBoard.rh_of_one_subset_comparison K (fun k late _ => fits k late)

#print axioms riemannHypothesis
