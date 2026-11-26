import PALRH.LocalDistance

open Finset
open scoped BigOperators

def distanceTicks (n d : ℕ) := if 2≤d ∧ d.gcd n.sqrt.factorial=1 then
  ((range (n*n.sqrt)).filter (fun t => (n.sqrt+1)^t<d*n.sqrt^t)).card else 0

def forwardBy (n m : ℕ) := ∑ d ∈ Icc 1 m,(n-d)*distanceTicks n d

def capacityBy (n h m : ℕ) := h*n+2*h*∑ d ∈ Icc 1 m,(n-d)

def columnJobs (n d : ℕ) := 2*((n-d)*distanceTicks n d)

def physicalReturn (n h W : ℕ) : Prop :=
  capacityBy n h n < 2*forwardBy n n+n^2 ∧
  ∃ put : ℕ → ℕ → ℕ,
    (∀ p<n+2, ∀ t<columnJobs n p, put p t∈Ico
      (if p≤W then 0 else capacityBy n h (p-W-1)) (capacityBy n h (min n (p+W)))) ∧
    (∀ p<n+2, ∀ q<n+2, ∀ t<columnJobs n p, ∀ u<columnJobs n q,
      put p t=put q u → p=q ∧ t=u)

theorem riemannHypothesis (moves : ∃ B : ℕ, ∀ j : ℕ, ∃ h W : ℕ,
    physicalReturn (16^(j+1)) h W ∧ W≤B*4^(j+1)*(j+1)^2) : RiemannHypothesis := PALRH.LocalDistance.rh_of_local_moves moves

theorem occupancyControlsHeight {n h W : ℕ} (positive : 0<n) (places : physicalReturn n h W) :
    h≤11*n.sqrt := PALRH.LocalDistance.measured_height positive places

#print axioms riemannHypothesis
#print axioms occupancyControlsHeight
