import Mathlib.Tactic

namespace PALRH.CutInventory

/-- External cells permanently spent, and ordinary cells held across the current cut. -/
def greedy (K : ℕ) (jobs released : ℕ → ℕ) : ℕ → ℕ × ℕ
  | 0 => (0,0)
  | i+1 =>
    let prev:=greedy K jobs released i
    let free:=prev.2+released i
    (prev.1+(jobs i-free),min K (free-jobs i))

/-- A competing placement may spend early and discard credit arbitrarily.
Greedy uses a smallest pocket at every prefix and preserves the corresponding net stock. -/
theorem least_draw (K : ℕ) (jobs released spent stock : ℕ → ℕ)
    (s0 : spent 0=0) (h0 : stock 0=0)
    (legal : ∀ i : ℕ, spent i≤spent (i+1) ∧ stock (i+1)≤K ∧
      stock (i+1)+jobs i≤stock i+released i+(spent (i+1)-spent i)) :
    ∀ i : ℕ, (greedy K jobs released i).1≤spent i ∧
      stock i+(greedy K jobs released i).1≤(greedy K jobs released i).2+spent i := by
  intro i
  induction i with
  | zero => simp [greedy,s0,h0]
  | succ i ih =>
    obtain ⟨mon,cap,pay⟩:=legal i
    simp only [greedy]
    rcases ih with ⟨s,h⟩
    omega

/-- On a downward, upward, downward reversal, the smaller middle excursion adds
exactly its depth above capacity to the pocket and leaves the final stock unchanged. -/
theorem down_up_down (K h a d b : ℕ) (da : d≤a) (db : d≤b) :
    d-min K (h+a)=d-K ∧
    min K ((min K (h+a)-d)+b)=min K (h+(a+b-d)) := by omega

/-- The other orientation gives the identical excess draw. -/
theorem up_down_up (K h a d b : ℕ) (hc : h≤K) (da : d≤a) (db : d≤b) :
    (a-h)+(b-min K ((h-a)+d))=((a+b-d)-h)+(d-K) ∧
    (min K ((h-a)+d))-b=h-(a+b-d) := by omega

/-- At a specified cut, the two bracketing peak requirements give its necessary inventory. -/
theorem crossing {a z b spent rest stock : ℤ} (first : a≤spent) (later : b-z≤stock+rest)
    (total : spent+rest=max a b) : min a b-z≤stock := by omega

#print axioms PALRH.CutInventory.least_draw
#print axioms PALRH.CutInventory.down_up_down
#print axioms PALRH.CutInventory.up_down_up
#print axioms PALRH.CutInventory.crossing
end PALRH.CutInventory
