import PALRH.AdjacentSquares

open Finset
open scoped BigOperators

def returnedNumerator (n d : ℕ) : ℤ :=
  (∑ j ∈ Icc 1 (2*n/d), (((2*n:ℕ):ℤ)-(d*j:ℕ))^5 *
    (7*((d*j:ℕ):ℤ)-(2*n:ℕ))) - ((2*n:ℕ):ℤ)^5 * (n-d:ℕ)

def primeDials (n : ℕ) : ℕ :=
  ∏ d ∈ Icc 1 (2*n), if d.Prime ∧ n^7 < d^8 then d^(returnedNumerator n d).toNat else 1

def squareMarks (n b : ℕ) : Finset ℕ :=
  ((Icc 1 (b-2)).image (fun t => b^2-t^2)).filter (fun d => 2*n<3*d ∧ d≤n)

def removedMarks (k s : ℕ) : Finset ℕ :=
  (range s).biUnion (fun a => squareMarks (k^4) (k^2+a))

def holeBill (k s : ℕ) : ℕ :=
  (∑ r ∈ range (2*k^4), r^6) -
    (16*(k^4)^7 + ∑ d ∈ removedMarks k s, (returnedNumerator (k^4) d).toNat)

def covered (k s : ℕ) : Prop :=
  (k^4+1)^(k^4*holeBill k s) ≤ (k^4)^(k^4*holeBill k s)*primeDials (k^4)

def commonPlaces (b : ℕ) : Finset ℕ := squareMarks (b^2) b ∩ squareMarks (b^2) (b+1)

def properFactors (b : ℕ) : Finset ℕ :=
  (range (2*b+2)).filter (fun r => 1<r ∧ r ∣ 2*b+1 ∧ r<(2*b+1)/r)

theorem sameCount {b : ℕ} (hb : 4≤b) : (commonPlaces b).card=(properFactors b).card := by
  exact PALRH.AdjacentSquares.number_of_overlaps hb

theorem inTopNinth {b d : ℕ} (hb : 4≤b) (hd : d∈commonPlaces b) : 8*b^2<9*d := by
  exact PALRH.AdjacentSquares.in_top_ninth hb hd

theorem boardEightOverlap : commonPlaces 64={3696} := by
  exact PALRH.AdjacentSquares.board_eight

theorem riemannHypothesis (paid : ∃ K : ℕ, ∀ k : ℕ, K≤k → covered k 2) :
    RiemannHypothesis := by
  obtain ⟨K,late⟩:=paid
  exact PALRH.SquareHoles.rh_of_two_traces K late

#print axioms sameCount
#print axioms inTopNinth
#print axioms boardEightOverlap
#print axioms riemannHypothesis
