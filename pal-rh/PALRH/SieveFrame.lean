import PALRH.PrimeBand
import Mathlib.Data.Nat.Prime.Factorial

open Finset
open scoped BigOperators

namespace PALRH.SieveFrame
open PrimeBoard PrimeBand

/-- Every label has one externally specified frame. Only their gcd decides whether it is counted. -/
def frameCount (n frame : ℕ) : ℕ :=
  n.factorial^n *
    ∏ m ∈ Icc 2 n, if m.gcd frame = 1 then m^(2*(n-m)) else 1

theorem factorial_test {m n : ℕ} (lo : 2≤m) (hi : m≤n) :
    m.Coprime n.sqrt.factorial ↔ m.Prime ∧ n.sqrt<m := by
  constructor
  · intro clean
    have least:= (Nat.coprime_factorial_iff (by omega : m≠1)).mp clean
    have prime : m.Prime := by
      by_contra composite
      have small:=Nat.minFac_sq_le_self (by omega : 0<m) composite
      have large:=Nat.sqrt_lt.mp least
      rw [pow_two] at small
      omega
    rw [prime.minFac_eq] at least
    exact ⟨prime,least⟩
  · rintro ⟨prime,large⟩
    exact prime.coprime_factorial_of_lt large

theorem frame_count_exact (n : ℕ) :
    frameCount n n.sqrt.factorial=inputCount n n.sqrt := by
  have sets : (Icc 2 n).filter (fun m => m.gcd n.sqrt.factorial = 1) =
      (primes n).filter (fun m => n.sqrt<m) := by
    ext m
    simp only [primes,mem_filter,mem_Icc]
    constructor
    · rintro ⟨⟨lo,hi⟩,clean⟩
      obtain ⟨p,s⟩:=(factorial_test lo hi).mp clean
      exact ⟨⟨⟨p.pos,hi⟩,p⟩,s⟩
    · rintro ⟨⟨⟨_,hi⟩,p⟩,s⟩
      exact ⟨⟨p.two_le,hi⟩,(factorial_test p.two_le hi).mpr ⟨p,s⟩⟩
  unfold frameCount inputCount retained
  rw [←Finset.prod_filter,sets]

/-- Exponents on frame primes do not change what an outside gcd can distinguish. -/
theorem same_frame_factors (m c : ℕ) : m.Coprime c.factorial ↔ m.Coprime (primorial c) := by
  constructor <;> intro clean <;> by_contra bad
  · obtain ⟨p,pp,pm,pf⟩:=Nat.Prime.not_coprime_iff_dvd.mp bad
    exact (Nat.Prime.not_coprime_iff_dvd.mpr ⟨p,pp,pm,pp.dvd_factorial.mpr
      (pp.dvd_primorial_iff.mp pf)⟩) clean
  · obtain ⟨p,pp,pm,pf⟩:=Nat.Prime.not_coprime_iff_dvd.mp bad
    exact (Nat.Prime.not_coprime_iff_dvd.mpr ⟨p,pp,pm,pp.dvd_primorial_iff.mpr
      (pp.dvd_factorial.mp pf)⟩) clean

/-- An exact frame must contain each small prime, witnessed even by that prime's square. -/
theorem square_witness {c frame p : ℕ} (pp : p.Prime) (pc : p≤c)
    (clean : ∀ m : ℕ, 2≤m → m≤c^2 → m.Coprime frame → m.Prime) : p∣frame := by
  by_contra missing
  have good:= (Nat.coprime_pow_left_iff (by decide : 0<2) p frame).mpr (pp.coprime_iff_not_dvd.mpr missing)
  have low : 2≤p^2 := pp.two_le.trans (Nat.le_self_pow (by decide) _)
  have isPrime := clean (p^2) low (Nat.pow_le_pow_left pc 2) good
  have ps:=isPrime.minFac_eq
  rw [pp.pow_minFac (by decide : (2:ℕ)≠0)] at ps
  have p2:=pp.two_le
  nlinarith only [p2,ps,Nat.mul_le_mul_left p p2]

theorem root_of_quartic (k : ℕ) : (k^4).sqrt=k^2 := by
  rw [show k^4=(k^2)^2 by ring,Nat.sqrt_eq']

/-- No primality predicate occurs in these arithmetic premises. -/
theorem rh_of_factorial_frame
    (funded : ∀ k : ℕ, 0<k →
      frameCount (k^4) (k^2).factorial ≤ (k^4)^((k^4)^2) ∧
      (k^4)^((k^4)^2) ≤ frameCount (k^4) (k^2).factorial * 2^(8*k^4*(k^2+1))) :
    RiemannHypothesis := by
  apply rh_of_large_primes
  intro k kp
  have eq:=frame_count_exact (k^4)
  rw [root_of_quartic] at eq
  have budget : (allowance (k^4))^2 = 2^(8*k^4*(k^2+1)) := by
    unfold allowance
    rw [root_of_quartic,←pow_mul]
    congr 1
    ring
  rw [←eq,budget]
  exact funded k kp

set_option maxRecDepth 24000 in
set_option maxHeartbeats 1500000 in
/-- Keep the distance-five question separate from the factor five in the recognizing frame. -/
theorem removing_five_breaks_the_board :
    frameCount (4^4) (primorial 16) ≤ capacity (4^4) ∧
      capacity (4^4) < frameCount (4^4) (primorial 16 / 5) := by decide +kernel

#print axioms PALRH.SieveFrame.frame_count_exact
#print axioms PALRH.SieveFrame.square_witness
#print axioms PALRH.SieveFrame.rh_of_factorial_frame
#print axioms PALRH.SieveFrame.removing_five_breaks_the_board
end PALRH.SieveFrame
