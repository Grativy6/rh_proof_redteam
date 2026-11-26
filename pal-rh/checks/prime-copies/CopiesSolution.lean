import PALRH.PrimeCopies

open Finset
open scoped BigOperators

def returnedNumerator (n d : ℕ) : ℤ :=
  (∑ j ∈ Icc 1 (2*n/d), (((2*n:ℕ):ℤ)-(d*j:ℕ))^5 *
    (7*((d*j:ℕ):ℤ)-(2*n:ℕ))) - ((2*n:ℕ):ℤ)^5 * (n-d:ℕ)

def primeDials (n : ℕ) : ℕ :=
  ∏ d ∈ Icc 1 (2*n), if d.Prime ∧ n^7 < d^8 then d^(returnedNumerator n d).toNat else 1

def cellTicks (k : ℕ) : ℕ := (2*k^4)^5 * k^4 * (k^4-k^2)^2

theorem primeCopyCounts :
    (∀ k : ℕ, 512 ≤ k →
      ¬ (k^4+1)^cellTicks k ≤ (k^4)^cellTicks k * (primeDials (k^4))^13) ∧
    (∀ k : ℕ, 200000^2 ≤ k →
      (k^4+1)^cellTicks k ≤ (k^4)^cellTicks k * (primeDials (k^4))^15) := by
  exact ⟨fun k hk => PALRH.PrimeCopies.thirteen_fail hk,
         fun k hk => PALRH.PrimeCopies.fifteen_pay hk⟩

theorem riemannHypothesis
    (late : ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      (k^4+1)^cellTicks k ≤ (k^4)^cellTicks k * (primeDials (k^4))^14) :
    RiemannHypothesis := by
  obtain ⟨K, paid⟩ := late
  exact PALRH.DoubledPrice.rh_of_prime_settings K (fun k hk _ => paid k hk)

#print axioms primeCopyCounts
#print axioms riemannHypothesis
