import PALRH.Frames
import Mathlib.Data.Nat.Factors
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Mathlib.Tactic

namespace PALRH

/-- Actual leftover after removing known prime factors, including their multiplicities. -/
def freshPart (B n : ℕ) : ℕ := (n.primeFactorsList.filter (fun p => B < p)).prod

private theorem prime_dvd_list {p : ℕ} (hp : p.Prime) (l : List ℕ)
    (h : p ∣ l.prod) : ∃ q ∈ l, p ∣ q := by
  induction l with
  | nil => exact (hp.not_dvd_one (by simpa only [List.prod_nil] using h)).elim
  | cons a l ih =>
    rw [List.prod_cons, hp.dvd_mul] at h
    rcases h with h | h
    · exact ⟨a, List.mem_cons_self, h⟩
    · obtain ⟨q,hq,hpq⟩ := ih h
      exact ⟨q, List.mem_cons_of_mem a hq, hpq⟩

theorem freshPart_dvd (B : ℕ) {n : ℕ} (hn : 0 < n) : freshPart B n ∣ n := by
  have h := (List.filter_sublist (p := fun p : ℕ => decide (B < p)) (l := n.primeFactorsList)).prod_dvd_prod
  simpa [freshPart, Nat.prod_primeFactorsList hn.ne'] using h

theorem freshPart_prime_gt (B n : ℕ) {p : ℕ} (hp : p.Prime) (h : p ∣ freshPart B n) : B < p := by
  obtain ⟨q, hq, hpq⟩ := prime_dvd_list hp _ h
  obtain ⟨hqmem, hBq⟩ := List.mem_filter.mp hq
  have hprime := Nat.prime_of_mem_primeFactorsList hqmem
  have heq := (Nat.prime_dvd_prime_iff_eq hp hprime).mp hpq
  simpa [heq] using hBq

/-- Pang's RPL square shell. After the old factors are removed, at most one fresh
prime remains, to exponent one. This includes products of old primes with leftover 1. -/
theorem freshPart_square {B n : ℕ} (hn : 0 < n) (hbound : n ≤ B^2) :
    freshPart B n = 1 ∨ ((freshPart B n).Prime ∧ B < freshPart B n) := by
  let r := freshPart B n
  change r = 1 ∨ r.Prime ∧ B < r
  rcases eq_or_ne r 1 with h | h
  · exact Or.inl h
  right
  have hr := freshPart_dvd B hn
  have hpos : 0 < r := Nat.pos_of_dvd_of_pos hr hn
  have hle : r ≤ n := Nat.le_of_dvd hn hr
  have hpr : r.Prime := by
    by_contra hc
    have hlarge : B < r.minFac := freshPart_prime_gt B n (Nat.minFac_prime h) (Nat.minFac_dvd _)
    have hs := Nat.minFac_sq_le_self hpos hc
    nlinarith
  exact ⟨hpr, freshPart_prime_gt B n hpr (dvd_refl r)⟩

/-- The recorded prime factors at or below the frame include repeated occurrences. -/
def knownPart (B n : ℕ) : ℕ := (n.primeFactorsList.filter (fun p => p ≤ B)).prod

/-- Multiplicities stored on the old side and the fresh remainder reproduce the original. -/
theorem restore_prime_trace (B : ℕ) {n : ℕ} (hn : 0 < n) :
    knownPart B n * freshPart B n = n := by
  have split (l : List ℕ) :
      (l.filter (fun p => decide (p ≤ B))).prod *
        (l.filter (fun p => decide (B < p))).prod = l.prod := by
    induction l with
    | nil => simp
    | cons a l ih =>
      by_cases ha : a ≤ B
      · simp [ha, Nat.not_lt.mpr ha, mul_assoc, ih]
      · have hb : B < a := lt_of_not_ge ha
        simp only [List.filter_cons, ha, hb, decide_false, decide_true, Bool.false_eq_true,
          ↓reduceIte, List.prod_cons]
        rw [mul_left_comm, ih]
  exact (split n.primeFactorsList).trans (Nat.prod_primeFactorsList hn.ne')

/-- The first square to admit two copies of the next prime exhibits the lost guarantee. -/
theorem freshPart_prime_square {p B : ℕ} (hp : p.Prime) (hB : B < p) :
    freshPart B (p*p) = p*p := by
  unfold freshPart
  have h : ((p*p).primeFactorsList.filter fun q => decide (B < q)) = (p*p).primeFactorsList := by
    apply List.filter_eq_self.mpr
    intro q hq
    have hprime := Nat.prime_of_mem_primeFactorsList hq
    have hdiv := Nat.dvd_of_mem_primeFactorsList hq
    have hqp : q ∣ p := by simpa only [hprime.dvd_mul, or_self] using hdiv
    have heq := (Nat.prime_dvd_prime_iff_eq hprime hp).mp hqp
    simpa [heq] using hB
  rw [h, Nat.prod_primeFactorsList (Nat.mul_ne_zero hp.ne_zero hp.ne_zero)]

/-- The actual stripped arithmetic supplies the two frames and their reversible readout. -/
theorem square_shell_readout {B n : ℕ} (hn : 0 < n) (within : n ≤ B^2) (k : ℕ) :
    let a := knownPart B n
    let p := freshPart B n
    a*p = n ∧ (p = 1 ∨ (p.Prime ∧ B < p ∧ a ≤ B)) ∧
      (p : ℚ)*turn n k - turn a k = (((k/a)%p : ℕ) : ℚ) := by
  have restore := restore_prime_trace B hn
  have both : 0 < knownPart B n * freshPart B n := restore.symm ▸ hn
  have ha : 0 < knownPart B n := Nat.pos_of_ne_zero (fun hz => by simp [hz] at both)
  have hp : 0 < freshPart B n := Nat.pos_of_ne_zero (fun hz => by simp [hz] at both)
  refine ⟨restore, ?_, ?_⟩
  · rcases freshPart_square hn within with h | ⟨hprime, hgt⟩
    · exact Or.inl h
    · refine Or.inr ⟨hprime, hgt, ?_⟩
      by_contra! hlarge
      have hle := Nat.mul_le_mul (show B+1 ≤ knownPart B n by omega)
        (show B+1 ≤ freshPart B n by omega)
      nlinarith
  · simpa only [restore] using quotient_turn ha hp k

end PALRH
