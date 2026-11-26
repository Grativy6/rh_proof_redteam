import PALRH.OneSidedBoard

open Finset
open scoped BigOperators
namespace PALRH.DoubledRuler

/-- The signed weight of one ordinary integer on a board of size N. -/
def ink (N m : ℕ) : ℤ := ((N:ℤ)-m)^5 * (7*(m:ℤ)-N)

/-- The registers addressed by multiples of d, after returning the original ramp. -/
def extra (n d : ℕ) : ℤ :=
  (∑ j ∈ Icc 1 (2*n/d), ink (2*n) (d*j)) - ((2*n:ℕ):ℤ)^5 * (n-d:ℕ)

/-- Keep first powers of primes strictly past the seven-eighths cutoff. -/
def primeSettings (n : ℕ) : ℕ :=
  ∏ d ∈ Icc 1 (2*n), if d.Prime ∧ n^7 < d^8 then d^(extra n d).toNat else 1

/-- Each cell of the inner square receives n clock ticks. -/
def ticks (k : ℕ) : ℕ := (2*k^4)^5 * k^4 * (k^4-k^2)^2

private def remainder (m d r : ℤ) :=
  d^6*m*(4*m^2-1) + 12*r*d^5*m^2 +
    15*m*r^2*d^2*(d^2-r^2) + 6*m*r^5*(3*d-r) + 3*r^5*(2*d-r)

/-- Finite polynomial summation with the last, incomplete address block retained. -/
private theorem ink_sum (N d m : ℕ) :
    6*(∑ j ∈ Icc 1 m, ink N (d*j)) =
      3*(N:ℤ)^6-6*(d:ℤ)*N^5+remainder m d ((N:ℤ)-d*m) := by
  induction m with
  | zero => simp [remainder]; ring
  | succ m ih =>
    rw [sum_Icc_succ_top (by omega : 1 ≤ m+1), mul_add, ih]
    unfold ink remainder
    push_cast
    ring

private theorem remainder_nonneg {m d r : ℤ} (hm : 1 ≤ m) (hr : 0 ≤ r) (hd : r ≤ d) :
    0 ≤ remainder m d r := by
  have dn : 0 ≤ d := hr.trans hd
  have mn : 0 ≤ m := by omega
  have first : 0 ≤ 4*m^2-1 := by nlinarith only [hm, sq_nonneg (m-1)]
  have square : 0 ≤ d^2-r^2 := by nlinarith only [mul_nonneg (sub_nonneg.mpr hd) (add_nonneg dn hr)]
  have triple : 0 ≤ 3*d-r := by omega
  have twice : 0 ≤ 2*d-r := by omega
  unfold remainder
  positivity

theorem extra_nonneg {n d : ℕ} (dp : 0 < d) (within : d ≤ 2*n) : 0 ≤ extra n d := by
  by_cases early : d ≤ n
  · let b := 2*n/d
    have bp : 0 < b := Nat.div_pos within dp
    have division := Nat.mod_add_div (2*n) d
    have rem : ((2*n%d:ℕ):ℤ) = (2*n:ℕ)-((d:ℤ)*b) := by
      dsimp [b]
      have h : ((2*n%d:ℕ):ℤ)+(d:ℤ)*(2*n/d:ℕ)=((2*n:ℕ):ℤ) := by exact_mod_cast division
      exact eq_sub_of_add_eq h
    have rpos : 0 ≤ remainder b d ((2*n:ℕ)-(d:ℤ)*b) := by
      rw [←rem]
      exact remainder_nonneg (by exact_mod_cast bp) (by positivity)
        (by exact_mod_cast (Nat.mod_lt (2*n) dp).le)
    have h := ink_sum (2*n) d b
    unfold extra
    rw [Nat.cast_sub early]
    dsimp [b] at h rpos
    push_cast at h rpos ⊢
    nlinarith only [h,rpos]
  · have m : 2*n/d = 1 := by
      have one := Nat.div_pos within dp
      have two := (Nat.div_lt_iff_lt_mul dp).mpr (show 2*n < 2*d by omega)
      omega
    have dN : (d:ℤ) ≤ 2*n := by exact_mod_cast within
    have large : (n:ℤ) < d := by exact_mod_cast (Nat.lt_of_not_ge early)
    unfold extra
    have nd : n ≤ d := by omega
    simp only [m, Icc_self, sum_singleton, mul_one, Nat.sub_eq_zero_of_le nd,
      Nat.cast_zero, mul_zero, sub_zero, ink, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
    exact mul_nonneg (pow_nonneg (sub_nonneg.mpr dN) _) (by linarith)

open LinearPrimeIntegral QuarticBoards

noncomputable def ordinary (N : ℕ) : ℝ :=
  ∑ m ∈ Icc 1 N, Real.log m * (ink N m : ℝ)

theorem original_and_return (n : ℕ) :
    ordinary (2*n) = ((2*n:ℕ):ℝ)^5 * fullWalk n +
      ∑ d ∈ Icc 1 (2*n), ArithmeticFunction.vonMangoldt d*(extra n d:ℝ) := by
  let N := 2*n
  have grouped := FactorialReturn.products N (fun d => ArithmeticFunction.vonMangoldt d)
    (fun _ => 1) (fun m => (ink N m:ℝ))
  simp only [one_mul] at grouped
  have source (m : ℕ) : (∑ d ∈ m.divisors, ArithmeticFunction.vonMangoldt (m/d))=Real.log m := by
    rw [Nat.sum_div_divisors m (fun d => ArithmeticFunction.vonMangoldt d), ArithmeticFunction.vonMangoldt_sum]
  simp_rw [source] at grouped
  have base : (∑ d ∈ Icc 1 N, ArithmeticFunction.vonMangoldt d*((n-d:ℕ):ℝ))=fullWalk n := by
    calc
      _ = ∑ d ∈ Icc 1 n, ArithmeticFunction.vonMangoldt d*((n-d:ℕ):ℝ) := by
        symm
        apply Finset.sum_subset (fun d h => mem_Icc.mpr ⟨(mem_Icc.mp h).1,(mem_Icc.mp h).2.trans (by dsimp [N];omega)⟩)
        intro d hd out
        have dp := (mem_Icc.mp hd).1
        have dn : n ≤ d := by by_contra! z; exact out (mem_Icc.mpr ⟨by omega, z.le⟩)
        simp [Nat.sub_eq_zero_of_le dn]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro d hd
        rw [Nat.cast_sub (mem_Icc.mp hd).2, mul_comm]
  change ordinary N = (N:ℝ)^5 * fullWalk n + _
  rw [←base, Finset.mul_sum, ←Finset.sum_add_distrib]
  unfold ordinary
  rw [←grouped]
  apply Finset.sum_congr rfl
  intro d _
  unfold extra
  dsimp [N]
  push_cast
  ring

end PALRH.DoubledRuler
