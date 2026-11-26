import PALRH.PrimeBand
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Algebra.Order.Ring.Pow

open Finset
open scoped BigOperators

namespace PALRH.PascalBoard
open PrimeBoard

/-- Choose one subset of every cardinality from zero through n. -/
def subsetStates (n : ℕ) := ∏ j ∈ range (n+1),n.choose j

theorem next_row (n : ℕ) :
    subsetStates (n+1)*(n+1).factorial=(n+1)^(n+1)*subsetStates n := by
  unfold subsetStates
  rw [Finset.prod_range_succ' (fun j => (n+1).choose j) (n+1),Nat.choose_zero_right,mul_one,
    Nat.factorial_eq_prod_range_add_one,←Finset.prod_mul_distrib]
  simp_rw [←Nat.add_one_mul_choose_eq]
  simp [Finset.prod_mul_distrib]

private noncomputable def step (n : ℕ) : ℝ := (((n:ℝ)+1)/n)^n
private noncomputable def room (n : ℕ) : ℝ := (n:ℝ)^n/n.factorial

private theorem step_pos {n : ℕ} (np : 0<n) : 0<step n := by
  unfold step;positivity

private theorem room_pos {n : ℕ} (np : 0<n) : 0<room n := by
  unfold room;positivity

private theorem room_next {n : ℕ} (np : 0<n) : room (n+1)=room n*step n := by
  have nz : (n:ℝ)≠0 := by exact_mod_cast np.ne'
  have fp : (n.factorial:ℝ)≠0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  unfold room step
  rw [Nat.factorial_succ]
  push_cast
  rw [div_pow,pow_succ]
  field_simp

private theorem subset_next_real (n : ℕ) : (subsetStates (n+1):ℝ)=(subsetStates n:ℝ)*room (n+1) := by
  have h:=next_row n
  have fp : (0:ℝ)<(n+1).factorial := by exact_mod_cast Nat.factorial_pos (n+1)
  unfold room
  rw [←mul_div_assoc,eq_div_iff fp.ne']
  exact_mod_cast (h.trans (Nat.mul_comm _ _))

private theorem step_increases {n : ℕ} (np : 0<n) : step n≤step (n+1) := by
  let a:ℝ:=((n:ℝ)+1)/n
  let b:ℝ:=((n:ℝ)+2)/((n:ℝ)+1)
  let u:ℝ:=(n:ℝ)+1
  have nr : 0<(n:ℝ) := by exact_mod_cast np
  have up : 0<u := by dsimp [u];positivity
  have ap : 0<a := by dsimp [a];positivity
  have bp : 0<b := by dsimp [b];positivity
  have frac : b/a=1-1/u^2 := by dsimp [a,b,u];field_simp;ring
  have one : 1≤u := by dsimp [u];linarith
  have invb : 1/u^2≤1 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith only [one,sq_nonneg (u-1)]
  have bern:=one_add_mul_le_pow (by linarith : (-2:ℝ)≤ -(1/u^2)) n
  have gain : 1≤(b/a)^n*b := by
    rw [frac]
    have mulw:=mul_le_mul_of_nonneg_right bern bp.le
    have low : (1+(n:ℝ)* -(1/u^2))*b=1+1/u^3 := by dsimp [u,b];field_simp;ring
    rw [low,show 1+ -(1/u^2)=1-1/u^2 by ring] at mulw
    linarith only [mulw,show 0≤1/u^3 by positivity]
  have raised:=mul_le_mul_of_nonneg_right gain (pow_nonneg ap.le n)
  have sx : (b/a)^n*b*a^n=b^(n+1) := by
    rw [div_pow,pow_succ]
    field_simp
  rw [sx,one_mul] at raised
  unfold step
  push_cast
  simpa only [a,b,show (n:ℝ)+1+1=(n:ℝ)+2 by ring] using raised

private theorem room_paid (k : ℕ) : room (k+1)≤(step (k+1))^k := by
  induction k with
  | zero => norm_num [room]
  | succ k ih =>
    rw [room_next (Nat.succ_pos k)]
    calc
      _ ≤ (step (k+1))^k*step (k+1) :=
        mul_le_mul_of_nonneg_right ih (step_pos (Nat.succ_pos k)).le
      _ = (step (k+1))^(k+1) := (pow_succ _ _).symm
      _ ≤ _ := pow_le_pow_left₀ (step_pos (Nat.succ_pos k)).le (step_increases (Nat.succ_pos _)) _

private theorem subset_paid (k : ℕ) : (subsetStates (k+1):ℝ)^2≤(room (k+1))^(k+1) := by
  induction k with
  | zero => norm_num [room,subsetStates,Finset.prod_range_succ]
  | succ k ih =>
    have lift : (room (k+1))^(k+1)≤(room (k+2))^k := by
      rw [room_next (Nat.succ_pos k),mul_pow,pow_succ]
      exact mul_le_mul_of_nonneg_left (room_paid k) (pow_nonneg (room_pos (Nat.succ_pos k)).le _)
    rw [subset_next_real (k+1),mul_pow]
    calc
      _ ≤ (room (k+2))^k*(room (k+2))^2 :=
        mul_le_mul_of_nonneg_right (ih.trans lift) (by positivity)
      _ = _ := (pow_add _ _ _).symm

/-- Two full independent rows of subset choices and all n row permutations fit for every n. -/
theorem two_pascal_rows_fit (n : ℕ) :
    n.factorial^n*(subsetStates n)^2 ≤ capacity n := by
  cases n with
  | zero => decide
  | succ k =>
    have paid:=subset_paid k
    unfold room at paid
    rw [div_pow,le_div_iff₀ (by positivity)] at paid
    unfold capacity
    rw [pow_two (k+1), pow_mul]
    exact_mod_cast (show ((k+1).factorial:ℝ)^(k+1)*(subsetStates (k+1):ℝ)^2 ≤
      ((((k+1:ℕ):ℝ)^(k+1))^(k+1)) by simpa only [mul_comm] using paid)

/-- One forward digit per prime interval. A second independent packet carries the reverse trips. -/
def oneWay (n : ℕ) := ∏ p ∈ (primes n).filter (fun p => n.sqrt<p),p^(n-p)

def shared (n : ℕ) := (oneWay n).gcd (subsetStates n)

theorem registered_digits_fit (n : ℕ) : n.factorial^n*(shared n)^2≤capacity n := by
  have pos : 0<subsetStates n := Finset.prod_pos (fun j hj => Nat.choose_pos
    (by have:=mem_range.mp hj;omega))
  have small : shared n≤subsetStates n := Nat.le_of_dvd pos (Nat.gcd_dvd_right _ _)
  exact (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left small 2)).trans (two_pascal_rows_fit n)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 1500000 in
theorem sixteen_lacks_175 : oneWay 16/shared 16=175 := by decide +kernel

#print axioms PALRH.PascalBoard.next_row
#print axioms PALRH.PascalBoard.two_pascal_rows_fit
#print axioms PALRH.PascalBoard.registered_digits_fit
#print axioms PALRH.PascalBoard.sixteen_lacks_175
end PALRH.PascalBoard
