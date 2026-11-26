import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

open Finset
open scoped BigOperators

namespace PALRH.SharedColumns

def total (price : ℕ → ℕ) (m : ℕ) := ∑ i ∈ range m,price i
def columns (x : ℕ) (price : ℕ → ℕ) (m : ℕ) := total price m ⌈/⌉ x
def opened (x : ℕ) (price : ℕ → ℕ) (i : ℕ) := columns x price (i+1)-columns x price i
def spare (x : ℕ) (price : ℕ → ℕ) (m : ℕ) := x*columns x price m-total price m
def records (n m : ℕ) (price : ℕ → ℕ) := ∑ i ∈ range m,(n-(i+1))*price i

theorem minimal {x m k : ℕ} (xp : 0<x) (price : ℕ → ℕ) :
    columns x price m≤k ↔ total price m≤x*k := ceilDiv_le_iff_le_mul xp

theorem cover {x : ℕ} (xp : 0<x) (price : ℕ → ℕ) (m : ℕ) :
    total price m≤x*columns x price m := (minimal xp price).mp le_rfl

theorem spare_small {x : ℕ} (xp : 0<x) (price : ℕ → ℕ) (m : ℕ) :
    spare x price m<x := by
  have h : x*columns x price m≤total price m+x-1 := by
    unfold columns;rw [Nat.ceilDiv_eq_add_pred_div,mul_comm]
    exact Nat.div_mul_le_self _ _
  unfold spare;omega

theorem column_step {x : ℕ} (xp : 0<x) (price : ℕ → ℕ) (i : ℕ) :
    columns x price i≤columns x price (i+1) := by
  apply (minimal xp price).mpr
  apply le_trans _ (cover xp price (i+1))
  simp [total,sum_range_succ]

theorem all_opened {x : ℕ} (xp : 0<x) (price : ℕ → ℕ) (m : ℕ) :
    total (opened x price) m=columns x price m := by
  induction m with
  | zero => apply le_antisymm (by simp [total]) ((minimal xp price).mpr (by simp [total]))
  | succ m ih =>
    rw [total,sum_range_succ,←show total (opened x price) m=∑ i ∈ range m,opened x price i from rfl,ih,opened]
    have := column_step xp price m
    omega

private theorem triangle (n m : ℕ) (price : ℕ → ℕ) (mn : m≤n) :
    records n m price=(n-m)*total price m+∑ k ∈ range m,total price k := by
  induction m with
  | zero => simp [records,total]
  | succ m ih =>
    have old:=ih (by omega)
    rw [records,sum_range_succ,←show records n m price=∑ i ∈ range m,(n-(i+1))*price i from rfl,old]
    rw [sum_range_succ,show total price (m+1)=total price m+price m by simp [total,sum_range_succ]]
    have diff : n-m=(n-(m+1))+1 := by omega
    rw [diff];ring

/-- Every empty lane either belongs to a still-active row or to a row retired earlier. -/
theorem exact_residue {n m x : ℕ} (xp : 0<x) (mn : m≤n) (price : ℕ → ℕ) :
    x*records n m (opened x price)=records n m price+
      (n-m)*spare x price m+∑ k ∈ range m,spare x price k := by
  have eq (k : ℕ) : x*columns x price k=total price k+spare x price k := by
    have := cover xp price k;unfold spare;omega
  rw [triangle n m _ mn,triangle n m _ mn,mul_add,Finset.mul_sum]
  simp_rw [all_opened xp]
  rw [show x*((n-m)*columns x price m)=(n-m)*(x*columns x price m) by ring,eq]
  simp_rw [eq]
  rw [sum_add_distrib];ring

theorem one_column_per_row {n m x : ℕ} (xp : 0<x) (mn : m≤n) (price : ℕ → ℕ) :
    records n m price≤x*records n m (opened x price) ∧
    x*records n m (opened x price)≤records n m price+n*(x-1) := by
  rw [exact_residue xp mn]
  have cut : ∀ i, spare x price i≤x-1 := fun i => by have :=spare_small xp price i;omega
  have frozen : (∑ i ∈ range m,spare x price i)≤m*(x-1) := by
    calc
      _ ≤ ∑ _ ∈ range m,(x-1) := sum_le_sum (fun i _ => cut i)
      _ = _ := by simp
  have openRows:=Nat.mul_le_mul_left (n-m) (cut m)
  have restored : (n-m)*(x-1)+m*(x-1)=n*(x-1) := by rw [←add_mul,Nat.sub_add_cancel mn]
  omega

/-- The quotient and lane of the arriving record are available and undo exactly. -/
theorem address {x m t : ℕ} (xp : 0<x) (price : ℕ → ℕ) (ht : t<price m) :
    let rank:=total price m+t
    rank/x<columns x price (m+1) ∧ rank%x<x ∧ rank/x*x+rank%x=rank := by
  dsimp only
  have h:=cover xp price (m+1)
  rw [show total price (m+1)=total price m+price m by simp [total,sum_range_succ]] at h
  refine ⟨(Nat.div_lt_iff_lt_mul xp).mpr ?_,Nat.mod_lt _ xp,Nat.div_add_mod' _ _⟩
  rw [mul_comm];omega

#print axioms PALRH.SharedColumns.exact_residue
#print axioms PALRH.SharedColumns.one_column_per_row
#print axioms PALRH.SharedColumns.address
end PALRH.SharedColumns
