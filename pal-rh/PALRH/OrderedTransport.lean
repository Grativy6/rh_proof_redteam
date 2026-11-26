import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Finset.Sigma

open Finset
open scoped BigOperators

namespace PALRH.OrderedTransport

/-- The next free ordinal after placing the first j groups as early as their respective windows permit. -/
def finish (left mass : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k+1 => max (finish left mass k) (left k)+mass k

def firstSlot (left mass : ℕ → ℕ) (i : ℕ) := max (finish left mass i) (left i)

private theorem past (left mass : ℕ → ℕ) {i j : ℕ} (order : i≤j) :
    left i+∑ k ∈ Icc i j,mass k ≤ finish left mass (j+1) := by
  induction j,order using Nat.le_induction with
  | base => simp [finish]
  | succ j ij ih =>
    rw [sum_Icc_succ_top (by omega : i≤j+1),←Nat.add_assoc]
    change _≤max (finish left mass (j+1)) (left (j+1))+mass (j+1)
    exact Nat.add_le_add_right (ih.trans (le_max_left _ _)) _

private theorem tight (left mass : ℕ → ℕ) (j : ℕ) :
    ∃ i≤j, finish left mass (j+1)=left i+∑ k ∈ Icc i j,mass k := by
  induction j with
  | zero => exact ⟨0,le_rfl,by simp [finish]⟩
  | succ j ih =>
    by_cases reset : finish left mass (j+1)≤left (j+1)
    · refine ⟨j+1,le_rfl,?_⟩
      change max (finish left mass (j+1)) _+_ = _
      rw [max_eq_right reset,Icc_self,sum_singleton]
    · obtain ⟨i,ij,h⟩:=ih
      refine ⟨i,by omega,?_⟩
      change max (finish left mass (j+1)) _+_ = _
      rw [max_eq_left (le_of_not_ge reset),h,sum_Icc_succ_top (by omega : i≤j+1),Nat.add_assoc]

theorem interval_test (N : ℕ) (left right mass : ℕ → ℕ) :
    (∀ j<N, finish left mass (j+1)≤right j) ↔
    (∀ i j, i≤j → j<N → left i+∑ k ∈ Icc i j,mass k≤right j) := by
  constructor
  · intro cap i j ij jn
    exact (past left mass ij).trans (cap j jn)
  · intro all j jn
    obtain ⟨i,ij,h⟩:=tight left mass j
    rw [h];exact all i j ij jn

private theorem finish_mono (left mass : ℕ → ℕ) : Monotone (finish left mass) := by
  apply monotone_nat_of_le_succ
  intro j
  exact (le_max_left _ _).trans (Nat.le_add_right _ _)

theorem greedy_injection {N : ℕ} {left right mass : ℕ → ℕ}
    (bounds : ∀ i j, i≤j → j<N → left i+∑ k ∈ Icc i j,mass k≤right j) :
    (∀ i<N, ∀ t<mass i, firstSlot left mass i+t∈Ico (left i) (right i)) ∧
    (∀ i j : ℕ, ∀ t<mass i, ∀ u<mass j, firstSlot left mass i+t=firstSlot left mass j+u → i=j ∧ t=u) := by
  have go:= (interval_test N left right mass).mpr bounds
  have separated {i j t : ℕ} (ij : i<j) (under : t<mass i) :
      firstSlot left mass i+t<firstSlot left mass j := by
    calc
      _ < finish left mass (i+1) := Nat.add_lt_add_left under _
      _ ≤ finish left mass j := finish_mono left mass ij
      _ ≤ _ := le_max_left _ _
  constructor
  · intro i ni t ht
    apply mem_Ico.mpr
    exact ⟨(le_max_right _ _).trans (Nat.le_add_right _ _),
      (Nat.add_lt_add_left ht (firstSlot left mass i)).trans_le (go i ni)⟩
  · intro i j t ti u uj same
    rcases lt_trichotomy i j with smaller|eq|larger
    · have := separated smaller ti; omega
    · subst j; exact ⟨rfl,by omega⟩
    · have := separated larger uj;omega

/-- Each interval is an obstruction to every possible injection, even one that reorders labels. -/
theorem necessary_interval {N : ℕ} {left right mass : ℕ → ℕ} (ml : Monotone left)
    (mr : Monotone right) (valid : ∀ k<N, left k≤right k)
    (put : ℕ → ℕ → ℕ)
    (lands : ∀ k<N, ∀ t<mass k, put k t∈Ico (left k) (right k))
    (inj : ∀ i<N, ∀ j<N, ∀ t<mass i, ∀ u<mass j, put i t=put j u → i=j ∧ t=u)
    {i j : ℕ} (ij : i≤j) (jn : j<N) :
    left i+∑ k ∈ Icc i j,mass k≤right j := by
  let S:=(Icc i j).sigma (fun k => range (mass k))
  let target:=Ico (left i) (right j)
  have subset : ∀ a∈S, put a.1 a.2∈target := by
    intro a ha
    obtain ⟨row,digit⟩:=mem_sigma.mp ha
    have r:=mem_Icc.mp row
    have yes:=mem_Ico.mp (lands _ (r.2.trans_lt jn) _ (mem_range.mp digit))
    exact mem_Ico.mpr ⟨(ml r.1).trans yes.1,yes.2.trans_le (mr r.2)⟩
  have single : Set.InjOn (fun a : Σ _ : ℕ,ℕ => put a.1 a.2) (S:Set (Σ _ : ℕ,ℕ)) := by
    rintro ⟨a,t⟩ ha ⟨b,u⟩ hb eq
    obtain ⟨rowA,digA⟩:=mem_sigma.mp ha
    obtain ⟨rowB,digB⟩:=mem_sigma.mp hb
    obtain ⟨sameRow,samePosition⟩:=inj a ((mem_Icc.mp rowA).2.trans_lt jn)
      b ((mem_Icc.mp rowB).2.trans_lt jn) t (mem_range.mp digA) u (mem_range.mp digB) eq
    subst b;subst u;rfl
  have count:=Finset.card_le_card_of_injOn (fun a : Σ _ : ℕ,ℕ => put a.1 a.2) subset single
  simp [S,target,Nat.card_Ico] at count
  have ok:=(ml ij).trans (valid j jn)
  omega

#print axioms PALRH.OrderedTransport.interval_test
#print axioms PALRH.OrderedTransport.greedy_injection
#print axioms PALRH.OrderedTransport.necessary_interval
end PALRH.OrderedTransport
