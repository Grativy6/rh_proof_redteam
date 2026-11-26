import PALRH.PascalBoard

open Finset
open scoped BigOperators

namespace PALRH.SharedPascal
open PascalBoard

/-- Two neighboring Pascal growth steps isolate a single consecutive-radix ratio. -/
theorem adjacent_rows (k : ℕ) :
    ((k+1)^(k+1))*(subsetStates (k+2)*subsetStates k) =
      ((k+2)^(k+1))*(subsetStates (k+1))^2 := by
  have prev:=next_row k
  have top:=next_row (k+1)
  have cancel : subsetStates (k+2)*(k+1).factorial=(k+2)^(k+1)*subsetStates (k+1) := by
    apply Nat.eq_of_mul_eq_mul_left (by omega : 0<k+2)
    rw [Nat.factorial_succ (k+1),pow_succ (k+2) (k+1)] at top
    nlinarith only [top]
  calc
    _ = subsetStates (k+2)*((k+1)^(k+1)*subsetStates k) := by ring
    _ = subsetStates (k+2)*(subsetStates (k+1)*(k+1).factorial) := by rw [prev]
    _ = (subsetStates (k+2)*(k+1).factorial)*subsetStates (k+1) := by ring
    _ = _ := by rw [cancel];ring

set_option maxRecDepth 10000 in
theorem twelve_fives :
    (subsetStates 2)^4*subsetStates 3*(subsetStates 5)^3 = (subsetStates 4)^2 * 5^12 := by decide +kernel

/-- Each fixed common state has the same number of remaining choices; both readings return. -/
theorem uniform_fiber {shared count r t : ℕ} (sp : 0<shared) (keep : r<shared) (free : t<count) :
    let k:=t*shared+r
    k<count*shared ∧ k%shared=r ∧ k/shared=t := by
  dsimp only
  have slot:=Nat.mul_le_mul_right shared (by omega : t+1≤count)
  rw [Nat.add_mul,Nat.one_mul] at slot
  exact ⟨by omega,by simp [Nat.add_comm,Nat.mod_eq_of_lt keep],
    by simp [Nat.add_comm,Nat.add_mul_div_right _ _ sp,Nat.div_eq_of_lt keep]⟩

theorem recover_both (rank shared : ℕ) :
    (rank/shared)*shared+rank%shared=rank := by
  simpa [Nat.mul_comm,Nat.add_comm] using Nat.mod_add_div rank shared

/-- A cutoff can select any collection of actual distances. Each admitted d requests n-d trips. -/
def trips (n j : ℕ) (tag : ℕ → Bool) :=
  ∑ d ∈ Icc j n, if tag d=true then n-d else 0

def slots (n j : ℕ) := (j-1)*(n+1-j)

private theorem triangle (j n : ℕ) (jn : j≤n) :
    2*(∑ d ∈ Icc j n,(n-d))=(n-j)*(n-j+1) := by
  induction n,jn using Nat.le_induction with
  | base => simp
  | succ k jk ih =>
    rw [sum_Icc_succ_top (by omega : j≤k+1),Nat.sub_self,add_zero]
    have layers : (∑ d ∈ Icc j k,(k+1-d))=(∑ d ∈ Icc j k,(k-d))+((k+1)-j) := by
      have each : (∑ d ∈ Icc j k,(k+1-d))=∑ d ∈ Icc j k,((k-d)+1) := by
        apply Finset.sum_congr rfl
        intro d hd
        have := (mem_Icc.mp hd).2
        omega
      rw [each,Finset.sum_add_distrib]
      simp [Nat.card_Icc]
    rw [layers,show k+1-j=(k-j)+1 by omega]
    nlinarith only [ih]

private theorem tail_upper (n j : ℕ) (tag : ℕ → Bool) :
    trips n j tag≤∑ d ∈ Icc j n,(n-d) := by
  unfold trips
  apply Finset.sum_le_sum
  intro d _
  split_ifs <;> omega

theorem upper_third {n j : ℕ} (positive : 0<j) (within : j≤n) (third : n+2≤3*j)
    (tag : ℕ → Bool) : trips n j tag≤slots n j := by
  have h:=Nat.mul_le_mul_left 2 (tail_upper n j tag)
  rw [triangle j n within] at h
  have u : n-j≤2*(j-1) := by omega
  have e:=Nat.mul_le_mul_right (n-j+1) u
  have sz : 2*((j-1)*(n+1-j))=2*(j-1)*(n-j+1) := by rw [show n+1-j=n-j+1 by omega];ring
  unfold slots
  omega

/-- The heights that can pay their own primitive step form one final interval. -/
theorem paid_above {n j k : ℕ} (jp : 0<j) (jk : j≤k) (kn : k≤n) (tag : ℕ → Bool)
    (paid : trips n j tag≤slots n j) : trips n k tag≤slots n k := by
  by_cases third : n+2≤3*k
  · exact upper_third (jp.trans_le jk) kn third tag
  have tails : trips n k tag≤trips n j tag := by
    unfold trips
    apply Finset.sum_le_sum_of_subset
    intro d hd
    exact mem_Icc.mpr ⟨jk.trans (mem_Icc.mp hd).1,(mem_Icc.mp hd).2⟩
  apply tails.trans (paid.trans ?_)
  unfold slots
  have kl : 1≤k := by omega
  have ju : j≤n+1 := by omega
  have ku : k≤n+1 := by omega
  have width : j+k≤n+2 := by omega
  zify [jp,kl,ju,ku]
  have ordered : (j:ℤ)≤k := by exact_mod_cast jk
  have edge : (j:ℤ)+k≤(n:ℤ)+2 := by exact_mod_cast width
  nlinarith only [mul_nonneg (sub_nonneg.mpr ordered) (sub_nonneg.mpr edge)]

#print axioms PALRH.SharedPascal.adjacent_rows
#print axioms PALRH.SharedPascal.twelve_fives
#print axioms PALRH.SharedPascal.uniform_fiber
#print axioms PALRH.SharedPascal.paid_above
end PALRH.SharedPascal
