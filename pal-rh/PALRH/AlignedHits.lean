import PALRH.GapClock

open Finset
namespace PALRH.AlignedHits
open GapClock PrimeCopies

/-- All factorial frames which have reached their own size threshold divide the index. -/
def aligned (k : ℕ) : Prop := ∀ m : ℕ, m.factorial^m ≤ k → m.factorial ∣ k

/-- One can align more and more complete initial divisibility frames in every
subpower index window. The chosen rounded-up multiple satisfies the condition
at its own index, including a possible threshold crossed during the move. -/
theorem aligned_in_windows (q : ℕ) (qp : 0<q) :
    ∃ K : ℕ, ∀ k : ℕ, K≤k → ∃ j : ℕ, k≤j ∧ (j-k)^q≤k ∧ aligned j := by
  classical
  refine ⟨(2*q).factorial^(2*q)+1,?_⟩
  intro k late
  have kp : 0<k := by omega
  let S:Finset ℕ:=(range (2*k+1)).filter (fun m => m.factorial^m ≤ 2*k)
  have eligible (m : ℕ) (price : m.factorial^m≤2*k) : m∈S := by
    have bound : m≤2*k := by
      by_cases zero : m=0
      · omega
      exact (Nat.self_le_factorial m).trans ((Nat.le_self_pow zero _).trans price)
    exact mem_filter.mpr ⟨mem_range.mpr (by omega),price⟩
  have active := eligible (2*q) (by omega)
  have nonempty : S.Nonempty := ⟨_,active⟩
  let top:=S.max' nonempty
  have above : 2*q≤top := le_max' S _ active
  have topPrice : top.factorial^top≤2*k := (mem_filter.mp (max'_mem S nonempty)).2
  let F:=top.factorial
  have fp : 0<F := Nat.factorial_pos _
  have square : (F^q)^2≤2*k := by
    rw [←pow_mul,Nat.mul_comm q 2]
    exact (Nat.pow_le_pow_right fp above).trans topPrice
  have small : F^q ≤ k := by
    by_contra! bad
    have h:=Nat.pow_le_pow_left (show k+1≤F^q by omega) 2
    nlinarith only [h,square,Nat.zero_le (k^2)]
  have fits : F≤k := (Nat.le_self_pow qp.ne' _).trans small
  let j:=(k/F+1)*F
  have div:=Nat.mod_add_div k F
  have remLt:=Nat.mod_lt k fp
  have bounds : k≤j ∧ j≤k+F := by
    dsimp [j];rw [Nat.add_mul,Nat.one_mul,Nat.mul_comm (k/F) F];omega
  refine ⟨j,bounds.1,(Nat.pow_le_pow_left (by omega : j-k≤F) q).trans small,?_⟩
  intro m opened
  have atTop : m∈S := eligible m (by omega)
  exact (Nat.factorial_dvd_factorial (le_max' S _ atTop)).trans (dvd_mul_left F _)

theorem rh_of_aligned (K : ℕ)
    (paid : ∀ k : ℕ, K≤k → aligned k → pays 14 k) : RiemannHypothesis := by
  apply rh_of_subpower_hits
  intro q qp
  obtain ⟨A,windows⟩:=aligned_in_windows q qp
  refine ⟨max A K,?_⟩
  intro k late
  obtain ⟨j,after,width,frame⟩:=windows k ((le_max_left _ _).trans late)
  exact ⟨j,after,width,paid j (((le_max_right _ _).trans late).trans after) frame⟩

#print axioms PALRH.AlignedHits.aligned_in_windows
#print axioms PALRH.AlignedHits.rh_of_aligned
end PALRH.AlignedHits
