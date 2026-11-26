import PALRH.ShapeObservation

open Finset
open scoped BigOperators

noncomputable section
namespace PALRH.PrefixReturn
open ShapeObservation

/-- Reference mass of the short distances deliberately omitted by the factorial test. -/
def smallReturn (n m : ℕ) := n.sqrt*plainArea n (min m n.sqrt)

theorem first_strip (n m : ℕ) (small : m≤n.sqrt) :
    prefixJobs n m+smallReturn n m=n.sqrt*plainArea n m := by
  have blank : prefixJobs n m=0 := by
    unfold prefixJobs
    apply sum_eq_zero
    intro d hd
    have hi: d≤n.sqrt := (mem_Icc.mp hd).2.trans small
    have dn:=hi.trans (Nat.sqrt_le_self n)
    have no : ¬(2≤d ∧ d.gcd n.sqrt.factorial=1) := by
      rintro ⟨lo,clean⟩
      exact (not_lt_of_ge hi) ((SieveFrame.factorial_test lo dn).mp clean).2
    simp [tickAt,no]
  simp [blank,smallReturn,min_eq_left small]

private def logAt (d : ℕ) : ℝ := if d.Prime then Real.log d else 0

private theorem sumLog (m : ℕ) : ∑ d ∈ Icc 1 m,logAt d=Chebyshev.theta m := by
  simp only [Chebyshev.theta,Nat.floor_natCast,←Finset.Icc_add_one_left_eq_Ioc,Nat.zero_add,
    Finset.sum_filter,logAt]

private theorem cut_sum (n m : ℕ) : ∑ d ∈ Icc 1 m,(if n.sqrt<d then logAt d else 0)=
    Chebyshev.theta m-Chebyshev.theta (min m n.sqrt:ℕ) := by
  have small : ∑ d ∈ Icc 1 m,(if d≤n.sqrt then logAt d else 0)=Chebyshev.theta (min m n.sqrt:ℕ) := by
    rw [←Finset.sum_filter,←sumLog]
    congr 1;ext d;simp only [mem_filter,mem_Icc,le_min_iff];tauto
  apply eq_sub_of_add_eq
  rw [←small,←sumLog,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  by_cases h:d≤n.sqrt <;> simp [h,show (n.sqrt<d) ↔ ¬d≤n.sqrt by omega]

/-- Replacing the discarded range by its measured prime weight leaves between zero and
three ticks per prefix site on average, even before passing to a limit. -/
theorem tick_remainder (n m : ℕ) (np : 0<n) (mn : m≤n) :
    let r := (∑ d ∈ Icc 1 m,(tickAt n d:ℝ)) -
      (n.sqrt:ℝ)*(Chebyshev.theta m-Chebyshev.theta (min m n.sqrt:ℕ))
    0≤r ∧ r≤3*m := by
  dsimp only
  rw [←cut_sum,Finset.mul_sum,←Finset.sum_sub_distrib]
  let err:=fun d : ℕ => (tickAt n d:ℝ)-(n.sqrt:ℝ)*(if n.sqrt<d then logAt d else 0)
  have each (d : ℕ) (hd : d∈Icc 1 m) : 0≤err d ∧ err d≤1+logAt d := by
    have dn:=(mem_Icc.mp hd).2.trans mn
    have xp:=Nat.sqrt_pos.mpr np
    have nonneg : 0≤logAt d := by
      unfold logAt;split_ifs with p
      · exact Real.log_nonneg (by exact_mod_cast p.one_le)
      · rfl
    by_cases good : 2≤d ∧ d.gcd n.sqrt.factorial=1
    · obtain ⟨prime,large⟩:=(SieveFrame.factorial_test good.1 dn).mp good.2
      simp [err,tickAt,good,large,logAt,prime]
      constructor
      · exact TickBoard.single_price xp prime.pos dn
      · nlinarith only [TickBoard.single_upper (n:=n) xp prime.pos]
    · by_cases p : d.Prime
      · have small : ¬n.sqrt<d := fun h => good ⟨p.two_le,
          (SieveFrame.factorial_test p.two_le dn).mpr ⟨p,h⟩⟩
        simp [err,good,tickAt,small]
        linarith only [nonneg]
      · simp [err,good,tickAt,logAt,p]
  change 0≤∑ d ∈ Icc 1 m,err d ∧ _ ≤ _
  refine ⟨sum_nonneg (fun d hd => (each d hd).1),?_⟩
  calc
    _ ≤ ∑ d ∈ Icc 1 m,(1+logAt d) := sum_le_sum (fun d hd => (each d hd).2)
    _ = (m:ℝ)+Chebyshev.theta m := by rw [sum_add_distrib,sumLog];simp
    _ ≤ _ := by linarith only [theta_price m]

#print axioms PALRH.PrefixReturn.first_strip
#print axioms PALRH.PrefixReturn.tick_remainder
end PALRH.PrefixReturn
