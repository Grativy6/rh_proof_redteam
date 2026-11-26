import PALRH.ColoredSquares
import PALRH.DoubledRuler

open Finset
open scoped BigOperators
namespace PALRH.RulerBalance
open DoubledRuler SquareCarry

def weight (N d : ℕ) : ℤ := ∑ j ∈ Icc 1 (N/d), ink N (d*j)

private theorem sum_unit (m : ℕ) :
    (∑ d ∈ m.divisors,(ArithmeticFunction.moebius (m/d):ℝ))=if m=1 then 1 else 0 := by
  rw [Nat.sum_div_divisors m (fun k=>(ArithmeticFunction.moebius k:ℝ))]
  have eq:=DFunLike.congr_fun ArithmeticFunction.moebius_mul_coe_zeta m
  rw [ArithmeticFunction.coe_mul_zeta_apply,ArithmeticFunction.one_apply] at eq
  by_cases one : m=1 <;> simp only [one,if_true,if_false] at eq ⊢ <;> exact_mod_cast eq

/-- All multiple addresses collapse to the original first mark when the actual
Möbius signs are applied before regrouping. -/
theorem first_mark {N : ℕ} (pos : 0<N) :
    (∑ d ∈ Icc 1 N, ArithmeticFunction.moebius d*weight N d)=ink N 1 := by
  have g:=FactorialReturn.products N (fun d=>(ArithmeticFunction.moebius d:ℝ))
    (fun _=>1) (fun m=>(ink N m:ℝ))
  simp only [one_mul,sum_unit] at g
  have single : (∑ m ∈ Icc 1 N,(if m=1 then (1:ℝ) else 0)*(ink N m:ℝ))=(ink N 1:ℝ) := by
    rw [sum_eq_single 1]
    · simp
    · intro m _ diff;simp [diff]
    · exact fun no=>False.elim (no (mem_Icc.mpr ⟨le_rfl,pos⟩))
  rw [single] at g
  unfold weight
  exact_mod_cast g

private theorem add_rows (u : ℕ → ℤ) (N : ℕ) :
    (∑ j ∈ Icc 1 N, walk j*(u j-u (j+1)))+walk N*u (N+1)=
      ∑ j ∈ Icc 1 N, ArithmeticFunction.moebius j*u j := by
  induction N with
  | zero => simp [walk]
  | succ N old =>
    rw [sum_Icc_succ_top (by omega : 1≤N+1),sum_Icc_succ_top (by omega : 1≤N+1)]
    have next : walk (N+1)=walk N+ArithmeticFunction.moebius (N+1) := by
      unfold walk
      rw [sum_Icc_succ_top (by omega : 1≤N+1)]
    rw [next]
    linarith only [old, show
      (walk N+ArithmeticFunction.moebius (N+1))*(u (N+1)-u (N+1+1))+
      (walk N+ArithmeticFunction.moebius (N+1))*u (N+1+1)=
      walk N*u (N+1)+ArithmeticFunction.moebius (N+1)*u (N+1) by ring]

theorem signed_balance {N : ℕ} (pos : 0<N) :
    (∑ j ∈ Icc 1 N, walk j*(weight N j-weight N (j+1)))=ink N 1 := by
  have final : weight N (N+1)=0 := by simp [weight,Nat.div_eq_of_lt (Nat.lt_succ_self N)]
  have balance:=add_rows (weight N) N
  rw [final,mul_zero,add_zero,first_mark pos] at balance
  exact balance

#print axioms PALRH.RulerBalance.first_mark
#print axioms PALRH.RulerBalance.signed_balance
end PALRH.RulerBalance
