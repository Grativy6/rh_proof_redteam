import PALRH.PascalBoard
import Mathlib.Data.Nat.Choose.Factorization

open Finset
open scoped BigOperators

namespace PALRH.PascalCarry
open PascalBoard

private theorem factorial_floor {m p : ℕ} (pp : p.Prime) (large : m<p^2) :
    m.factorial.factorization p=m/p := by
  rw [Nat.factorization_factorial pp (Nat.log_lt_of_lt_pow' (by decide : (2:ℕ)≠0) large)]
  simp [show Ico (1:ℕ) 2={1} by decide]

private theorem choose_floor {n p a : ℕ} (pp : p.Prime) (large : n<p^2) (ha : a≤n) :
    (n.choose a).factorization p+a/p+(n-a)/p=n/p := by
  have h:=congrArg (fun v : ℕ => v.factorization p) (Nat.choose_mul_factorial_mul_factorial ha)
  have cn:=(Nat.choose_pos ha).ne'
  have an:=(Nat.factorial_pos a).ne'
  have bn:=(Nat.factorial_pos (n-a)).ne'
  simp only [Nat.factorization_mul (mul_ne_zero cn an) bn,Nat.factorization_mul cn an,
    Finsupp.coe_add,Pi.add_apply,factorial_floor pp (ha.trans_lt large),
    factorial_floor pp ((Nat.sub_le _ _).trans_lt large),factorial_floor pp large] at h
  exact h

private theorem floor_triangle (q r p : ℕ) (pp : 0<p) (rp : r<p) :
    2*(∑ j ∈ range (q*p+r+1),j/p)+p*q=p*q^2+2*q*(r+1) := by
  have zero_block : (∑ j ∈ range p,j/p)=0 :=
    Finset.sum_eq_zero (fun j hj => Nat.div_eq_of_lt (mem_range.mp hj))
  induction q with
  | zero =>
    simp only [Nat.zero_mul,Nat.zero_add,Nat.mul_zero,pow_two,Nat.add_zero]
    have short : (∑ j ∈ range (r+1),j/p)=0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have := mem_range.mp hj
      exact Nat.div_eq_of_lt (by omega)
    simp [short]
  | succ q ih =>
    rw [show (q+1)*p+r+1=p+(q*p+r+1) by ring,Finset.sum_range_add,zero_block,zero_add]
    simp_rw [Nat.add_div_left _ pp]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const,Finset.card_range,smul_eq_mul,mul_one]
    nlinarith only [ih]

/-- For a large prime, the Pascal row supplies exactly q*(p-1-r) prime digits,
where n=q*p+r. -/
theorem digit_count {n p : ℕ} (pp : p.Prime) (large : n<p^2) :
    (subsetStates n).factorization p=(n/p)*(p-1-n%p) := by
  let q:=n/p
  let r:=n%p
  have rebuild : q*p+r=n := Nat.div_add_mod' n p
  have rm : r<p:=Nat.mod_lt n pp.pos
  have total : (subsetStates n).factorization p+2*(∑ j ∈ range (n+1),j/p)=(n+1)*q := by
    unfold subsetStates
    rw [Nat.factorization_prod_apply (fun a ha => (Nat.choose_pos
      (by have:=mem_range.mp ha;omega : a≤n)).ne')]
    have h : (∑ a ∈ range (n+1),((n.choose a).factorization p+a/p+(n-a)/p))=
        ∑ _ ∈ range (n+1),q := by
      apply Finset.sum_congr rfl
      intro a ha
      exact choose_floor pp large (Nat.le_of_lt_succ (mem_range.mp ha))
    have reflected:=Finset.sum_range_reflect (fun a : ℕ => a/p) (n+1)
    simp only [Nat.add_sub_cancel] at reflected
    rw [Finset.sum_add_distrib,Finset.sum_add_distrib,reflected] at h
    simp only [Finset.sum_const,Finset.card_range,smul_eq_mul] at h
    omega
  have floor_sum:=floor_triangle q r p pp.pos rm
  rw [rebuild] at floor_sum
  have right : (n+1)*q=p*q^2+q*(r+1) := by rw [←rebuild];ring
  have split : (p-1-r)+(r+1)=p := by omega
  have mulsplit:=congrArg (fun z : ℕ => q*z) split
  rw [Nat.mul_add] at mulsplit
  change _=q*(p-1-r)
  nlinarith only [total,floor_sum,right,mulsplit]

theorem leftovers_coprime (n : ℕ) : Nat.Coprime (oneWay n/shared n) (subsetStates n/shared n) := by
  have pn : 0<subsetStates n := Finset.prod_pos (fun a ha => Nat.choose_pos
    (by have:=mem_range.mp ha;omega))
  exact Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_right _ pn)

theorem exchange_iff (n : ℕ) : oneWay n/shared n≤subsetStates n/shared n ↔ oneWay n≤subsetStates n := by
  constructor
  · intro h
    have scaled:=Nat.mul_le_mul_right (shared n) h
    simpa only [shared,Nat.div_mul_cancel (Nat.gcd_dvd_left _ _),
      Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)] using scaled
  · exact Nat.div_le_div_right

theorem exchange_pays {n : ℕ} (pay : oneWay n/shared n≤subsetStates n/shared n) :
    PALRH.PrimeBand.inputCount n n.sqrt≤PALRH.PrimeBoard.capacity n := by
  have eq : PALRH.PrimeBand.retained n n.sqrt=(oneWay n)^2 := by
    unfold PALRH.PrimeBand.retained oneWay
    rw [←Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro p _
    rw [←pow_mul,Nat.mul_comm 2]
  unfold PALRH.PrimeBand.inputCount
  rw [eq]
  exact (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ((exchange_iff n).mp pay) 2)).trans
    (two_pascal_rows_fit n)

#print axioms PALRH.PascalCarry.digit_count
#print axioms PALRH.PascalCarry.leftovers_coprime
#print axioms PALRH.PascalCarry.exchange_pays
end PALRH.PascalCarry
