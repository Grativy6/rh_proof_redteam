import PALRH.SharedColumns
import PALRH.SignedStrip

open Finset
open scoped BigOperators

noncomputable section
namespace PALRH.ProductClock
open ShapeObservation ReturnedHorizon

/-- The least number of multiplications by (x+1)/x covering a positive integer q. -/
def clock (x q : ℕ) := TickBoard.ticks q x q

private theorem pays {x q : ℕ} (xp : 0<x) : q*x^(clock x q)≤(x+1)^(clock x q) :=
  TickBoard.tick_cover xp le_rfl

private theorem stays_paid {x q i j : ℕ} (ij : i≤j) (pay : q*x^i≤(x+1)^i) :
    q*x^j≤(x+1)^j := by
  obtain ⟨v,rfl⟩:=Nat.exists_eq_add_of_le ij
  rw [pow_add,pow_add,←mul_assoc]
  exact Nat.mul_le_mul pay (Nat.pow_le_pow_left (Nat.le_succ _) _)

private theorem misses {x q i : ℕ} (early : i<clock x q) : (x+1)^i<q*x^i := by
  by_contra! pay
  exact (not_le_of_gt early) (TickBoard.ticks_le_of_price pay)

theorem integer_test {x q h : ℕ} (xp : 0<x) : clock x q≤h ↔ q*x^h≤(x+1)^h :=
  ⟨fun early => stays_paid early (pays xp),fun pay => TickBoard.ticks_le_of_price pay⟩

@[simp] theorem clock_one (x : ℕ) : clock x 1=0 :=
  Nat.eq_zero_of_le_zero (TickBoard.ticks_le_of_price (t:=0) (by simp))

/-- Concatenation saves exactly zero or one of the separate covering ticks. -/
theorem concatenate {x a b : ℕ} (xp : 0<x) (ap : 0<a) (bp : 0<b) :
    clock x (a*b)≤clock x a+clock x b ∧ clock x a+clock x b≤clock x (a*b)+1 := by
  constructor
  · apply (integer_test xp).mpr
    rw [pow_add,pow_add,show a*b*(x^clock x a*x^clock x b)=(a*x^clock x a)*(b*x^clock x b) by ring]
    exact Nat.mul_le_mul (pays xp) (pays xp)
  · cases ca : clock x a with
    | zero =>
      have q:=pays (q:=a) xp;rw [ca] at q;simp at q
      have one : a=1 := by omega
      simp [one]
    | succ i =>
      cases cb : clock x b with
      | zero =>
        have q:=pays (q:=b) xp;rw [cb] at q;simp at q
        have one : b=1 := by omega
        simp [one,ca]
      | succ k =>
        have h:=misses (x:=x) (q:=a) (show i<clock x a by omega)
        have v:=misses (x:=x) (q:=b) (show k<clock x b by omega)
        have short : (x+1)^(i+k)<a*b*x^(i+k) := by
          rw [pow_add,pow_add,show a*b*(x^i*x^k)=(a*x^i)*(b*x^k) by ring]
          exact (Nat.mul_lt_mul_of_pos_right h (pow_pos (by omega) _)).trans_le
            (Nat.mul_le_mul_left _ v.le)
        have later : i+k<clock x (a*b) := lt_of_not_ge (fun h => (not_le_of_gt short) ((integer_test xp).mp h))
        omega

def label (n d : ℕ) := if 2≤d ∧ d.gcd n.sqrt.factorial=1 then d else 1
def product (n m : ℕ) := ∏ d ∈ Icc 1 m,label n d
def tickSum (n m : ℕ) := ∑ d ∈ Icc 1 m,tickAt n d

private theorem label_pos (n d : ℕ) : 0<label n d := by
  unfold label;split_ifs with h <;> omega

private theorem tick_eq {n d : ℕ} (np : 0<n) (dn : d≤n) : tickAt n d=clock n.sqrt (label n d) := by
  by_cases good : 2≤d ∧ d.gcd n.sqrt.factorial=1
  · simp only [tickAt,label,if_pos good]
    apply Nat.le_antisymm
    · exact TickBoard.ticks_le_of_price (pays (Nat.sqrt_pos.mpr np))
    · exact (integer_test (Nat.sqrt_pos.mpr np)).mpr (TickBoard.tick_cover (Nat.sqrt_pos.mpr np) dn)
  · simp [tickAt,label,good]

theorem cumulative_rounding (n m : ℕ) (np : 0<n) (mn : m≤n) :
    clock n.sqrt (product n m)≤tickSum n m ∧ tickSum n m≤clock n.sqrt (product n m)+m := by
  induction m with
  | zero => simp [product,tickSum]
  | succ m ih =>
    obtain ⟨old,back⟩:=ih (by omega)
    have q : 0<product n m := prod_pos (fun i _ => label_pos n i)
    obtain ⟨lo,hi⟩:=concatenate (Nat.sqrt_pos.mpr np) q (label_pos n (m+1))
    have first : product n (m+1)=product n m*label n (m+1) := by
      unfold product;rw [prod_Icc_succ_top (by omega : 1≤m+1)]
    have second : tickSum n (m+1)=tickSum n m+tickAt n (m+1) := by
      unfold tickSum;rw [sum_Icc_succ_top (by omega : 1≤m+1)]
    rw [first,second,tick_eq np mn]
    omega

/-- All original per-prime ticks fit per row if the cumulative product price passes
one rational-power comparison. m is a valid simple reserve for discarded ticks. -/
theorem from_one_product {n m h : ℕ} (np : 0<n) (mn : m≤n)
    (fit : product n m*n.sqrt^h≤(n.sqrt+1)^h) : tickSum n m≤h+m := by
  exact ((cumulative_rounding n m np mn).2).trans (Nat.add_le_add_right ((integer_test (Nat.sqrt_pos.mpr np)).mpr fit) _)

#print axioms PALRH.ProductClock.concatenate
#print axioms PALRH.ProductClock.cumulative_rounding
#print axioms PALRH.ProductClock.from_one_product
end PALRH.ProductClock
