import PALRH.DoubledPrice

open Finset
open scoped BigOperators
namespace PALRH.DivisorBracket

def slots := Icc 1 16

def upper (j : ℕ) : ℤ :=
  [0,102,-51,-34,0,-20,17,-15,1,0,8,-8,0,0,4,-1,-3].getD j 0

def lower (j : ℕ) : ℤ :=
  [0,-198,99,66,0,40,-29,21,3,0,-9,0,7,11,-8,-6,3].getD j 0

def first (c : ℕ → ℤ) : ℤ := ∑ j ∈ slots, (j:ℤ)*c j
def absolute (c : ℕ → ℤ) : ℤ := ∑ j ∈ slots, |c j| *(j:ℤ)^2

def reading (c : ℕ → ℤ) (k : ℕ) : ℤ :=
  -(k:ℤ)*first c + ∑ j ∈ slots, c j*(k%j:ℕ)*((j:ℤ)-(k%j:ℕ))

/-- The signed arrays have zero total. The finite checks fix the direction on
each initial integral address, and leave a positive coefficient for the tail. -/
theorem upper_data :
    (∑ j ∈ slots, upper j) = 0 ∧ first upper = -212 ∧ absolute upper = 6068 ∧
    ∀ k ∈ Icc 1 (200:ℕ), 204*((k:ℤ)-1) ≤ reading upper k := by decide +kernel

theorem lower_data :
    (∑ j ∈ slots, lower j) = 0 ∧ first lower = 378 ∧ absolute lower = 11906 ∧
    ∀ k ∈ Icc 1 (200:ℕ), (-396)*((k:ℤ)-1) ≤ reading lower k := by decide +kernel

private theorem tail (c : ℕ → ℤ) (k : ℕ) :
    -absolute c ≤ 4*(∑ j ∈ slots, c j*(k%j:ℕ)*((j:ℤ)-(k%j:ℕ))) := by
  rw [Finset.mul_sum, absolute, ← Finset.sum_neg_distrib]
  apply sum_le_sum
  intro j hj
  have jp : 0 < j := (mem_Icc.mp hj).1
  let r : ℤ := (k%j:ℕ)
  have rn : 0 ≤ r := Int.natCast_nonneg _
  have left : r ≤ j := by dsimp [r]; exact_mod_cast (Nat.mod_lt k jp).le
  have four : 4*r*(j-r) ≤ (j:ℤ)^2 := by nlinarith only [sq_nonneg ((j:ℤ)-2*r)]
  have lo := mul_le_mul_of_nonneg_right (neg_abs_le (c j)) (mul_nonneg rn (sub_nonneg.mpr left))
  have hi := mul_le_mul_of_nonneg_left four (abs_nonneg (c j))
  change -(|c j| *(j:ℤ)^2) ≤ 4*(c j*r*((j:ℤ)-r))
  nlinarith only [lo,hi]

theorem upper_address {k : ℕ} (hp : 0 < k) : 204*((k:ℤ)-1) ≤ reading upper k := by
  obtain ⟨_,f,a,early⟩ := upper_data
  by_cases small : k ≤ 200
  · exact early k (mem_Icc.mpr ⟨hp,small⟩)
  have kt : (201:ℤ) ≤ k := by exact_mod_cast (show 201 ≤ k by omega)
  have low := tail upper k
  rw [a] at low
  unfold reading
  rw [f]
  linarith only [low,kt]

theorem lower_address {k : ℕ} (hp : 0 < k) : (-396)*((k:ℤ)-1) ≤ reading lower k := by
  obtain ⟨_,f,a,early⟩ := lower_data
  by_cases small : k ≤ 200
  · exact early k (mem_Icc.mpr ⟨hp,small⟩)
  have kt : (201:ℤ) ≤ k := by exact_mod_cast (show 201 ≤ k by omega)
  have low := tail lower k
  rw [a] at low
  unfold reading
  rw [f]
  linarith only [low,kt]

/-- Twice j times the sum of the ramps at all multiples of j up to k. -/
private def multiple (j k : ℕ) : ℤ :=
  (j:ℤ)*(2*k*(k/j:ℕ)-(j:ℤ)*(k/j:ℕ)*((k/j:ℕ)+1))

private theorem multiple_mod (j k : ℕ) :
    multiple j k = (k:ℤ)^2 - j*k + (k%j:ℕ)*((j:ℤ)-(k%j:ℕ)) := by
  have eqn : ((k%j:ℕ):ℤ) + (j:ℤ)*(k/j:ℕ) = k := by exact_mod_cast Nat.mod_add_div k j
  unfold multiple
  rw [show ((k%j:ℕ):ℤ)=(k:ℤ)-j*(k/j:ℕ) from eq_sub_of_add_eq eqn]
  ring

private theorem multiple_succ (j k : ℕ) :
    multiple j (k+1) = multiple j k + 2*(j:ℤ)*(k/j:ℕ) := by
  unfold multiple
  by_cases dv : j ∣ k+1
  · have next := Nat.succ_div_of_dvd dv
    have e := Nat.div_mul_cancel dv
    rw [next] at e ⊢
    have split : ((k/j:ℕ):ℤ)*j+j=(k:ℤ)+1 := by
      have h : (((k/j:ℕ):ℤ)+1)*j=(k:ℤ)+1 := by exact_mod_cast e
      linarith only [h]
    simp only [Nat.cast_succ]
    linear_combination -2*(j:ℤ)*split
  · rw [Nat.succ_div_of_not_dvd dv]
    simp only [Nat.cast_succ]
    ring

private theorem integral_address (c : ℕ → ℤ) (zero : (∑ j ∈ slots, c j)=0) (k : ℕ) :
    (∑ j ∈ slots,c j*multiple j k) = reading c k := by
  simp_rw [multiple_mod]
  have point (j : ℕ) :
      c j*((k:ℤ)^2-j*k+(k%j:ℕ)*((j:ℤ)-(k%j:ℕ))) =
      (k:ℤ)^2*c j - k*((j:ℤ)*c j) + c j*(k%j:ℕ)*((j:ℤ)-(k%j:ℕ)) := by ring
  simp_rw [point]
  rw [sum_add_distrib, sum_sub_distrib, ←mul_sum, zero, mul_zero, zero_sub, ←mul_sum]
  unfold reading first
  ring

def cell (n d j : ℕ) : ℤ :=
  (j:ℤ)*∑ m ∈ Icc 1 (n/(d*j)), ((n:ℤ)-(d*j*m:ℕ))

private theorem double_sum (x y L : ℕ) :
    2*(∑ m ∈ Icc 1 L, ((x:ℤ)-(y*m:ℕ))) =
      2*(x:ℤ)*L-(y:ℤ)*L*(L+1) := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [sum_Icc_succ_top (by omega : 1 ≤ L+1),mul_add,ih]
    simp only [Nat.cast_succ, Nat.cast_mul]
    ring

private theorem interpolate (n d j : ℕ) :
    let k := n/d
    let e : ℤ := (n%d:ℕ)
    2*cell n d j = ((d:ℤ)-e)*multiple j k + e*multiple j (k+1) := by
  dsimp only
  rw [multiple_succ]
  unfold cell
  rw [←mul_assoc, mul_comm (2:ℤ) j, mul_assoc, double_sum, ←Nat.div_div_eq_div_mul]
  have split : ((n%d:ℕ):ℤ)+(d:ℤ)*(n/d:ℕ)=n := by exact_mod_cast Nat.mod_add_div n d
  unfold multiple
  simp only [Nat.cast_mul]
  linear_combination 2*(j:ℤ)*(n/d/j:ℕ)*split.symm

/-- An integer inequality at every integral quotient also holds between quotients.
The actual dividend is carried through its quotient and remainder. -/
theorem enclose_label (c : ℕ → ℤ) (s : ℤ) (zero : (∑ j ∈ slots,c j)=0)
    (addresses : ∀ k : ℕ, 0 < k → 2*s*((k:ℤ)-1) ≤ reading c k)
    {n d : ℕ} (dp : 0<d) (cap : d≤n) :
    s*((n:ℤ)-d) ≤ ∑ j ∈ slots, c j*cell n d j := by
  let k := n/d
  let e : ℤ := (n%d:ℕ)
  have kp : 0<k := Nat.div_pos cap dp
  have en : 0 ≤ e := Int.natCast_nonneg _
  have ed : e ≤ d := by dsimp [e]; exact_mod_cast (Nat.mod_lt n dp).le
  have split : e+(d:ℤ)*k=n := by dsimp [k,e]; exact_mod_cast Nat.mod_add_div n d
  have mix : 2*(∑ j ∈ slots,c j*cell n d j) =
      ((d:ℤ)-e)*reading c k + e*reading c (k+1) := by
    rw [←integral_address c zero k, ←integral_address c zero (k+1),
      mul_sum, mul_sum, mul_sum, ←sum_add_distrib]
    apply sum_congr rfl
    intro j _
    have h := interpolate n d j
    change 2*cell n d j = ((d:ℤ)-e)*multiple j k + e*multiple j (k+1) at h
    linear_combination c j*h
  have lo:=mul_le_mul_of_nonneg_left (addresses k kp) (sub_nonneg.mpr ed)
  have hi:=mul_le_mul_of_nonneg_left (addresses (k+1) (Nat.succ_pos _)) en
  push_cast at hi
  have pay := add_le_add lo hi
  rw [←mix] at pay
  have source : ((d:ℤ)-e)*(2*s*((k:ℤ)-1)) + e*(2*s*((k:ℤ)+1-1)) =
      2*s*((n:ℤ)-d) := by linear_combination 2*s*split
  rw [source] at pay
  linarith only [pay]

#print axioms PALRH.DivisorBracket.upper_address
#print axioms PALRH.DivisorBracket.lower_address
#print axioms PALRH.DivisorBracket.enclose_label
end PALRH.DivisorBracket
