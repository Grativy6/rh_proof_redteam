import PALRH.Sieve

open Finset
open scoped BigOperators
noncomputable section
namespace PALRH.CarriedPrime

/-- Count a wrap at an actual positive row. -/
def jump (f : ℕ → ℚ) (n : ℕ) : ℚ := f (n-1)+f 1-f n

def detector (n : ℕ) (f : ℕ → ℚ) : ℚ :=
  ∑ a ∈ n.divisorsAntidiagonal, (ArithmeticFunction.moebius a.1:ℚ)*jump f a.2

private lemma jump_turn {d : ℕ} (hd : 2≤d) {n : ℕ} (hn : 0<n) :
    jump (turn d) n = if d ∣ n then 1 else 0 := by
  have first : turn d 1=1/(d:ℚ) := by simp [turn,Nat.mod_eq_of_lt (by omega : 1<d)]
  have hs := turn_step (show 0<d by omega) (n-1)
  rw [Nat.sub_add_cancel (show 1≤n by omega)] at hs
  unfold jump
  rw [first]
  linarith

/-- Möbius inversion singles out the coefficient at exactly one modulus. -/
theorem detector_turn {d n : ℕ} (hd : 0<d) (hn : 2≤n) :
    detector n (turn d) = if d=n then 1 else 0 := by
  by_cases one : d=1
  · subst d
    simp [detector,jump,turn,Nat.mod_one,show 1≠n by omega]
  · have forward : ∀ m>0, (∑ e ∈ m.divisors, if d=e then (1:ℚ) else 0) = jump (turn d) m := by
      intro m hm
      simp [jump_turn (by omega : 2≤d) hm,Nat.mem_divisors,hm.ne']
    exact ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mp forward n (by omega)

private lemma detector_sub (n : ℕ) (f g : ℕ → ℚ) :
    detector n (f-g) = detector n f - detector n g := by
  unfold detector
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  simp only [jump,Pi.sub_apply]
  ring

private lemma detector_smul (n : ℕ) (a : ℚ) (f : ℕ → ℚ) :
    detector n (a • f) = a*detector n f := by
  unfold detector
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  simp only [jump,Pi.smul_apply,smul_eq_mul]
  ring

/-- Normalized d-clock copies carry one coefficient from m to md. -/
def carry (d m : ℕ) (k : ℕ) : ℚ := (d:ℚ)*turn d (k/m)

theorem detector_carry {n m d : ℕ} (hn : 2≤n) (hm : 0<m) (hd : 2≤d) :
    detector n (carry d m) = (d:ℚ)*(if m*d=n then 1 else 0) - (if m=n then 1 else 0) := by
  have hd0 : 0<d := by omega
  have eq : carry d m = (d:ℚ) • turn (m*d)-turn m := by
    funext k
    simp only [carry,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,quotient_signal hm hd0 k]
    field_simp
  rw [eq,detector_sub,detector_smul,detector_turn (Nat.mul_pos hm hd0) hn,detector_turn hm hn]


/-- A normalized physical edge is the difference of the two integer remainders. -/
theorem physical_edge {d m : ℕ} (hd : 0<d) (hm : 0<m) (k : ℕ) :
    (m:ℚ)*carry d m k = ((k%(m*d):ℕ):ℚ)-((k%m:ℕ):ℚ) := by
  rw [carry,quotient_signal hm hd]
  unfold turn
  push_cast
  field_simp

/-- The two possible orders of doubling and tripling have identical physical response. -/
theorem square_path {m : ℕ} (hm : 0<m) (k : ℕ) :
    (m:ℚ)*carry 2 m k + ((m*2:ℕ):ℚ)*carry 3 (m*2) k =
    (m:ℚ)*carry 3 m k + ((m*3:ℕ):ℚ)*carry 2 (m*3) k := by
  rw [physical_edge (by decide) hm,physical_edge (by decide) (Nat.mul_pos hm (by decide)),
    physical_edge (by decide) hm,physical_edge (by decide) (Nat.mul_pos hm (by decide))]
  rw [show m*2*3=m*3*2 by ring]
  ring

/-- On any finite signed graph the physical reading depends only on the net
coefficient at each endpoint. Internal cycles have identically zero response. -/
theorem endpoint_evaluation {E V : Type*} [Fintype E] [Fintype V] [DecidableEq V]
    (src dst : E → V) (a : E → ℚ) (read : V → ℚ) :
    (∑ e, a e*(read (dst e)-read (src e))) =
      ∑ v, (∑ e, ((if dst e=v then a e else 0)-(if src e=v then a e else 0)))*read v := by
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  simp [sub_mul,ite_mul,Finset.sum_sub_distrib,mul_sub]

def shell (u : ℕ → ℕ → ℚ) (t : ℕ) : ℚ :=
  ∑ i ∈ Finset.range (t+1), u i (t-i)

def divergence (x y : ℕ → ℕ → ℚ) (i j : ℕ) : ℚ :=
  x i j+y i j-(if i=0 then 0 else x (i-1) j)-(if j=0 then 0 else y i (j-1))

private lemma next_shell (x y : ℕ → ℕ → ℚ) (t : ℕ) :
    shell (divergence x y) (t+1) =
      shell (fun i j => x i j+y i j) (t+1) - shell (fun i j => x i j+y i j) t := by
  have left : (∑ i ∈ Finset.range (t+1+1), (if i=0 then 0 else x (i-1) (t+1-i))) = shell x t := by
    rw [Finset.sum_range_succ']
    simp [shell]
  have right : (∑ i ∈ Finset.range (t+1+1), (if t+1-i=0 then 0 else y i (t+1-i-1))) = shell y t := by
    rw [Finset.sum_range_succ]
    simp only [Nat.sub_self,if_true,add_zero]
    apply Finset.sum_congr rfl
    intro i hi
    have lt := Finset.mem_range.mp hi
    rw [if_neg (by omega),show t+1-i-1=t-i by omega]
  unfold shell divergence
  rw [Finset.sum_sub_distrib,Finset.sum_sub_distrib,left,right]
  simp only [shell,Finset.sum_add_distrib]
  ring

/-- All internal two-clock edges cancel. Both outgoing readings on the last shell
sum to precisely the source retained by the whole triangle. -/
theorem triangle_conservation (x y : ℕ → ℕ → ℚ) (t : ℕ) :
    (∑ k ∈ Finset.range (t+1), shell (divergence x y) k) =
      shell (fun i j => x i j+y i j) t := by
  induction t with
  | zero => simp [shell,divergence]
  | succ t ih => rw [Finset.sum_range_succ,ih,next_shell]; ring

def spreadRight (R : ℚ) (i j : ℕ) : ℚ :=
  R*((i:ℚ)+1)/(((i:ℚ)+j+1)*((i:ℚ)+j+2))
def spreadUp (R : ℚ) (i j : ℕ) : ℚ := spreadRight R j i

/-- This rational split carries a single source through every layer with equal
total outgoing load at each node of the layer. -/
theorem spread_source (R : ℚ) (i j : ℕ) :
    divergence (spreadRight R) (spreadUp R) i j = if i=0 ∧ j=0 then R else 0 := by
  cases i <;> cases j <;>
    simp [divergence,spreadRight,spreadUp,Nat.cast_succ] <;> field_simp <;> ring

theorem spread_node (R : ℚ) (i j : ℕ) :
    spreadRight R i j+spreadUp R i j=R/((i:ℚ)+j+1) := by
  unfold spreadRight spreadUp
  unfold spreadRight
  field_simp
  ring

#print axioms PALRH.CarriedPrime.endpoint_evaluation
#print axioms PALRH.CarriedPrime.square_path
#print axioms PALRH.CarriedPrime.detector_carry
#print axioms PALRH.CarriedPrime.triangle_conservation
#print axioms PALRH.CarriedPrime.spread_source

/-- An exactly annihilated finite measurement gives a lower bound on the physical
quadratic loss of every profile sharing that measurement. -/
theorem finite_dual_floor {ι : Type*} (rows : Finset ι) (w z r : ι → ℝ)
    (positive : ∀ i ∈ rows, 0<w i) (nonzero : 0<∑ i ∈ rows, (z i)^2/w i) :
    (∑ i ∈ rows, z i*r i)^2/(∑ i ∈ rows, (z i)^2/w i) ≤ ∑ i ∈ rows, w i*(r i)^2 := by
  let u := ∑ i ∈ rows, z i*r i
  let v := ∑ i ∈ rows, (z i)^2/w i
  let a := u/v
  have term (i : ι) (hi : i ∈ rows) : 0 ≤ w i*(r i)^2 -
      2*a*(z i*r i)+a^2*((z i)^2/w i) := by
    have hw := positive i hi
    have eq : w i*(r i)^2-2*a*(z i*r i)+a^2*((z i)^2/w i) =
        w i*(r i-a*z i/w i)^2 := by field_simp; ring
    rw [eq]
    positivity
  have total := Finset.sum_nonneg term
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib, ←Finset.mul_sum, ←Finset.mul_sum] at total
  change 0 ≤ _ - 2*a*u+a^2*v at total
  have hv : 0<v := nonzero
  have identity : 2*a*u-a^2*v=u^2/v := by dsimp [a]; field_simp; ring
  change u^2/v ≤ _
  linarith

/-- Columns annihilated by a finite row observation can be varied independently
without changing that observation. -/
theorem invariant_observation {ι J : Type*} (rows : Finset ι) (cols : Finset J)
    (z r : ι → ℝ) (X : J → ι → ℝ) (b : J → ℝ)
    (blind : ∀ j ∈ cols, (∑ i ∈ rows, z i*X j i)=0) :
    (∑ i ∈ rows, z i*(r i-∑ j ∈ cols, b j*X j i)) = ∑ i ∈ rows, z i*r i := by
  simp only [mul_sub,Finset.mul_sum,Finset.sum_sub_distrib]
  rw [Finset.sum_comm (s:=rows) (t:=cols)]
  have empty : (∑ j ∈ cols, ∑ i ∈ rows, z i*(b j*X j i))=0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp only [mul_left_comm (z _) (b j),←Finset.mul_sum,blind j hj,mul_zero]
  rw [empty,sub_zero]

#print axioms PALRH.CarriedPrime.finite_dual_floor
#print axioms PALRH.CarriedPrime.invariant_observation

end PALRH.CarriedPrime
