import PALRH.CubicWeights
import PALRH.CubicGaps

open Finset Set
open scoped Classical BigOperators
noncomputable section
namespace PALRH.CubicCarry
open RectangleBalance TaperedNewton CubicQuadrature CubicWeights SquarePass

private theorem atom_all (b : ℕ → ℝ) {T d : ℕ} (dp : 0<d) (stop : ∀ i : ℕ, T ≤ i → b i=0) :
    (∑ n ∈ Finset.Icc 1 T, cost b n*tick d n)=d*(b d-b (2*d)) := by
  by_cases inside : d≤T
  · exact atom_read b dp inside stop
  rw [stop d (by omega),stop (2*d) (by omega),sub_zero,mul_zero]
  apply Finset.sum_eq_zero
  intro n hn
  have nr : 0<(n:ℝ) := by exact_mod_cast (show 0<n from (Finset.mem_Icc.mp hn).1)
  have before : (n:ℝ)≤d := by exact_mod_cast ((Finset.mem_Icc.mp hn).2.trans (by omega : T≤d))
  have low : 2≤2*(d:ℝ)/n := (le_div_iff₀ nr).mpr (by linarith)
  simp [tick,taper,min_eq_right (show 2-2*(d:ℝ)/n≤1 by linarith),
    max_eq_left (show 2-2*(d:ℝ)/n≤0 by linarith)]

theorem dilated_rows (b : ℕ → ℝ) {T j : ℕ} (jp : 0<j) (stop : ∀ i : ℕ, T ≤ i → b i=0) :
    (∑ n ∈ Finset.Icc 1 T, cost b n*edge ((n:ℝ)/2/j))=
      (j:ℝ)*∑ d ∈ Finset.Icc 1 T, (marks d:ℝ)*(b (d*j)-b (2*d*j)) := by
  let I:=Finset.Icc 1 T
  have jr : 0<(j:ℝ) := by exact_mod_cast jp
  have one : (1:ℝ)≤j := by exact_mod_cast jp
  have row (n : ℕ) (hn : n∈I) : cost b n*edge ((n:ℝ)/2/j)=
      ∑ d ∈ I, (marks d:ℝ)/d*(cost b n*tick (d*j) n) := by
    have nr : 0<(n:ℝ) := by exact_mod_cast (show 0<n from (Finset.mem_Icc.mp hn).1)
    have head : (n:ℝ)/2/j≤(T:ℝ)/2 := (div_le_self (by positivity) one).trans
      (div_le_div_of_nonneg_right (by exact_mod_cast (Finset.mem_Icc.mp hn).2) (by norm_num))
    rw [edge_pad_positive (by positivity) head,show 2*((T:ℝ)/2)=T by ring,Nat.floor_natCast,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    rw [tick,show (d:ℝ)/((n:ℝ)/2/j)=2*((d*j:ℕ):ℝ)/n by push_cast;field_simp]
    ring
  rw [Finset.sum_congr rfl row,Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have dp : 0<d := (Finset.mem_Icc.mp hd).1
  rw [←Finset.mul_sum,atom_all b (Nat.mul_pos dp jp) stop,←Nat.mul_assoc,Nat.cast_mul]
  have dr : 0<(d:ℝ) := by exact_mod_cast dp
  field_simp

def response (T : ℕ) (w : ℕ → ℝ) (j : ℕ) :=
  ∑ n ∈ Finset.Icc 1 T, if ∃ b : ℕ, n=3^b then w (n*j) else 0

private theorem dilated_source {w : ℕ → ℝ} {T j : ℕ} (jp : 0<j) (stop : ∀ i : ℕ, T ≤ i → w i=0) :
    (∑ n ∈ Finset.Icc 1 T, cost (profile T w) n*edge ((n:ℝ)/2/j))=(j:ℝ)*response T w j := by
  have closed {k : ℕ} (h : T≤k) : profile T w k=0 := Finset.sum_eq_zero (fun r hr =>
    stop _ (h.trans (Nat.le_mul_of_pos_left k (Finset.mem_Icc.mp hr).1)))
  have shifted : ∀ i : ℕ, T ≤ i → w (i*j)=0 := fun i hi =>stop _ (hi.trans (Nat.le_mul_of_pos_right _ jp))
  have other {k : ℕ} (h : T≤k) : profile T (fun i => w (i*j)) k=0 := Finset.sum_eq_zero (fun r hr =>
    shifted _ (h.trans (Nat.le_mul_of_pos_left k (Finset.mem_Icc.mp hr).1)))
  have same (k : ℕ) : profile T w (k*j)=profile T (fun i => w (i*j)) k := by simp [profile,Nat.mul_assoc]
  rw [dilated_rows _ jp (fun _ hi => closed hi)]
  apply congrArg (fun t : ℝ => (j:ℝ)*t)
  simp_rw [same]
  rw [←actual_rows _ (fun _ hi => other hi),full_grid shifted,response]

theorem one_pass_mean {w : ℕ → ℝ} {T : ℕ} (stop : ∀ i : ℕ, T ≤ i → w i=0) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 T, cost (profile T w) n*reading N 1 ((n:ℝ)/2))=
      ∑ a ∈ Finset.range (N+1), ∑ b ∈ Finset.range (N+1),
        ((2^a*3^b:ℕ):ℝ)*response T w ((2^a*3^b)^2) := by
  let I:=Finset.Icc 1 T
  let J:=Finset.range (N+1)
  let c:=cost (profile T w)
  have root (a b : ℕ) : 0<2^a*3^b := by positivity
  have atom (a b : ℕ) :
      (∑ n ∈ I, c n*shift (2^a*3^b) edge ((n:ℝ)/2))=
        ((2^a*3^b:ℕ):ℝ)*response T w ((2^a*3^b)^2) := by
    let p:=2^a*3^b
    have pr : 0<(p:ℝ) := by exact_mod_cast root a b
    have form (n : ℕ) : c n*shift p edge ((n:ℝ)/2)=(c n*edge ((n:ℝ)/2/((p^2:ℕ):ℝ)))/p := by
      rw [shift,Nat.cast_pow];ring
    rw [Finset.sum_congr rfl (fun n _ => form n),←Finset.sum_div,dilated_source (pow_pos (root a b) 2) stop]
    dsimp [p] at pr ⊢
    push_cast
    field_simp
  have row (n : ℕ) : c n*reading N 1 ((n:ℝ)/2)=
      ∑ a ∈ J, ∑ b ∈ J, c n*shift (2^a*3^b) edge ((n:ℝ)/2) := by
    change c n*sweep N 2 (sweep N 3 edge) ((n:ℝ)/2)=_
    rw [sweep,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [shift_sweep,Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun n _ => row n),Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun b _ => atom a b)

def measured (T N : ℕ) := ∑ n ∈ Finset.Icc 1 T, cost (samples 0 T) n*reading N 1 ((n:ℝ)/2)

theorem cubic_mean {T : ℕ} (tp : 0<T) (N : ℕ) :
    measured T N=∑ a ∈ Finset.range (N+1), ∑ b ∈ Finset.range (N+1),
      ((2^a*3^b:ℕ):ℝ)*response T (cubic T) ((2^a*3^b)^2) := by
  rw [measured,show samples 0 T=profile T (cubic T) from funext (full_samples T)]
  exact one_pass_mean (cubic_stop tp) N

#print axioms PALRH.CubicCarry.dilated_rows
#print axioms PALRH.CubicCarry.one_pass_mean
#print axioms PALRH.CubicCarry.cubic_mean

private theorem corner (N b : ℕ) (inrange : b≤N/4) : ∃ a : ℕ, a≤N ∧
    (2^a*3^b)^2≤2^N ∧ 2^N<4*(2^a*3^b)^2 := by
  have nine : 9^b≤2^N := calc
    9^b≤(2^4)^b := Nat.pow_le_pow_left (by decide) _
    _ = 2^(4*b) := (pow_mul _ _ _).symm
    _ ≤ 2^N := Nat.pow_le_pow_right (by decide) (by omega)
  let a:=Nat.log 4 (2^N/9^b)
  have p : 0<9^b := by positivity
  have q : 0<2^N/9^b := (Nat.le_div_iff_mul_le p).mpr (by simpa using nine)
  have low : 4^a*9^b≤2^N := (Nat.le_div_iff_mul_le p).mp (Nat.pow_log_le_self 4 q.ne')
  have high : 2^N<4^(a+1)*9^b := (Nat.div_lt_iff_lt_mul p).mp (Nat.lt_pow_succ_log_self (by decide : 1<4) _)
  have root : (2^a*3^b)^2=4^a*9^b := by
    rw [mul_pow,←pow_mul,←pow_mul,Nat.mul_comm a 2,Nat.mul_comm b 2,pow_mul,pow_mul]
    norm_num
  have pre : 2^a≤2^N :=
    (Nat.pow_le_pow_left (by decide : 2≤4) a).trans ((Nat.le_mul_of_pos_right _ p).trans low)
  have an : a≤N := by
    by_contra! no
    exact (not_lt_of_ge pre) (Nat.pow_lt_pow_right (by decide) no)
  refine ⟨a,an,by simpa [root] using low,?_⟩
  rw [root,←Nat.mul_assoc,←pow_succ']
  exact high

/-- The average of the actual once-passed rows has an unconditional lower bound at
every dyadic head, growing at least linearly in the number of doublings in log units. -/
theorem mean_floor (N : ℕ) :
    ((N/4:ℕ)+1:ℝ)*Real.sqrt ((2:ℝ)^N)/16≤measured (2*2^N) N := by
  let H:ℕ:=2^N
  have hp : 0<H := by dsimp [H];positivity
  have hr : 0<(H:ℝ) := by exact_mod_cast hp
  let T:=2*H
  have tp : 0<T := by dsimp [T];omega
  let term:=fun b a : ℕ => ((2^a*3^b:ℕ):ℝ)*response T (cubic T) ((2^a*3^b)^2)
  have non (b a : ℕ) : 0≤term b a := by
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro n _
    split_ifs <;> first | exact pow_nonneg (le_max_left _ _) _ | exact le_rfl
  have one (b : ℕ) (hb : b∈Finset.range (N/4+1)) :
      Real.sqrt (H:ℝ)/16≤∑ a ∈ Finset.range (N+1), term b a := by
    obtain ⟨a,an,le,gt⟩ := corner N b (by simpa using hb)
    let p:=2^a*3^b
    have pr : 0<(p:ℝ) := by dsimp [p];positivity
    have psmall : (p:ℝ)^2≤H := by exact_mod_cast le
    have plarge : (H:ℝ)<4*(p:ℝ)^2 := by exact_mod_cast gt
    have ss : Real.sqrt (H:ℝ)≤2*p := by nlinarith [Real.sq_sqrt hr.le,Real.sqrt_nonneg (H:ℝ)]
    have den : 0<(T:ℝ) := by exact_mod_cast tp
    have half : (p:ℝ)^2/T≤1/2 := (div_le_iff₀ den).mpr (by dsimp [T];push_cast;linarith)
    have cube : (1/8:ℝ)≤cubic T (p^2) := by
      dsimp only [cubic];rw [Nat.cast_pow]
      have yes : (1/2:ℝ)≤max 0 (1-(p:ℝ)^2/T) := (by linarith : (1/2:ℝ)≤1-(p:ℝ)^2/T).trans (le_max_right _ _)
      rw [show (1/8:ℝ)=(1/2:ℝ)^3 by norm_num]
      exact pow_le_pow_left₀ (by norm_num) yes 3
    have first : cubic T (p^2)≤response T (cubic T) (p^2) := by
      let I:=Finset.Icc 1 T
      let f:=fun n : ℕ => if ∃ c : ℕ, n=3^c then cubic T (n*p^2) else 0
      have f1 : f 1=cubic T (p^2) := by simp [f,show ∃ c : ℕ, 1=3^c from ⟨0,rfl⟩]
      rw [←f1]
      apply Finset.single_le_sum (f:=f)
      · intro n _
        dsimp [f];split_ifs <;> first | exact pow_nonneg (le_max_left _ _) _ | exact le_rfl
      · exact Finset.mem_Icc.mpr ⟨le_rfl,tp⟩
    have price := mul_le_mul_of_nonneg_left (cube.trans first) pr.le
    have below : Real.sqrt (H:ℝ)/16≤term b a := by change _≤(p:ℝ)*_;linarith
    exact below.trans (Finset.single_le_sum (f:=term b) (fun i _ => non b i) (Finset.mem_range.mpr (by omega)))
  change ((N/4:ℕ)+1:ℝ)*Real.sqrt ((2:ℝ)^N)/16≤measured T N
  rw [cubic_mean tp N,Finset.sum_comm]
  have begin := Finset.sum_le_sum one
  rw [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at begin
  have extend : (∑ b ∈ Finset.range (N/4+1), ∑ a ∈ Finset.range (N+1), term b a)≤
      ∑ b ∈ Finset.range (N+1), ∑ a ∈ Finset.range (N+1), term b a :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (fun b _ _ => Finset.sum_nonneg (fun a _ => non b a))
  apply le_trans _ (begin.trans extend)
  dsimp [H]
  push_cast
  ring_nf
  exact le_rfl

#print axioms PALRH.CubicCarry.mean_floor
end PALRH.CubicCarry
