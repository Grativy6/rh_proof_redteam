import PALRH.OneSidedBoard
import PALRH.SharedPascal
import PALRH.UpperHalfBoard

open Finset
open scoped BigOperators

noncomputable section
namespace PALRH.TickBoard
open PrimeBoard PrimeBand SieveFrame OneSidedBoard QuarticBoards LinearPrimeIntegral

/-- Count the equal multiplicative steps required to reach the distance label. The upper
bound on the search is supplied by the board size. -/
def ticks (n x m : ℕ) :=
  ((range (n*x)).filter (fun t => (x+1)^t<m*x^t)).card

def count (k : ℕ) :=
  ∑ m ∈ Icc 2 (k^4), if m.gcd (k^2).factorial=1 then (k^4-m)*ticks (k^4) (k^2) m else 0

private theorem power_slots {x b m : ℕ} (xp : 0<x) (bits : m≤2^b) :
    m*x^(b*x)≤(x+1)^(b*x) := by
  have step:=Nat.pow_le_pow_left (PALRH.UpperHalfBoard.doubled_words x xp) b
  rw [mul_pow,←pow_mul,←pow_mul,Nat.mul_comm x b] at step
  exact (Nat.mul_le_mul_right _ bits).trans step

private theorem cap {m n x : ℕ} (xp : 0<x) (mn : m≤n) : m*x^(n*x)≤(x+1)^(n*x) :=
  power_slots xp (mn.trans (show n<2^n from Nat.lt_two_pow_self).le)

private theorem later {t v x m : ℕ} (tv : t≤v) (h : m*x^t≤(x+1)^t) : m*x^v≤(x+1)^v := by
  induction v,tv using Nat.le_induction with
  | base => exact h
  | succ a _ ih =>
    rw [pow_succ,pow_succ,←Nat.mul_assoc]
    exact Nat.mul_le_mul ih (Nat.le_succ x)

theorem tick_cover {n x m : ℕ} (xp : 0<x) (mn : m≤n) : m*x^(ticks n x m)≤(x+1)^(ticks n x m) := by
  have witness : ∃ t : ℕ,m*x^t≤(x+1)^t := ⟨n*x,cap xp mn⟩
  let T:=Nat.find witness
  have pays : m*x^T≤(x+1)^T := Nat.find_spec witness
  have top : T≤n*x := Nat.find_min' witness (cap xp mn)
  have exact_set : (range (n*x)).filter (fun t => (x+1)^t<m*x^t)=range T := by
    ext t
    simp only [mem_filter,mem_range]
    constructor
    · intro h
      exact lt_of_not_ge (fun cover => (not_le_of_gt h.2) (later cover pays))
    · intro h
      exact ⟨h.trans_le top,lt_of_not_ge (Nat.find_min witness h)⟩
  simpa [ticks,exact_set] using pays

theorem ticks_le_of_price {n x m t : ℕ} (enough : m*x^t≤(x+1)^t) : ticks n x m≤t := by
  unfold ticks
  calc
    _ ≤ (range t).card := Finset.card_le_card (fun i hi => mem_range.mpr (lt_of_not_ge
      (fun h => (not_le_of_gt (mem_filter.mp hi).2) (later h enough))))
    _ = _ := Finset.card_range _

theorem bit_price {n x m b : ℕ} (xp : 0<x) (mb : m≤2^b) : ticks n x m≤b*x :=
  ticks_le_of_price (power_slots xp mb)

theorem single_price {n x m : ℕ} (xp : 0<x) (mp : 0<m) (mn : m≤n) :
    (x:ℝ)*Real.log m≤ticks n x m := by
  let T:=ticks n x m
  have xr : 0<(x:ℝ) := by exact_mod_cast xp
  have mr : 0<(m:ℝ) := by exact_mod_cast mp
  have cover : (m:ℝ)*(x:ℝ)^T≤((x:ℝ)+1)^T := by exact_mod_cast tick_cover xp mn
  have logc:=Real.log_le_log (mul_pos mr (pow_pos xr T)) cover
  rw [Real.log_mul mr.ne' (pow_pos xr T).ne',Real.log_pow,Real.log_pow] at logc
  have slope:=Real.log_le_sub_one_of_pos (show 0<((x:ℝ)+1)/x by positivity)
  have size : ((x:ℝ)+1)/x-1=1/x := by field_simp;ring
  rw [Real.log_div (by positivity) xr.ne',size] at slope
  have high:=mul_le_mul_of_nonneg_left slope (Nat.cast_nonneg T)
  rw [mul_comm]
  apply (le_div_iff₀ xr).mp
  rw [mul_one_div] at high
  change Real.log m≤(T:ℝ)/x
  linarith only [logc,high]

/-- One whole tick of rounding and one reciprocal-unit correction suffice uniformly. -/
theorem single_upper {n x m : ℕ} (xp : 0<x) (mp : 0<m) :
    (ticks n x m:ℝ)≤1+((x:ℝ)+1)*Real.log m := by
  have xn : 0<(x:ℝ) := by exact_mod_cast xp
  have mn : 0<(m:ℝ) := by exact_mod_cast mp
  have lm : 0≤Real.log m := Real.log_nonneg (by exact_mod_cast mp)
  cases h : ticks n x m with
  | zero => push_cast;positivity
  | succ a =>
    have fails : (x+1)^a<m*x^a := by
      by_contra! ok
      have bad:=ticks_le_of_price (n:=n) ok
      omega
    have realFail : ((x:ℝ)+1)^a<(m:ℝ)*(x:ℝ)^a := by exact_mod_cast fails
    have logc:=Real.log_lt_log (by positivity) realFail
    rw [Real.log_mul mn.ne' (pow_pos xn a).ne',Real.log_pow,Real.log_pow] at logc
    have lower:=Real.one_sub_inv_le_log_of_pos (show 0<((x:ℝ)+1)/x by positivity)
    have e : 1-(((x:ℝ)+1)/x)⁻¹=1/((x:ℝ)+1) := by field_simp;ring
    rw [e,Real.log_div (by positivity) xn.ne'] at lower
    have scaled:=mul_le_mul_of_nonneg_left lower (Nat.cast_nonneg a)
    have limit : (a:ℝ)/((x:ℝ)+1)≤Real.log m := by
      rw [mul_one_div] at scaled
      linarith only [scaled,logc]
    have count:=(div_le_iff₀ (by positivity)).mp limit
    push_cast
    nlinarith only [count]

private theorem one_positive (n f : ℕ) : 0<oneFrameDirection n f := by
  apply Finset.prod_pos
  intro m hm
  have mp : 0<m := by have := (mem_Icc.mp hm).1;omega
  split_ifs
  · exact pow_pos mp _
  · decide

private theorem total_price (k : ℕ) (kp : 0<k) :
    ((k^2:ℕ):ℝ)*Real.log (oneFrameDirection (k^4) (k^2).factorial:ℝ)≤(count k:ℝ) := by
  let n:=k^4
  let x:=k^2
  have xp : 0<x := pow_pos kp _
  unfold count oneFrameDirection
  push_cast
  rw [Real.log_prod]
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro m hm
    have mp : 0<m := by have := (mem_Icc.mp hm).1;omega
    have mn : m≤n := (mem_Icc.mp hm).2
    change (k:ℝ)^2 * Real.log (if m.gcd x.factorial=1 then (m:ℝ)^(n-m) else 1) ≤
      if m.gcd x.factorial=1 then ((n-m:ℕ):ℝ)*(ticks n x m:ℝ) else 0
    by_cases good : m.gcd x.factorial=1
    · rw [if_pos good,if_pos good,Real.log_pow]
      calc
        _ = ((n-m:ℕ):ℝ)*((x:ℝ)*Real.log m) := by dsimp [x];push_cast;ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (single_price xp mp mn) (Nat.cast_nonneg _)
    · simp [good]
  · intro m hm
    have mp : 0<(m:ℝ) := by exact_mod_cast (show 0<m by have := (mem_Icc.mp hm).1;omega)
    split_ifs <;> positivity

/-- At a fourth power the one remaining premise is a count of unit positions in a box:
two orientations of the eligible triples eventually fit into n by n by sqrt(n) cells. -/
theorem rh_of_layers (K : ℕ)
    (funded : ∀ k : ℕ, K≤k → 0<k → 2*count k≤(k^4)^2*k^2) : RiemannHypothesis := by
  obtain ⟨A,reps⟩:=Chebyshev.psi_sub_theta_le_mul_sqrt
  apply rh_of_eventual_upper_area K (C:=max 0 A+2) (by positivity)
  intro k late kp
  let n:=k^4
  let x:=k^2
  have nx : n.sqrt=x := root_of_quartic k
  have xn : x≤n := nx ▸ Nat.sqrt_le_self n
  have xp : 0<x := pow_pos kp _
  have xr : 0<(x:ℝ) := by exact_mod_cast xp
  have nr : 0≤(n:ℝ) := Nat.cast_nonneg _
  have rroot : Real.sqrt (n:ℝ)=(x:ℝ) := by
    dsimp [n,x];push_cast
    rw [show (k:ℝ)^4=((k:ℝ)^2)^2 by ring,Real.sqrt_sq (by positivity)]
  let F:=oneFrameDirection n x.factorial
  have fp : 0<(F:ℝ) := by exact_mod_cast one_positive n x.factorial
  have weight : (x:ℝ)*Real.log (F:ℝ)≤(count k:ℝ) := total_price k kp
  have box : 2*(count k:ℝ)≤(n:ℝ)^2*x := by exact_mod_cast funded k late kp
  have outside : 2*Real.log (F:ℝ)≤(n:ℝ)^2 := by
    apply le_of_mul_le_mul_left (a:=(x:ℝ)) _ xr
    nlinarith only [weight,box]
  have posfull : 0<n.factorial^n := pow_pos (Nat.factorial_pos _) _
  have eq:=frame_count_exact n
  rw [nx,frame_square,inputCount] at eq
  have returned : F^2=retained n x := Nat.eq_of_mul_eq_mul_left posfull eq
  have split:=exact_split n x
  unfold demand inputCount at split
  rw [mul_assoc] at split
  have all_digits : dials n=F^2*removed n x := by
    rw [returned]
    exact Nat.eq_of_mul_eq_mul_left posfull split
  have small := small_prime_price xn
  have rpos : 0<(removed n x:ℝ) := by exact_mod_cast removed_pos n x
  have log_small:=Real.log_le_log rpos (by exact_mod_cast small :
    (removed n x:ℝ)≤(2:ℝ)^(4*n*x))
  rw [Real.log_pow] at log_small
  push_cast at log_small
  have log_two:=Real.log_le_sub_one_of_pos (by norm_num : 0<(2:ℝ))
  have price:=mul_le_mul_of_nonneg_left (show Real.log 2≤1 by linarith only [log_two])
    (show 0≤4*(n:ℝ)*x by positivity)
  have all_log:=dial_log n
  rw [all_digits,Nat.cast_mul,Nat.cast_pow,Real.log_mul (pow_ne_zero _ fp.ne') rpos.ne',Real.log_pow] at all_log
  push_cast at all_log
  have diff:=(repeated n).2
  have lifts:=mul_le_mul_of_nonneg_left (reps (n:ℝ)) nr
  rw [rroot] at lifts
  have gain:=mul_le_mul_of_nonneg_right (le_max_right (0:ℝ) A) (show 0≤(n:ℝ)*x by positivity)
  change fullWalk n-(n:ℝ)^2/2≤(max 0 A+2)*(k:ℝ)^6
  rw [show (k:ℝ)^6=(n:ℝ)*(x:ℝ) by dsimp [n,x];push_cast;ring]
  nlinarith only [diff,lifts,gain,outside,all_log,price,log_small]

/-- The smaller lattice with two entire height layers set aside still gives the same implication. -/
theorem rh_of_two_spare_layers (K : ℕ)
    (packed : ∀ k : ℕ, K≤k → 0<k → 2*count k≤(k^4)^2*(k^2-2)) :
    RiemannHypothesis := by
  apply rh_of_layers K
  intro k hk kp
  exact (packed k hk kp).trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))

#print axioms PALRH.TickBoard.tick_cover
#print axioms PALRH.TickBoard.rh_of_layers
#print axioms PALRH.TickBoard.rh_of_two_spare_layers
end PALRH.TickBoard
