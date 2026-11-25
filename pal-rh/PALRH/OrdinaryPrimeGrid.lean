import PALRH.RepeatAllowance
import PALRH.FourthAccounts

open Finset Set Filter Real
open scoped BigOperators Topology
noncomputable section
namespace PALRH.OrdinaryPrimeGrid
open RectangleBalance PrimeRenewal RepeatAllowance TaperedNewton

def frameCut (R : ℕ) (x : ℝ) := max R ((Nat.log 2 ⌊2*x⌋₊ / 160)^2)
def remaining (R : ℕ) (x : ℝ) (n : ℕ) : ℝ :=
  if n.Prime ∧ frameCut R x<n then primePowers n else 0
def parked (R : ℕ) (x : ℝ) (n : ℕ) : ℝ :=
  if n.Prime ∧ frameCut R x<n then 0 else primePowers n

/-- This reading is made from the old rational marks, their logarithms and the retained ordinary primes. -/
def discrepancy (R : ℕ) (x : ℝ) :=
  (∑ n ∈ Finset.Icc 1 ⌊2*x⌋₊, (marks n:ℝ)/n*taper (n/x)*Real.log (x/n))-observe (remaining R x) x

theorem paid_identity (R : ℕ) {x : ℝ} (xp : 0<x) :
    Real.log x*edge x=discrepancy R x-observe (parked R x) x := by
  have separate : observe primePowers x=observe (remaining R x) x+observe (parked R x) x := by
    unfold observe
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    by_cases active : n.Prime ∧ frameCut R x<n <;> simp [remaining,parked,active]
  have eq := finite_log_renewal xp
  rw [separate] at eq
  unfold discrepancy
  linarith

private theorem lambda_cap (n : ℕ) :
    0≤primePowers n ∧ primePowers n≤ArithmeticFunction.vonMangoldt n := by
  change 0≤ArithmeticFunction.vonMangoldt n*(allowed n:ℝ) ∧ ArithmeticFunction.vonMangoldt n*(allowed n:ℝ)≤ArithmeticFunction.vonMangoldt n
  rw [show allowed n=(if n.Coprime 6 then (1:ℚ) else 0) by rfl]
  split <;> simp [ArithmeticFunction.vonMangoldt_nonneg]

private theorem parked_nonnegative (R : ℕ) (x : ℝ) (n : ℕ) : 0≤parked R x n := by
  unfold parked;split <;> first | exact le_rfl | exact (lambda_cap n).1

def constant (R : ℕ) := 8*Real.sqrt R+(Real.log 4+4)+highConstant

private theorem cpos (R : ℕ) : 0≤constant R := by
  have g : 0≤highConstant := by unfold highConstant;positivity
  unfold constant
  positivity [Real.log_nonneg (by norm_num : (1:ℝ)≤4)]

theorem clock_cut (R : ℕ) {x : ℝ} (low : 1≤2*x) :
    Real.sqrt (frameCut R x)≤Real.sqrt R+Real.log (2*x)/80 := by
  let n:=⌊2*x⌋₊
  let k:=Nat.log 2 n
  have np : 0<n := Nat.floor_pos.mpr low
  have limit : 2^k≤n := Nat.pow_log_le_self 2 np.ne'
  have left : (2:ℝ)^k≤2*x :=
    (show (2:ℝ)^k≤n by exact_mod_cast limit).trans (Nat.floor_le (by linarith))
  have lp := Real.log_le_log (by positivity) left
  rw [Real.log_pow] at lp
  have log2 : 1/2≤Real.log 2 := by
    have q := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<1/2)
    rw [Real.log_div (by norm_num) (by norm_num),Real.log_one] at q
    linarith
  have kp : (k:ℝ)*(1/2)≤(k:ℝ)*Real.log 2 :=
    mul_le_mul_of_nonneg_left log2 (by positivity)
  have div : ((k/160:ℕ):ℝ)*160≤k := by exact_mod_cast Nat.div_mul_le_self k 160
  have non := Real.log_nonneg low
  change Real.sqrt ((max R ((k/160)^2):ℕ):ℝ)≤_
  rcases le_total R ((k/160)^2) with small|large
  · rw [max_eq_right small,Nat.cast_pow,Real.sqrt_sq (by positivity)]
    linarith [Real.sqrt_nonneg (R:ℝ)]
  · rw [max_eq_left large];linarith

/-- The absolute price of every removed clock has a strict margin below log(2x). -/
theorem parked_budget (R : ℕ) {x : ℝ} (low : 1≤2*x) :
    (∑ n ∈ Finset.Icc 1 ⌊2*x⌋₊, parked R x n/Real.sqrt n)≤
      (3/5)*Real.log (2*x)+constant R := by
  let N:=⌊2*x⌋₊
  let I:=Finset.Icc 1 N
  let Y:=frameCut R x
  have np : 0<N := Nat.floor_pos.mpr low
  have point (n : ℕ) (_ : n∈I) : parked R x n/Real.sqrt n≤repeated n/Real.sqrt n+
      (if n≤Y then primeMass n/Real.sqrt n else 0) := by
    have cap := div_le_div_of_nonneg_right (lambda_cap n).2 (Real.sqrt_nonneg (n:ℝ))
    by_cases prime : n.Prime <;> by_cases early : n≤Y
    · simp only [parked,Y,prime,show ¬frameCut R x<n by exact not_lt_of_ge early,and_false,if_false,
        repeated,if_true,zero_div,zero_add,early,primeMass,ArithmeticFunction.vonMangoldt_apply_prime prime] at cap ⊢
      exact cap
    · simp [parked,repeated,prime,Y,show frameCut R x<n from lt_of_not_ge early,early]
    · simpa [parked,repeated,prime,primeMass,early] using cap
    · simpa [parked,repeated,prime,primeMass,early] using cap
  have selected : I.filter (fun n => n≤Y)⊆Finset.Icc 1 Y := fun n hn =>
    Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1,(Finset.mem_filter.mp hn).2⟩
  have small : (∑ n ∈ I, if n≤Y then primeMass n/Real.sqrt n else 0)≤8*Real.sqrt Y := by
    rw [←Finset.sum_filter]
    apply le_trans _ (root_prime_budget Y)
    apply Finset.sum_le_sum_of_subset_of_nonneg selected
    intro n hn _
    apply div_nonneg _ (Real.sqrt_nonneg _)
    by_cases p : n.Prime
    · exact (show 0≤primeMass n by simp [primeMass,p,Real.log_nonneg (by exact_mod_cast p.pos : (1:ℝ)≤n)])
    · simp [primeMass,p]
  have repeats := repeated_budget np
  have ln := Real.log_le_log (by exact_mod_cast np : 0<(N:ℝ)) (Nat.floor_le (by linarith))
  have amount := Finset.sum_le_sum point
  rw [Finset.sum_add_distrib] at amount
  have bound := clock_cut R low
  change Real.sqrt Y≤_ at bound
  change (∑ n ∈ I, repeated n/Real.sqrt n)≤_ at repeats
  change (∑ n ∈ I, parked R x n/Real.sqrt n)≤_
  dsimp only [constant]
  linarith

theorem parked_transfer (R : ℕ) {x M : ℝ} (low : 1≤2*x) (non : 0≤M)
    (prior : ∀ n ∈ Finset.Icc 1 ⌊2*x⌋₊, Real.sqrt (x/n)*|edge (x/n)|≤M) :
    Real.sqrt x*|observe (parked R x) x|≤((3/5)*Real.log (2*x)+constant R)*M := by
  have xp : 0<x := by linarith
  unfold observe
  apply (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (Real.sqrt_nonneg _)).trans
  rw [Finset.mul_sum]
  have each (n : ℕ) (hn : n∈Finset.Icc 1 ⌊2*x⌋₊) :
      Real.sqrt x*|parked R x n/n*edge (x/n)|≤(parked R x n/Real.sqrt n)*M := by
    have nr : 0<(n:ℝ) := by exact_mod_cast (show 0<n from (Finset.mem_Icc.mp hn).1)
    have coef := parked_nonnegative R x n
    rw [abs_mul,abs_of_nonneg (div_nonneg coef nr.le)]
    have eq : Real.sqrt x*(parked R x n/n*|edge (x/n)|)=
        parked R x n/Real.sqrt n*(Real.sqrt (x/n)*|edge (x/n)|) := by
      rw [Real.sqrt_div xp.le]
      field_simp [(Real.sqrt_pos.mpr nr).ne']
      rw [Real.sq_sqrt nr.le]
      ring
    rw [eq]
    exact mul_le_mul_of_nonneg_left (prior n hn) (div_nonneg coef (Real.sqrt_nonneg _))
  have total := Finset.sum_le_sum each
  rw [←Finset.sum_mul] at total
  exact total.trans (mul_le_mul_of_nonneg_right (parked_budget R low) non)

#print axioms PALRH.OrdinaryPrimeGrid.paid_identity
#print axioms PALRH.OrdinaryPrimeGrid.parked_budget
#print axioms PALRH.OrdinaryPrimeGrid.parked_transfer

def oldAge (H : ℕ) := min H ((1+Nat.log 2 H)^2)
def row (H d : ℕ) : ℝ := (H:ℝ)/d
def start (R : ℕ) := 10*(|constant R|+2)
def initial (R : ℕ) := 10+5*(1+Real.exp (start R))

/-- One certificate contains only the finite primitive logarithmic comparisons to be paid. -/
def certificate (R H b : ℕ) : Prop :=
  ∀ d ∈ Finset.Icc 1 (2*H), (oldAge H:ℝ)≤row H d →
    (H:ℝ)*(⌈Real.sqrt (row H d)⌉₊:ℝ)*|discrepancy R (row H d)|≤(b:ℝ)*Real.log (4*row H d)

private theorem edge_unit_scale {x : ℝ} (low : 1≤2*x) : |edge x|≤5 := by
  have xp : 0<x := by linarith
  by_cases one : 1≤x
  · let h:=⌊x⌋₊
    have hp : 0<h := Nat.floor_pos.mpr one
    have near := FourthAccounts.fractional hp (Nat.floor_le xp.le) (Nat.lt_floor_add_one x).le
    have sharp : |(slope h marks:ℝ)|≤1 := by exact_mod_cast slope_cap hp
    have hr : (1:ℝ)≤h := by exact_mod_cast hp
    have claim : 4/(h:ℝ)≤4 := by simpa using div_le_div_of_nonneg_left (by norm_num : (0:ℝ)≤4) zero_lt_one hr
    have step := abs_add_le (edge x-(slope h marks:ℝ)) (slope h marks:ℝ)
    rw [sub_add_cancel] at step
    linarith
  · have v := exterior_term xp (lt_of_not_ge one) low
    rw [div_one] at v
    rw [v,abs_le]
    have a : 1≤1/x := (le_div_iff₀ xp).mpr (by linarith)
    have b : 1/x≤2 := (div_le_iff₀ xp).mpr (by linarith)
    constructor <;> linarith

private theorem old_sqrt {H : ℕ} (hp : 0<H) :
    Real.sqrt (oldAge H)≤1+2*Real.log H := by
  have pow := Nat.pow_log_le_self 2 hp.ne'
  have le : (2:ℝ)^(Nat.log 2 H)≤H := by exact_mod_cast pow
  have logs := Real.log_le_log (by positivity) le
  rw [Real.log_pow] at logs
  have atTwo : 1/2≤Real.log 2 := by linarith [Real.log_two_gt_d9]
  have mul := mul_le_mul_of_nonneg_left atTwo (Nat.cast_nonneg (α:=ℝ) (Nat.log 2 H))
  have cap : (oldAge H:ℝ)≤(((1+Nat.log 2 H:ℕ)^2:ℕ):ℝ) := by exact_mod_cast (min_le_right H ((1+Nat.log 2 H)^2))
  apply (Real.sqrt_le_sqrt cap).trans
  rw [Nat.cast_pow,Real.sqrt_sq (by positivity)]
  push_cast;linarith

/-- All children of an actual maximizing cell lie on the same rational quotient grid. -/
theorem grid_funds_head {R H b : ℕ} (hp : 0<H) (checks : certificate R H b) :
    Real.sqrt H*|(slope H marks:ℝ)|≤ initial R+10*Real.log H+8*((b:ℝ)/H) := by
  let I:=Finset.Icc 1 (2*H)
  let val:=fun d : ℕ => Real.sqrt (row H d)*|edge (row H d)|
  have member : 1∈I := Finset.mem_Icc.mpr ⟨le_rfl,by omega⟩
  have ne : I.Nonempty := ⟨1,member⟩
  obtain ⟨d,hd,maximal⟩ := Finset.exists_mem_eq_sup' ne val
  have major (j : ℕ) (hj : j∈I) : val j≤val d := by rw [←maximal];exact Finset.le_sup' val hj
  have head : val 1=Real.sqrt H*|(slope H marks:ℝ)| := by simp [val,row,same_edge hp]
  rw [←head]
  apply (major 1 member).trans
  let x:=row H d
  have dp : 0<d := (Finset.mem_Icc.mp hd).1
  have dr : 0<(d:ℝ) := by positivity
  have hr : 0<(H:ℝ) := by positivity
  have xp : 0<x := div_pos hr dr
  have low : 1≤2*x := by
    dsimp [x,row];rw [←mul_div_assoc]
    apply (le_div_iff₀ dr).mpr;rw [one_mul]
    exact_mod_cast (Finset.mem_Icc.mp hd).2
  let M:=val d
  let q:=(b:ℝ)/H
  have qn : 0≤q := by dsimp [q];positivity
  have mn : 0≤M := mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)
  have hlog : 0≤Real.log H := Real.log_nonneg (by exact_mod_cast hp)
  have initial_pos : 5≤ initial R := by unfold initial;linarith [Real.exp_pos (start R)]
  change M≤ initial R+10*Real.log H+8*q
  by_cases tooOld : x<(oldAge H:ℝ)
  · have cap := mul_le_mul (Real.sqrt_le_sqrt tooOld.le) (edge_unit_scale low) (abs_nonneg _) (Real.sqrt_nonneg _)
    change M≤_*5 at cap
    linarith [old_sqrt hp]
  let u:=Real.log (2*x)
  have split : Real.log x=u-Real.log 2 := by dsimp [u];rw [Real.log_mul (by norm_num) xp.ne'];ring
  have twice : Real.log (4*x)=u+Real.log 2 := by
    dsimp [u];rw [show 4*x=(2*x)*2 by ring,Real.log_mul (by positivity) (by norm_num)]
  have twoLog : Real.log 2≤1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  by_cases early : u≤start R
  · have bound : x≤Real.exp (start R) := (show x≤2*x by linarith).trans ((Real.log_le_iff_le_exp (by linarith)).mp early)
    have root : Real.sqrt x≤1+x := by nlinarith [Real.sq_sqrt xp.le,sq_nonneg (Real.sqrt x-1)]
    have cap := mul_le_mul root (edge_unit_scale low) (abs_nonneg _) (by linarith : 0≤1+x)
    change M≤_*5 at cap
    dsimp only [initial];linarith
  have ahead : start R<u := lt_of_not_ge early
  have big : 10*(|constant R|+2)<u := ahead
  have up : 0<u := by linarith [abs_nonneg (constant R)]
  have avail : u/4≤u-Real.log 2-((3/5)*u+constant R) := by linarith [le_abs_self (constant R),abs_nonneg (constant R)]
  have mark := checks d hd (le_of_not_gt tooOld)
  change (H:ℝ)*(⌈Real.sqrt x⌉₊:ℝ)*|discrepancy R x|≤(b:ℝ)*Real.log (4*x) at mark
  have cert : Real.sqrt x*|discrepancy R x|≤q*(u+Real.log 2) := by
    have fo := mul_le_mul_of_nonneg_right (Nat.le_ceil (Real.sqrt x)) (abs_nonneg (discrepancy R x))
    apply fo.trans
    dsimp only [q]
    rw [div_mul_eq_mul_div,le_div_iff₀ hr,←twice]
    nlinarith
  have floor : ⌊2*x⌋₊=(2*H)/d := by
    dsimp only [x,row]
    rw [show 2*((H:ℝ)/d)=((2*H:ℕ):ℝ)/d by push_cast;ring,Nat.floor_div_natCast,Nat.floor_natCast]
  have old (n : ℕ) (hn : n∈Finset.Icc 1 ⌊2*x⌋₊) : Real.sqrt (x/n)*|edge (x/n)|≤M := by
    rw [floor] at hn
    have lower := (Finset.mem_Icc.mp hn).1
    have upper := (Nat.le_div_iff_mul_le dp).mp (Finset.mem_Icc.mp hn).2
    have nm : d*n∈I := Finset.mem_Icc.mpr ⟨Nat.mul_pos dp lower,by simpa [Nat.mul_comm] using upper⟩
    have id : row H (d*n)=x/n := by dsimp [row,x];push_cast;ring
    have pay := major _ nm
    dsimp only [val] at pay
    rw [id] at pay
    exact pay
  have paid := parked_transfer R low mn old
  change _≤((3/5)*u+constant R)*M at paid
  have logx : 0≤Real.log x := by rw [split];linarith [abs_nonneg (constant R)]
  have abs := congrArg (fun y : ℝ => |y|) (paid_identity R xp)
  have sum := (mul_le_mul_of_nonneg_left
    (abs_sub (discrepancy R x) (observe (parked R x) x)) (Real.sqrt_nonneg x))
  change |Real.log x*edge x|=_ at abs
  rw [←abs,abs_mul,abs_of_nonneg logx,mul_add] at sum
  have mval : Real.sqrt x*|edge x|=M := rfl
  have total : (u-Real.log 2)*M≤q*(u+Real.log 2)+((3/5)*u+constant R)*M := by
    rw [←split]
    rw [show Real.sqrt x*(Real.log x*|edge x|)=Real.log x*M by rw [←mval];ring] at sum
    linarith
  have add := mul_le_mul_of_nonneg_right avail mn
  have two : u+Real.log 2≤2*u := by linarith [abs_nonneg (constant R)]
  have price := mul_le_mul_of_nonneg_left two qn
  have short : M≤8*q := by
    apply le_of_mul_le_mul_left (a:=u) _ up
    nlinarith
  linarith

#print axioms PALRH.OrdinaryPrimeGrid.grid_funds_head


/-- The submitted price uses integers and finite support on the sampled fourth-power heads. -/
def cost (bids : ℕ →₀ ℕ) (J : ℕ) : ℚ :=
  ∑ j ∈ Finset.Icc 1 J, (bids j:ℚ)/((j:ℚ)^4*j)

def PrimeCheckpoints (R : ℕ) : Prop := ∀ k : ℕ, 0<k → ∀ B : ℕ, ∃ J : ℕ, B≤J ∧
  ∃ bids : ℕ →₀ ℕ, (cost bids J)^k≤(J:ℚ) ∧
    ∀ j ∈ Finset.Icc 1 J, certificate R (j^4) (bids j)

private theorem harmonic_eq (J : ℕ) :
    (∑ j ∈ Finset.Icc 1 J, 1/(j:ℝ))=(harmonic J:ℝ) := by
  induction J with
  | zero => simp [harmonic]
  | succ j old => rw [Finset.sum_Icc_succ_top (by omega),old,harmonic_succ];push_cast;ring

theorem account_funded {R J : ℕ} (jp : 0<J) (bids : ℕ →₀ ℕ)
    (checks : ∀ j ∈ Finset.Icc 1 J, certificate R (j^4) (bids j)) (o : Bool) :
    (FourthAccounts.tally o J:ℝ)≤(initial R+40*Real.log J)*(1+Real.log J)+8*(cost bids J:ℝ) := by
  let I:=Finset.Icc 1 J
  have introPrice : 0≤ initial R := by dsimp [initial];positivity
  have ln : 0≤Real.log J := Real.log_nonneg (by exact_mod_cast jp)
  have each (j : ℕ) (hj : j∈I) :
      (j:ℝ)*(FourthAccounts.peak o j:ℝ)≤(initial R+40*Real.log J)*(1/(j:ℝ))+
        8*((bids j:ℝ)/((j:ℝ)^4*j)) := by
    have pos := (Finset.mem_Icc.mp hj).1
    have jr : 0<(j:ℝ) := by exact_mod_cast (show 0<j from pos)
    have pay := grid_funds_head (by positivity : 0<j^4) (checks j hj)
    push_cast at pay
    rw [show (j:ℝ)^4=((j:ℝ)^2)^2 by ring,Real.sqrt_sq (sq_nonneg _)] at pay
    rw [show ((j:ℝ)^2)^2=(j:ℝ)^4 by ring,Real.log_pow] at pay
    have absDir : |(SourceAllowance.direction o:ℝ)|=1 := by exact_mod_cast SourceAllowance.direction_abs o
    have peak : (FourthAccounts.peak o j:ℝ)≤|(slope (j^4) marks:ℝ)| := by
      unfold FourthAccounts.peak
      push_cast
      apply max_le _ (abs_nonneg _)
      apply (le_abs_self _).trans_eq
      rw [abs_mul,absDir,one_mul]
    have logle := Real.log_le_log jr (by exact_mod_cast (Finset.mem_Icc.mp hj).2 : (j:ℝ)≤J)
    have scaled := mul_le_mul_of_nonneg_left peak (sq_nonneg (j:ℝ))
    have eq : (initial R+40*Real.log J)*(1/(j:ℝ))+8*((bids j:ℝ)/((j:ℝ)^4*j))=
        (initial R+40*Real.log J+8*((bids j:ℝ)/(j:ℝ)^4))/j := by ring
    rw [eq]
    apply (le_div_iff₀ jr).mpr
    nlinarith
  have total := Finset.sum_le_sum each
  rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum] at total
  change (∑ j ∈ Finset.Icc 1 J, (j:ℝ)*(FourthAccounts.peak o j:ℝ))≤
    (initial R+40*Real.log J)*(∑ j ∈ Finset.Icc 1 J, 1/(j:ℝ))+
      8*(∑ j ∈ Finset.Icc 1 J, (bids j:ℝ)/((j:ℝ)^4*j)) at total
  rw [harmonic_eq] at total
  unfold FourthAccounts.tally cost
  push_cast
  have non : 0 ≤ initial R+40*Real.log J := by linarith
  exact total.trans (add_le_add (mul_le_mul_of_nonneg_left (harmonic_le_one_add_log J) non) le_rfl)

theorem rh_of_prime_checkpoints {R : ℕ} (checks : PrimeCheckpoints R) : RiemannHypothesis := by
  apply FourthAccounts.rh_of_checkpoints
  intro k positive B
  let e : ℝ:=1/(4*(k:ℝ))
  have ep : 0<e := by dsimp [e];positivity
  have unit : e*((4*k:ℕ):ℝ)=1 := by dsimp [e];push_cast;field_simp
  let K := (initial R+40/e)*(1+1/e)+8
  obtain ⟨N,hN⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop ep).comp tendsto_natCast_atTop_atTop).eventually_gt_atTop (K+2))
  obtain ⟨J,late,bids,test,paid⟩ := checks (4*k) (by omega) (max (max B N) 1)
  have jp : 0<J := by omega
  have jr : 0<(J:ℝ) := by positivity
  let p:=(J:ℝ)^e
  have one : 1≤p := Real.one_le_rpow (by exact_mod_cast jp) ep.le
  have target : p^(4*k)=(J:ℝ) := by
    dsimp only [p]
    rw [←Real.rpow_natCast,←Real.rpow_mul jr.le,unit,Real.rpow_one]
  have tested : (cost bids J:ℝ)^(4*k)≤(J:ℝ) := by exact_mod_cast test
  have limit : (cost bids J:ℝ)≤p := by
    by_contra! greater
    exact (not_lt_of_ge (tested.trans_eq target.symm)) (pow_lt_pow_left₀ greater (by linarith) (by omega))
  have log := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos jr e)
  rw [Real.log_rpow jr] at log
  have logle : Real.log J≤p/e := (le_div_iff₀ ep).mpr (by dsimp [p];linarith)
  have non : 0≤ initial R := by dsimp [initial];positivity
  have scale1 := mul_le_mul_of_nonneg_left one non
  have l1 : initial R+40*Real.log J≤(initial R+40/e)*p := by
    have eq : 40*(p/e)=(40/e)*p := by ring
    nlinarith
  have l2 : 1+Real.log J≤(1+1/e)*p := by
    have eq : p/e=(1/e)*p := by ring
    linarith
  have logpos := Real.log_nonneg (by exact_mod_cast jp : 1≤(J:ℝ))
  have multiply := mul_le_mul l1 l2 (by linarith) (mul_nonneg (by positivity) (by linarith))
  have raw := account_funded jp bids paid true
  have area : (FourthAccounts.tally true J:ℝ)≤K*p^2 := by
    dsimp only [K]
    nlinarith [mul_nonneg (show 0≤p by linarith) (sub_nonneg.mpr one)]
  have high : K+2<p := by simpa only [Function.comp_apply,p] using hN J (show N≤J by omega)
  have lift : K*p^2≤p^4 := by
    have free : K≤p^2 := by nlinarith [mul_nonneg (show 0≤p by linarith) (sub_nonneg.mpr one)]
    nlinarith [mul_le_mul_of_nonneg_right free (sq_nonneg p)]
  have posArea : 0≤FourthAccounts.tally true J :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (by positivity) (le_max_right _ _))
  have powered := pow_le_pow_left₀ (by exact_mod_cast posArea : 0≤(FourthAccounts.tally true J:ℝ))
    (area.trans lift) k
  rw [←pow_mul,target] at powered
  exact ⟨J,by omega,true,by exact_mod_cast powered⟩

#print axioms PALRH.OrdinaryPrimeGrid.account_funded
#print axioms PALRH.OrdinaryPrimeGrid.rh_of_prime_checkpoints

end PALRH.OrdinaryPrimeGrid
