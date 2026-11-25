import PALRH.RoughSquares

open Finset
open scoped BigOperators
noncomputable section
namespace PALRH.CoreMatrix
open RoughSquares

def gate (n : ℕ) : ℝ := if 2 ∣ n ∨ 3 ∣ n then 0 else 1
def count := partialSum gate
def indices (x : ℕ) := Finset.Icc 1 x

private lemma gate_mul (a b : ℕ) : gate (a*b)=gate a*gate b := by
  simp only [gate,Nat.prime_two.dvd_mul,Nat.prime_three.dvd_mul]
  by_cases a2 : 2 ∣ a <;> by_cases a3 : 3 ∣ a <;> by_cases b2 : 2 ∣ b <;> by_cases b3 : 3 ∣ b <;>
    simp [a2,a3,b2,b3]

private lemma core_gate (n : ℕ) : core n=mu n*gate n := by
  by_cases a : 2 ∣ n <;> by_cases b : 3 ∣ n <;> simp [core,remove,gate,a,b]

private lemma mu_divisors (n : ℕ) :
    (∑ d ∈ n.divisors, mu d)=if n=1 then 1 else 0 := by
  have h := DFunLike.congr_fun ArithmeticFunction.moebius_mul_coe_zeta n
  rw [ArithmeticFunction.coe_mul_zeta_apply,ArithmeticFunction.one_apply] at h
  by_cases one : n=1 <;> simp only [mu,one,if_true,if_false] at h ⊢ <;> exact_mod_cast h

private lemma count_increment (k d : ℕ) :
    count ((k+1)/d)-count (k/d) = if d ∣ k+1 then gate ((k+1)/d) else 0 := by
  by_cases hit : d ∣ k+1
  · simp [count,partialSum,Nat.succ_div_of_dvd hit,hit,Finset.sum_range_succ]
  · simp [Nat.succ_div_of_not_dvd hit,hit]

private def line (h k : ℕ) := ∑ d ∈ indices h, core d*count (k/d)

private lemma line_step {h k : ℕ} (le : k+1≤h) :
    line h (k+1)-line h k = if k+1=1 then 1 else 0 := by
  have term (d : ℕ) (hd : d∈indices h) :
      core d*count ((k+1)/d)-core d*count (k/d) =
        if d ∣ k+1 then mu d*gate (k+1) else 0 := by
    rw [←mul_sub,count_increment]
    by_cases hit : d ∣ k+1
    · rw [if_pos hit,if_pos hit,core_gate,mul_assoc,←gate_mul,Nat.mul_div_cancel' hit]
    · simp [hit]
  have eq : (indices h).filter (fun d => d ∣ k+1) = (k+1).divisors := by
    ext d
    simp only [indices,Finset.mem_filter,Finset.mem_Icc,Nat.mem_divisors]
    constructor
    · intro hd; exact ⟨hd.2,by omega⟩
    · rintro ⟨dvd,_⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos dvd (by omega),(Nat.le_of_dvd (by omega) dvd).trans le⟩,dvd⟩
  unfold line
  rw [←Finset.sum_sub_distrib,Finset.sum_congr rfl term,←Finset.sum_filter,eq,←Finset.sum_mul,mu_divisors]
  by_cases first : k+1=1
  · simp [first,gate]
  · simp only [if_neg first,zero_mul]

private lemma line_full (h k : ℕ) (le : k≤h) : line h k=if k=0 then 0 else 1 := by
  induction k with
  | zero => simp [line,count,partialSum]
  | succ k old =>
    have step := line_step le
    specialize old (by omega)
    by_cases zero : k=0
    · simp only [zero] at old step ⊢; norm_num at old step ⊢; linarith
    · rw [if_neg zero] at old
      rw [if_neg (by omega : k+1≠1)] at step
      simp only [Nat.succ_ne_zero,if_false]
      linarith

def block (I J : Finset ℕ) (x : ℕ) : ℝ :=
  ∑ i ∈ I, ∑ j ∈ J, core i*core j*count (x/(i*j))

def form (h x : ℕ) := block (indices h) (indices h) x

private lemma flip (I J : Finset ℕ) (x : ℕ) : block I J x=block J I x := by
  unfold block
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  rw [Nat.mul_comm i j,mul_comm (core i) (core j)]

private lemma block_left {I J : Finset ℕ} (dis : Disjoint I J) (K : Finset ℕ) (x : ℕ) :
    block (I∪J) K x=block I K x+block J K x := Finset.sum_union dis

private lemma block_right {I J : Finset ℕ} (dis : Disjoint I J) (K : Finset ℕ) (x : ℕ) :
    block K (I∪J) x=block K I x+block K J x := by
  rw [flip K (I∪J),block_left dis,flip I K,flip J K]

private lemma block_strip {h x : ℕ} (le : h≤x) :
    block (indices h) (indices x) x=coreWalk h := by
  rw [←rough_agrees]
  unfold block roughSum
  apply Finset.sum_congr rfl
  intro i hi
  have iv := Finset.mem_Icc.mp hi
  have pos : 0<x/i := Nat.div_pos (iv.2.trans le) iv.1
  have sum := line_full x (x/i) (Nat.div_le_self _ _)
  rw [if_neg pos.ne'] at sum
  simp only [←Nat.div_div_eq_div_mul,mul_assoc,←Finset.mul_sum]
  unfold line at sum
  rw [sum,mul_one]

/-- Inclusion-exclusion leaves exactly the simultaneous omitted tail. Every summand
uses the actual two earlier signs and the exact counting kernel. -/
theorem unpaid {h x : ℕ} (fit : h≤x) :
    coreWalk x-(2*coreWalk h-form h x)=block (Finset.Ioc h x) (Finset.Ioc h x) x := by
  let I := indices h
  let O := Finset.Ioc h x
  have all : indices x=I∪O := by
    ext n; simp only [I,O,indices,Finset.mem_union,Finset.mem_Icc,Finset.mem_Ioc]; omega
  have dis : Disjoint I O := Finset.disjoint_left.mpr (fun _ a b =>
    (not_lt_of_ge (Finset.mem_Icc.mp a).2) (Finset.mem_Ioc.mp b).1)
  have mixed := block_strip fit
  have whole := block_strip (le_refl x)
  rw [all,block_left dis,block_right dis,block_right dis,flip O I] at whole
  change block I (indices x) x=coreWalk h at mixed
  rw [all,block_right dis] at mixed
  change coreWalk x-(2*coreWalk h-block I I x)=block O O x
  linarith

/-- Hyperbola identity on the whole interval where two indices beyond h cannot meet.
This is Huxley and Watt's two-factor identity for the filter coprime to six. -/
theorem square_sweep {h x : ℕ} (fit : h≤x) (outside : x<(h+1)*(h+1)) :
    coreWalk x=2*coreWalk h-form h x := by
  have zero : block (Finset.Ioc h x) (Finset.Ioc h x) x=0 := by
    apply Finset.sum_eq_zero
    intro i hi
    apply Finset.sum_eq_zero
    intro j hj
    have big := outside.trans_le (Nat.mul_le_mul (Nat.succ_le_of_lt (Finset.mem_Ioc.mp hi).1)
      (Nat.succ_le_of_lt (Finset.mem_Ioc.mp hj).1))
    simp [Nat.div_eq_of_lt big,count,partialSum]
  have eq := unpaid fit
  rw [zero] at eq
  linarith

/-- Crop both omitted axes at u once every product with a larger input costs zero. -/
theorem cropped_unpaid {h x u : ℕ} (fit : h≤x) (inside : u≤x) (beyond : x<(u+1)*(h+1)) :
    coreWalk x-(2*coreWalk h-form h x)=block (Finset.Ioc h u) (Finset.Ioc h u) x := by
  rw [unpaid fit]
  let O := Finset.Ioc h x
  let S := Finset.Ioc h u
  have sub : S⊆O := fun i hi => Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hi).1,(Finset.mem_Ioc.mp hi).2.trans inside⟩
  have van (i j : ℕ) (hi : i∈O) (hj : j∈O) (missing : i∉S) : core i*core j*count (x/(i*j))=0 := by
    have ip := (Finset.mem_Ioc.mp hi).1
    have jp := (Finset.mem_Ioc.mp hj).1
    have big : u < i := by by_contra! le; exact missing (Finset.mem_Ioc.mpr ⟨ip,le⟩)
    have off := beyond.trans_le (Nat.mul_le_mul (Nat.succ_le_of_lt big) (Nat.succ_le_of_lt jp))
    simp [Nat.div_eq_of_lt off,count,partialSum]
  have crop (U : Finset ℕ) (legal : U⊆O) : block S U x=block O U x := by
    apply Finset.sum_subset sub
    intro i hi missing
    apply Finset.sum_eq_zero
    intro j hj
    exact van i j hi (legal hj) missing
  symm
  change block S S x=block O O x
  rw [crop S sub,flip O S,crop O (by rfl)]

theorem at_square (h : ℕ) : coreWalk (h*h)=2*coreWalk h-form h (h*h) := by
  apply square_sweep <;> nlinarith [Nat.le_mul_self h]

/-- The jump on any integer threshold strictly beyond the side and before the next square
is exactly the negative of the true rough Möbius sign at that threshold. -/
theorem form_jump {h x : ℕ} (lo : h≤x) (hi : x+1<(h+1)*(h+1)) :
    form h (x+1)-form h x = -core (x+1) := by
  have old := square_sweep lo (by omega : x<(h+1)*(h+1))
  have fresh := square_sweep (by omega : h≤x+1) hi
  have step : coreWalk (x+1)=coreWalk x+core (x+1) := by simp only [coreWalk,partialSum,Finset.sum_range_succ]
  linarith

theorem square_jump_vanishes {h : ℕ} (big : 1<h) : form h (h*h)=form h (h*h-1) := by
  obtain ⟨p,hp,dvd⟩ := Nat.exists_prime_and_dvd (show h≠1 by omega)
  have no : ¬Squarefree (h*h) := fun yes =>
    Nat.squarefree_iff_prime_squarefree.mp yes p hp (Nat.mul_dvd_mul dvd dvd)
  have zero : core (h*h)=0 := by simp [core_gate,mu,ArithmeticFunction.moebius_eq_zero_of_not_squarefree no]
  have pos : 0<h*h := Nat.mul_pos (by omega) (by omega)
  have next : h*h-1+1=h*h := by omega
  have old : h≤h*h-1 := by
    have h2 : 2*h≤h*h := Nat.mul_le_mul_right h big
    omega
  have jump := form_jump (h:=h) (x:=h*h-1) old (by rw [next]; nlinarith)
  rw [next,zero,neg_zero] at jump
  linarith

#print axioms PALRH.CoreMatrix.at_square
#print axioms PALRH.CoreMatrix.form_jump
#print axioms PALRH.CoreMatrix.square_jump_vanishes

def harmonic (h : ℕ) := ∑ i ∈ indices h, core i/(i:ℝ)
def centered (h : ℕ) := form h (h*h)-((h:ℝ)*harmonic h)^2/3
def peeled (h : ℕ) := form h (h*h)-(coreWalk h)^2

private lemma core_cap (n : ℕ) : |core n|≤1 := by
  have b : |mu n|≤1 := by unfold mu; exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n:=n))
  by_cases a : 2 ∣ n <;> by_cases t : 3 ∣ n <;> simp [core,remove,a,t,b]

theorem walked_cap (n : ℕ) : |coreWalk n|≤(n:ℝ) := by
  rw [←rough_agrees,roughSum]
  calc
    _ ≤ ∑ i ∈ Finset.Icc 1 n, |core i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.Icc 1 n, (1:ℝ) := Finset.sum_le_sum (fun i _ => core_cap i)
    _ = _ := by simp [Nat.card_Icc]

theorem centered_gives_upper (h : ℕ) (B : ℝ) (paid : -B≤centered h) :
    coreWalk (h*h)≤2*h+B := by
  rw [at_square]
  dsimp [centered] at paid
  nlinarith [sq_nonneg ((h:ℝ)*harmonic h),(le_abs_self (coreWalk h)).trans (walked_cap h)]

theorem peeled_gives_upper (h : ℕ) (B : ℝ) (paid : -B≤peeled h) :
    coreWalk (h*h)≤1+B := by
  rw [at_square]
  dsimp [peeled] at paid
  nlinarith [sq_nonneg (coreWalk h-1)]

/-- The rank-one product of the two side census readings has exactly unit quadratic
value on the true Möbius vector at every positive side. -/
theorem side_read {h : ℕ} (positive : 0<h) :
    (∑ i ∈ indices h, core i*count (h/i))=1 := by
  simpa [line,positive.ne'] using line_full h h le_rfl

private lemma before_five {n : ℕ} (low : 0<n) (high : n<5) : count n=1 := by
  interval_cases n <;> norm_num [count,partialSum,Finset.sum_range_succ,gate]

def peeledRow (h j : ℕ) : ℝ :=
  ∑ i ∈ indices h, core i*(count (h*h/(i*j))-1)

/-- After removing the common unit, an outer row reads the neighboring signed
core walk directly. The hypothesis includes every j>h/5 with j<=h. -/
theorem outer_row {h j : ℕ} (jp : 0<j) (inside : j≤h) (near : h*h/j<5*(h+1)) :
    peeledRow h j=1-coreWalk (h*h/j) := by
  let u := h*h/j
  have hu : h≤u := (Nat.le_div_iff_mul_le jp).mpr (Nat.mul_le_mul_left h inside)
  have up : 0<u := lt_of_lt_of_le jp (inside.trans hu)
  have full := line_full u u le_rfl
  rw [if_neg up.ne'] at full
  have split : indices u=indices h∪Finset.Ioc h u := by
    ext i
    simp only [indices,Finset.mem_Icc,Finset.mem_union,Finset.mem_Ioc]
    omega
  have dis : Disjoint (indices h) (Finset.Ioc h u) := Finset.disjoint_left.mpr (fun _ a b =>
    (not_lt_of_ge (Finset.mem_Icc.mp a).2) (Finset.mem_Ioc.mp b).1)
  have one (i : ℕ) (hi : i∈Finset.Ioc h u) : count (u/i)=1 := by
    obtain ⟨lower,upper⟩ := Finset.mem_Ioc.mp hi
    have ip : 0 < i := by omega
    exact before_five (Nat.div_pos upper ip)
      ((Nat.div_lt_iff_lt_mul ip).mpr (lt_of_lt_of_le near (Nat.mul_le_mul_left 5 (by omega))))
  have frozen : (∑ i ∈ Finset.Ioc h u, core i*count (u/i))=∑ i ∈ Finset.Ioc h u, core i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [one i hi,mul_one]
  unfold line at full
  rw [split,Finset.sum_union dis,frozen] at full
  have mass : coreWalk u=(∑ i ∈ indices h, core i)+∑ i ∈ Finset.Ioc h u, core i := by
    rw [←rough_agrees]
    change (∑ i ∈ indices u, core i)=_
    rw [split,Finset.sum_union dis]
  unfold peeledRow
  have terms (i : ℕ) : h*h/(i*j)=u/i := by dsimp [u]; rw [Nat.div_div_eq_div_mul,Nat.mul_comm j i]
  simp only [terms,mul_sub,mul_one,Finset.sum_sub_distrib]
  change _=1-coreWalk u
  linarith

theorem rh_of_form_size (paid : ∀ a : ℝ, 1/2<a → ∃ C : ℝ, 0≤C ∧
    ∀ h : ℕ, 0<h → |form h (h*h)|≤C*((h*h:ℕ):ℝ)^a) : RiemannHypothesis := by
  apply rh_of_square_signs
  intro a ha
  obtain ⟨C,hC,cap⟩ := paid a ha
  refine ⟨C+3,by linarith,fun h hp => ?_⟩
  have use := cap h hp
  have hreal : (1:ℝ)≤((h*h:ℕ):ℝ) := by exact_mod_cast (Nat.mul_pos hp hp)
  have first : (h:ℝ)≤((h*h:ℕ):ℝ)^a := by
    have bound := Real.rpow_le_rpow_of_exponent_le hreal ha.le
    rw [←Real.sqrt_eq_rpow,Nat.cast_mul,Real.sqrt_mul_self (by positivity)] at bound
    simpa only [Nat.cast_mul] using bound
  have p := pruned_cost h
  rw [abs_sub_comm] at p
  have tri := abs_add_le (retained h-coreWalk (h*h)) (coreWalk (h*h))
  rw [sub_add_cancel] at tri
  have root := abs_sub (2*coreWalk h) (form h (h*h))
  rw [←at_square,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2)] at root
  linarith [walked_cap h]

#print axioms PALRH.CoreMatrix.outer_row
#print axioms PALRH.CoreMatrix.rh_of_form_size


private lemma sign31 : core 31=(-1:ℝ) := by
  norm_num [core,remove,mu,ArithmeticFunction.moebius_apply_prime (by decide : Nat.Prime 31)]

private lemma sign35 : core 35=(1:ℝ) := by
  have base := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (m:=5) (n:=7) (by decide)
  norm_num [ArithmeticFunction.moebius_apply_prime (by decide : Nat.Prime 5),
    ArithmeticFunction.moebius_apply_prime (by decide : Nat.Prime 7)] at base
  norm_num [core,remove,mu,base]

/-- The first actual product is 31 squared. Its sign is positive. -/
theorem side_thirty_first :
    coreWalk 961-(2*coreWalk 30-form 30 961)=1 := by
  rw [cropped_unpaid (u:=31) (by decide) (by decide) (by decide)]
  have setEq : Finset.Ioc 30 31=({31}:Finset ℕ) := by decide +kernel
  norm_num [block,setEq,sign31,count,partialSum,Finset.sum_range_succ,gate]

/-- The two orderings of 31 times 35 then reverse the cumulative sign. -/
theorem side_thirty_cross :
    coreWalk 1085-(2*coreWalk 30-form 30 1085)= -1 := by
  rw [cropped_unpaid (u:=35) (by decide) (by decide) (by decide)]
  have setEq : Finset.Ioc 30 35=({31,32,33,34,35}:Finset ℕ) := by decide +kernel
  have z2 : core 32=0 := by norm_num [core,remove]
  have z3 : core 33=0 := by norm_num [core,remove]
  have z4 : core 34=0 := by norm_num [core,remove]
  norm_num [block,setEq,Finset.sum_insert,sign31,sign35,z2,z3,z4,count,partialSum,Finset.sum_range_succ,gate]

#print axioms PALRH.CoreMatrix.unpaid
#print axioms PALRH.CoreMatrix.side_thirty_first
#print axioms PALRH.CoreMatrix.side_thirty_cross

end PALRH.CoreMatrix
