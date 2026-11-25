import PALRH.Smoothed
import PALRH.SquareBudget
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

open Finset
open scoped BigOperators
noncomputable section
namespace PALRH.TaperedNewton

abbrev AF := ArithmeticFunction ℚ

/-- A rational plateau followed by a linear taper. -/
def weight (H n : ℕ) : ℚ :=
  if n≤H then 1 else if n≤2*H then ((2*H-n:ℕ):ℚ)/H else 0

def bill (H n : ℕ) : ℚ := if H<n ∧ n≤2*H then (n:ℚ)/H else 0

def slope (H : ℕ) (f : AF) : ℚ :=
  ∑ n ∈ Finset.Icc 1 (2*H), weight H n*f n/n

def side (H : ℕ) (f : AF) : AF :=
  ⟨fun n => weight H n*f n-bill H n*slope H f,by simp [bill,ArithmeticFunction.map_zero]⟩

private theorem side_apply (H n : ℕ) (f : AF) :
    side H f n=weight H n*f n-bill H n*slope H f := rfl

theorem head (H : ℕ) (f : AF) {n : ℕ} (inside : n≤H) : side H f n=f n := by
  simp [side_apply,weight,bill,inside,show ¬H<n by omega]

theorem ended (H : ℕ) (f : AF) {n : ℕ} (out : 2*H<n) : side H f n=0 := by
  simp [side_apply,weight,bill,show ¬n≤H by omega,show ¬n≤2*H by omega]

theorem bill_total {H : ℕ} (positive : 0<H) :
    (∑ n ∈ Finset.Icc 1 (2*H), bill H n/n)=1 := by
  have each (n : ℕ) (inSet : n∈Finset.Icc 1 (2*H)) :
      bill H n/n = if H<n then 1/(H:ℚ) else 0 := by
    obtain ⟨low,high⟩ := Finset.mem_Icc.mp inSet
    by_cases after : H<n
    · simp only [bill,after,high,and_self,if_true]
      field_simp
    · simp [bill,after]
  have eq : (Finset.Icc 1 (2*H)).filter (fun n => H<n)=Finset.Ioc H (2*H) := by
    ext n; simp only [Finset.mem_filter,Finset.mem_Icc,Finset.mem_Ioc];omega
  rw [Finset.sum_congr rfl each,←Finset.sum_filter,eq,Finset.sum_const,Nat.card_Ioc,nsmul_eq_mul]
  rw [show 2*H-H=H by omega]
  field_simp

theorem balanced {H : ℕ} (hp : 0<H) (f : AF) :
    (∑ n ∈ Finset.Icc 1 (2*H), side H f n/n)=0 := by
  simp only [side_apply,sub_div,Finset.sum_sub_distrib]
  have term (n : ℕ) : bill H n*slope H f/(n:ℚ)=(bill H n/n)*slope H f := by ring
  simp_rw [term]
  rw [←Finset.sum_mul,bill_total hp,one_mul]
  exact sub_self _

private lemma sub_apply (f g : AF) (n : ℕ) : (f-g) n=f n-g n := by
  simp only [sub_eq_add_neg,ArithmeticFunction.add_apply,ArithmeticFunction.neg_apply]

private theorem linear_mixed (K : ℕ) (a b c : AF) :
    side K (a+b-c)=side K a+side K b-side K c := by
  have add (f g : AF) : slope K (f+g)=slope K f+slope K g := by
    simp only [slope,ArithmeticFunction.add_apply,mul_add,add_div,Finset.sum_add_distrib]
  have sub (f g : AF) : slope K (f-g)=slope K f-slope K g := by
    simp only [slope,sub_apply,mul_sub,sub_div,Finset.sum_sub_distrib]
  ext n
  simp only [side_apply,sub_apply,ArithmeticFunction.add_apply,sub,add]
  ring

theorem wider_fixes {H K : ℕ} (hp : 0<H) (wide : 2*H≤K) (f : AF) :
    side K (side H f)=side H f := by
  let a := side H f
  have sub : Finset.Icc 1 (2*H) ⊆ Finset.Icc 1 (2*K) := fun n h =>
    Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp h).1,(Finset.mem_Icc.mp h).2.trans (by omega)⟩
  have old : (∑ n ∈ Finset.Icc 1 (2*H), weight K n*a n/n)=0 := by
    rw [←balanced hp f]
    apply Finset.sum_congr rfl
    intro n hn
    simp [weight,((Finset.mem_Icc.mp hn).2.trans wide),a]
  have lift : (∑ n ∈ Finset.Icc 1 (2*H), weight K n*a n/n)=slope K a := by
    apply Finset.sum_subset sub
    intro n high miss
    have out : 2*H<n := by
      by_contra! bad; exact miss (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp high).1,bad⟩)
    simp [a,ended H f out]
  have zero : slope K a=0 := lift.symm.trans old
  change side K a=a
  ext n
  rw [side_apply,zero,mul_zero,sub_zero]
  by_cases h : n≤2*H
  · simp [weight,h.trans wide]
  · simp [a,ended H f (lt_of_not_ge h)]

/-- A product of two omitted tails has no coefficient before their first possible product. -/
private lemma delayed_mul {f g : AF} {A B n : ℕ}
    (hf : ∀ i<A, f i=0) (hg : ∀ j<B, g j=0) (before : n<A*B) :
    (f*g) n=0 := by
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro ij member
  have eq := (Nat.mem_divisorsAntidiagonal.mp member).1
  by_cases i : ij.1<A
  · rw [hf _ i,zero_mul]
  · have j : ij.2<B := by
      by_contra! bj
      have both := Nat.mul_le_mul (le_of_not_gt i) bj
      omega
    rw [hg _ j,mul_zero]

def update (g a : AF) : AF := a+a-a*a*g

theorem unpaid_square {m g : AF} (inv : m*g=1) (a : AF) :
    m-update g a=(m-a)*(m-a)*g := by
  unfold update
  linear_combination (a+a-m)*inv

theorem updated_head {m g : AF} (inv : m*g=1) (H : ℕ) (n : ℕ) (early : n<(H+1)*(H+1)) :
    update g (side H m) n=m n := by
  let a := side H m
  have old (i : ℕ) (low : i<H+1) : (m-a) i=0 := by
    rw [sub_apply,show a i=m i from head H m (by omega),sub_self]
  have pair (j : ℕ) (low : j<(H+1)*(H+1)) : ((m-a)*(m-a)) j=0 := delayed_mul old old low
  have zero : ((m-a)*(m-a)*g) n=0 := delayed_mul (A:=(H+1)*(H+1)) (B:=1) pair
    (fun i hi => by rw [show i=0 by omega,ArithmeticFunction.map_zero]) (by simpa using early)
  have eq := DFunLike.congr_fun (unpaid_square inv a) n
  rw [sub_apply,zero] at eq
  exact (sub_eq_zero.mp eq).symm

private theorem sees_head {K : ℕ} {a b : AF} (agree : ∀ n, n≤2*K → a n=b n) :
    side K a=side K b := by
  have cap : slope K a=slope K b := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [agree n (Finset.mem_Icc.mp hn).2]
  ext n
  by_cases yes : n≤2*K
  · rw [side_apply,side_apply,cap,agree n yes]
  · rw [ended K a (lt_of_not_ge yes),ended K b (lt_of_not_ge yes)]

/-- The renewed balanced side requires only the prior balanced coefficients. -/
theorem same_frame_update {m g : AF} (inv : m*g=1) {H K : ℕ} (hp : 0<H)
    (wide : 2*H≤K) (before : 2*K<(H+1)*(H+1)) :
    side K m=side H m+side H m-side K (side H m*side H m*g) := by
  let a := side H m
  have equal : side K m=side K (update g a) :=
    sees_head (fun n hn => (updated_head inv H n (hn.trans_lt before)).symm)
  rw [equal,update,linear_mixed]
  change side K (side H m)+side K (side H m)-_=_
  rw [wider_fixes hp wide]

def allowed : AF := ⟨fun n => if n.Coprime 6 then 1 else 0,by decide⟩
def marks : AF := ⟨fun n => (ArithmeticFunction.moebius n:ℚ)*allowed n,by simp [ArithmeticFunction.map_zero]⟩

private lemma allowed_mul (a b : ℕ) : allowed (a*b)=allowed a*allowed b := by
  change (if (a*b).Coprime 6 then 1 else 0)=
    (if a.Coprime 6 then (1:ℚ) else 0)*(if b.Coprime 6 then 1 else 0)
  by_cases ha : a.Coprime 6
  · by_cases hb : b.Coprime 6
    · rw [if_pos (Nat.coprime_mul_iff_left.mpr ⟨ha,hb⟩),if_pos ha,if_pos hb,one_mul]
    · rw [if_neg (fun yes => hb (Nat.coprime_mul_iff_left.mp yes).2),if_neg hb,mul_zero]
  · rw [if_neg (fun yes => ha (Nat.coprime_mul_iff_left.mp yes).1),if_neg ha,zero_mul]

theorem marks_inverse : marks*allowed=1 := by
  ext n
  have law := DFunLike.congr_fun ArithmeticFunction.moebius_mul_coe_zeta n
  rw [ArithmeticFunction.coe_mul_zeta_apply,ArithmeticFunction.one_apply] at law
  have sum : (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d:ℚ))=if n=1 then 1 else 0 := by
    by_cases one : n=1 <;> simp only [one,if_true,if_false] at law ⊢ <;> exact_mod_cast law
  rw [ArithmeticFunction.mul_apply,Nat.sum_divisorsAntidiagonal (fun i j => marks i*allowed j),ArithmeticFunction.one_apply]
  calc
    _ = (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d:ℚ))*allowed n := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d hd
      change ((ArithmeticFunction.moebius d:ℚ)*allowed d)*allowed (n/d)=_
      rw [mul_assoc,←allowed_mul,Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)]
    _ = _ := by rw [sum]; by_cases one : n=1 <;> simp [allowed,one]

theorem rough_update {H K : ℕ} (hp : 0<H) (wide : 2*H≤K) (before : 2*K<(H+1)*(H+1)) :
    side K marks=side H marks+side H marks-side K (side H marks*side H marks*allowed) :=
  same_frame_update marks_inverse hp wide before

#print axioms PALRH.TaperedNewton.balanced
#print axioms PALRH.TaperedNewton.unpaid_square
#print axioms PALRH.TaperedNewton.rough_update

/-- The same balance law applies to two independently prepared sides. Their
unpaid coefficient is the product of the two omitted parts against the census. -/
theorem mixed_unpaid {m g : AF} (inv : m*g=1) (a b : AF) :
    m-(a+b-a*b*g)=(m-a)*(m-b)*g := by
  linear_combination (a+b-m)*inv

theorem mixed_update {m g : AF} (inv : m*g=1) {H J K : ℕ} (hH : 0<H) (hJ : 0<J)
    (keepH : 2*H≤K) (keepJ : 2*J≤K) (fit : 2*K<(H+1)*(J+1)) :
    side K m=side H m+side J m-side K (side H m*side J m*g) := by
  let a := side H m
  let b := side J m
  have lh (n : ℕ) (small : n<H+1) : (m-a) n=0 := by
    rw [sub_apply,show a n=m n from head H m (by omega),sub_self]
  have rh (n : ℕ) (small : n<J+1) : (m-b) n=0 := by
    rw [sub_apply,show b n=m n from head J m (by omega),sub_self]
  have no (n : ℕ) (small : n<(H+1)*(J+1)) : ((m-a)*(m-b)) n=0 := delayed_mul lh rh small
  have eq : side K m=side K (a+b-a*b*g) := by
    apply sees_head
    intro n hn
    have e := DFunLike.congr_fun (mixed_unpaid inv a b) n
    have z : ((m-a)*(m-b)*g) n=0 := delayed_mul (B:=1) no
      (fun t ht => by rw [show t=0 by omega,ArithmeticFunction.map_zero]) (by simpa using hn.trans_lt fit)
    rw [sub_apply,z] at e
    exact sub_eq_zero.mp e
  rw [eq,linear_mixed]
  dsimp only [a,b]
  rw [wider_fixes hH keepH,wider_fixes hJ keepJ]

#print axioms PALRH.TaperedNewton.mixed_update


/-- The four actual quotient digits for the census restricted to 2 and 3. -/
def fourFloors (k : ℕ) : ℚ := (k:ℚ)-(k/2:ℕ)-(k/3:ℕ)+(k/6:ℕ)

theorem actual_floors (k : ℕ) : (fourFloors k:ℝ)=CoreMatrix.count k := by
  have atOne (n : ℕ) : PrimeOpening.census 1 n=(n:ℝ) := by
    simp [PrimeOpening.census,RoughSquares.partialSum,PrimeOpening.allow]
  have atTwo (n : ℕ) : PrimeOpening.census 2 n=(n:ℝ)-(n/2:ℕ) := by
    have h := PrimeOpening.open_census (N:=1) Nat.prime_two (by decide) n
    simpa only [Nat.one_mul,atOne] using h
  have h := PrimeOpening.open_census (N:=2) Nat.prime_three (by decide) k
  rw [←PrimeOpening.census_six]
  simp only [atTwo,Nat.div_div_eq_div_mul,show 3*2=6 by decide] at h
  rw [h]
  simp only [fourFloors,Rat.cast_sub,Rat.cast_add,Rat.cast_natCast]
  ring

def signal (d k : ℕ) : ℚ :=
  -(turn d k-turn (2*d) k-turn (3*d) k+turn (6*d) k)

private lemma turnAsFloor {d : ℕ} (hd : 0<d) (k : ℕ) :
    turn d k=(k:ℚ)/d-(k/d:ℕ) := by
  have h : (d:ℚ)*(k/d:ℕ)+(k%d:ℕ)=(k:ℚ) := by exact_mod_cast Nat.div_add_mod k d
  unfold turn;field_simp;linarith

theorem floor_and_linear {d : ℕ} (hd : 0<d) (k : ℕ) :
    fourFloors (k/d) = (k:ℚ)/(3*d)+signal d k := by
  simp only [signal,fourFloors,turnAsFloor hd k,turnAsFloor (Nat.mul_pos (by decide : 0<2) hd) k,
    turnAsFloor (Nat.mul_pos (by decide : 0<3) hd) k,turnAsFloor (Nat.mul_pos (by decide : 0<6) hd) k,
    Nat.div_div_eq_div_mul,Nat.cast_mul,Nat.cast_ofNat]
  rw [Nat.mul_comm d 2,Nat.mul_comm d 3,Nat.mul_comm d 6]
  ring

private lemma signal_mem {d : ℕ} (hd : 0<d) : signal d ∈ OneTick.fits := by
  have any (v : ℕ) (h : 0<v) : turn v∈OneTick.fits := by
    by_cases one : v=1
    · have eq : turn v=0 := by funext k; simp [turn,one,Nat.mod_one]
      rw [eq];exact OneTick.fits.zero_mem
    · exact OneTick.turn_mem (by omega)
  exact OneTick.fits.neg_mem (OneTick.fits.add_mem (OneTick.fits.sub_mem
    (OneTick.fits.sub_mem (any d hd) (any _ (by positivity))) (any _ (by positivity)))
    (any _ (by positivity)))

def reading (H : ℕ) : ℕ → ℚ :=
  ∑ d ∈ Finset.Icc 1 (2*H), side H marks d • signal d

theorem legal (H : ℕ) : reading H∈OneTick.fits := by
  apply OneTick.fits.sum_mem
  intro d hd
  exact OneTick.fits.smul_mem _ (signal_mem (Finset.mem_Icc.mp hd).1)

theorem reading_is_count {H : ℕ} (hp : 0<H) (k : ℕ) :
    reading H k=∑ d ∈ Finset.Icc 1 (2*H), side H marks d*fourFloors (k/d) := by
  simp only [reading,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  have eq (d : ℕ) (hd : d∈Finset.Icc 1 (2*H)) :
      side H marks d*fourFloors (k/d) =
        ((k:ℚ)/3)*(side H marks d/d)+side H marks d*signal d k := by
    rw [floor_and_linear (Finset.mem_Icc.mp hd).1];ring
  rw [Finset.sum_congr rfl eq,Finset.sum_add_distrib,←Finset.mul_sum,balanced hp,mul_zero,zero_add]

private lemma marks_real (n : ℕ) : (marks n:ℝ)=RoughSquares.core n := by
  have a : n.Coprime 2 ↔ ¬2 ∣ n := Nat.coprime_comm.trans Nat.prime_two.coprime_iff_not_dvd
  have b : n.Coprime 3 ↔ ¬3 ∣ n := Nat.coprime_comm.trans Nat.prime_three.coprime_iff_not_dvd
  have g : n.Coprime 6 ↔ n.Coprime 2 ∧ n.Coprime 3 := by
    change n.Coprime (2*3) ↔ _; exact Nat.coprime_mul_iff_right
  change (((ArithmeticFunction.moebius n:ℚ)*(if n.Coprime 6 then 1 else 0):ℚ):ℝ)=_
  by_cases t : 2 ∣ n <;> by_cases r : 3 ∣ n <;>
    simp [RoughSquares.core,RoughSquares.remove,RoughSquares.mu,g,a,b,t,r]

theorem agrees_on_head {H k : ℕ} (hp : 0<H) (kp : 0<k) (inside : k≤H) :
    reading H k=OneTick.occupied k := by
  rw [reading_is_count hp]
  have filter : Finset.Icc 1 k ⊆ Finset.Icc 1 (2*H) := fun d hd =>
    Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1,(Finset.mem_Icc.mp hd).2.trans (by omega)⟩
  have cropped : (∑ d ∈ Finset.Icc 1 k, side H marks d*fourFloors (k/d)) =
      ∑ d ∈ Finset.Icc 1 (2*H), side H marks d*fourFloors (k/d) := by
    apply Finset.sum_subset filter
    intro d hd out
    have far : k<d := by by_contra! bad; exact out (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1,bad⟩)
    simp [Nat.div_eq_of_lt far,fourFloors]
  rw [←cropped]
  have strip : (∑ d ∈ Finset.Icc 1 k, side H marks d*fourFloors (k/d))=
      ∑ d ∈ Finset.Icc 1 k, marks d*fourFloors (k/d) := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [head H marks ((Finset.mem_Icc.mp hd).2.trans inside)]
  rw [strip,OneTick.occupied,if_neg kp.ne']
  apply (Rat.cast_injective (α:=ℝ))
  simp only [Rat.cast_sum,Rat.cast_mul,marks_real,actual_floors,Rat.cast_one]
  exact CoreMatrix.side_read kp

/-- The sole remaining estimate for this specific recursively reproducible family. -/
def Stable : Prop := ∀ δ : ℝ, 0<δ → ∀ N : ℕ, ∃ H : ℕ, N≤H ∧ 0<H ∧
    OneTick.loss OneTick.occupied (reading H) ≤ ((H:ℝ)+1)^δ

theorem rh_of_stable (stability : Stable) : RiemannHypothesis := by
  apply HeadGrowth.rh_of_subpower_occupied
  intro δ pos N
  obtain ⟨H,late,hp,cost⟩ := stability δ pos N
  exact ⟨H,late,reading H,legal H,fun _ kp inside => agrees_on_head hp kp inside,cost⟩

#print axioms PALRH.TaperedNewton.agrees_on_head
#print axioms PALRH.TaperedNewton.rh_of_stable


private lemma bounds_at_integer (k : ℕ) :
    -(1:ℚ)/3≤fourFloors k-(k:ℚ)/3 ∧ fourFloors k-(k:ℚ)/3≤2/3 := by
  have left : 3*(k/2)+3*(k/3)≤2*k+3*(k/6)+1 := by omega
  have right : 2*k+3*(k/6)≤3*(k/2)+3*(k/3)+2 := by omega
  have a : 3*((k/2:ℕ):ℚ)+3*((k/3:ℕ):ℚ)≤2*(k:ℚ)+3*((k/6:ℕ):ℚ)+1 := by exact_mod_cast left
  have b : 2*(k:ℚ)+3*((k/6:ℕ):ℚ)≤3*((k/2:ℕ):ℚ)+3*((k/3:ℕ):ℚ)+2 := by exact_mod_cast right
  unfold fourFloors
  constructor <;> linarith

private lemma row_error {d : ℕ} (pos : 0<d) (k : ℕ) :
    |fourFloors (k/d)-(k:ℚ)/(3*d)|≤2/3 := by
  have b := bounds_at_integer (k/d)
  have lo : 0≤turn d k := by unfold turn;positivity
  have hi : turn d k≤1 := by
    unfold turn
    apply (div_le_one (by positivity)).mpr
    exact_mod_cast (Nat.mod_lt k pos).le
  rw [turnAsFloor pos] at lo hi
  have eq : (k:ℚ)/(3*d)=((k:ℚ)/d)/3 := by ring
  rw [eq,abs_le]
  constructor <;> linarith

private lemma marks_cap (n : ℕ) : |marks n|≤allowed n := by
  have bound : |(ArithmeticFunction.moebius n:ℚ)|≤1 := by exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n:=n))
  change |(ArithmeticFunction.moebius n:ℚ)*(if n.Coprime 6 then 1 else 0)|≤(if n.Coprime 6 then 1 else 0)
  split_ifs <;> simp [bound]

private lemma total_census (h : ℕ) : (∑ d ∈ Finset.Icc 1 h, allowed d)=fourFloors h := by
  apply (Rat.cast_injective (α:=ℝ))
  rw [actual_floors,←PrimeOpening.census_six]
  have coord (d : ℕ) : ((allowed d):ℝ)=PrimeOpening.allow 6 d := by
    rw [show allowed d=(if d.Coprime 6 then (1:ℚ) else 0) by rfl]
    unfold PrimeOpening.allow
    split <;> norm_num
  simp only [Rat.cast_sum,coord]
  induction h with
  | zero => simp [PrimeOpening.census,RoughSquares.partialSum]
  | succ h old =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    simp only [PrimeOpening.census,RoughSquares.partialSum,Finset.sum_range_succ] at old ⊢
    rw [old]

def oldSlope (H : ℕ) := ∑ d ∈ Finset.Icc 1 H, marks d/d

/-- The true rough signs have a reciprocal sum of magnitude at most one at every cut. -/
theorem old_slope_cap {H : ℕ} (hp : 0<H) : |oldSlope H|≤1 := by
  let S := Finset.Icc 1 H
  let t := fun d : ℕ => marks d*(fourFloors (H/d)-(H:ℚ)/(3*d))
  have one : 1∈S := Finset.mem_Icc.mpr ⟨le_rfl,hp⟩
  have m1 : marks 1=1 := by change (ArithmeticFunction.moebius 1:ℚ)*_=1; simp [allowed]
  have g1 : allowed 1=1 := by decide +kernel
  have read : (∑ d ∈ S, marks d*fourFloors (H/d))=1 := by
    apply (Rat.cast_injective (α:=ℝ))
    simp only [Rat.cast_sum,Rat.cast_mul,marks_real,actual_floors,Rat.cast_one]
    exact CoreMatrix.side_read hp
  have slope_eq : (∑ d ∈ S, t d)=1-((H:ℚ)/3)*oldSlope H := by
    dsimp only [t,oldSlope,S]
    simp only [mul_sub,Finset.sum_sub_distrib]
    rw [read,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro d _
    ring
  have left := Finset.sum_erase_add S t one
  have right := Finset.sum_erase_add S allowed one
  have census := total_census H
  change (∑ d ∈ S, allowed d)=fourFloors H at census
  have cap : |∑ d ∈ S.erase 1, t d| ≤ ((fourFloors H)-1)*(2/3) := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    have bound (d : ℕ) (hd : d∈S.erase 1) : |t d|≤allowed d*(2/3) := by
      rw [show t d=marks d*(fourFloors (H/d)-(H:ℚ)/(3*d)) by rfl,abs_mul]
      exact mul_le_mul (marks_cap d) (row_error (Finset.mem_Icc.mp (Finset.mem_erase.mp hd).2).1 H)
        (abs_nonneg _) ((abs_nonneg _).trans (marks_cap d))
    have up := Finset.sum_le_sum bound
    rw [←Finset.sum_mul] at up
    rw [g1,census] at right
    have eq : (∑ d ∈ S.erase 1, allowed d)=fourFloors H-1 := by linarith
    simpa only [eq] using up
  have t1 : t 1=fourFloors H-(H:ℚ)/3 := by simp [t,m1]
  rw [t1,slope_eq] at left
  have cpos : 1≤fourFloors H := by
    rw [←census,←right,g1]
    have h : 0≤∑ d ∈ S.erase 1, allowed d := Finset.sum_nonneg (fun d _ => (abs_nonneg _).trans (marks_cap d))
    linarith
  obtain ⟨low,high⟩ := abs_le.mp cap
  have bias := (bounds_at_integer H).2
  have hpos : 0<(H:ℚ) := by positivity
  apply abs_le.mpr
  constructor
  · apply le_of_mul_le_mul_left (a:=(H:ℚ)) _ hpos
    linarith
  · apply le_of_mul_le_mul_left (a:=(H:ℚ)) _ hpos
    linarith

#print axioms PALRH.TaperedNewton.old_slope_cap


/-- A linear taper is the average of the old sharp cuts in its transition strip. -/
theorem slope_as_average {H : ℕ} (hp : 0<H) :
    slope H marks=(∑ r ∈ Finset.Ico H (2*H), oldSlope r)/(H:ℚ) := by
  let D := Finset.Icc 1 (2*H)
  let R := Finset.Ico H (2*H)
  have raw (r : ℕ) (hr : r∈R) :
      oldSlope r=∑ d ∈ D, if d≤r then marks d/d else 0 := by
    have eq : D.filter (fun d => d≤r)=Finset.Icc 1 r := by
      ext d
      have upper := (Finset.mem_Ico.mp hr).2
      simp only [D,Finset.mem_filter,Finset.mem_Icc]
      omega
    rw [←Finset.sum_filter,eq,oldSlope]
  have charge (d : ℕ) (hd : d∈D) :
      (∑ r ∈ R, if d≤r then marks d/d else 0)=(H:ℚ)*(weight H d*marks d/d) := by
    have eq : R.filter (fun r => d≤r)=Finset.Ico (max H d) (2*H) := by
      ext r
      simp only [R,Finset.mem_filter,Finset.mem_Ico,max_le_iff]
      tauto
    have below := (Finset.mem_Icc.mp hd).2
    rw [←Finset.sum_filter,eq,Finset.sum_const,Nat.card_Ico,nsmul_eq_mul]
    by_cases inside : d≤H
    · simp [weight,inside,show 2*H-H=H by omega]
    · simp only [weight,inside,below,if_false,if_true,max_eq_right (by omega : H≤d)]
      field_simp
  apply (eq_div_iff (by positivity : (H:ℚ)≠0)).mpr
  rw [Finset.sum_congr rfl raw,Finset.sum_comm]
  change (∑ d ∈ D, weight H d*marks d/d)*(H:ℚ)=_
  rw [Finset.sum_congr rfl charge,←Finset.mul_sum,mul_comm]

theorem slope_cap {H : ℕ} (hp : 0<H) : |slope H marks|≤1 := by
  rw [slope_as_average hp,abs_div,abs_of_pos (by positivity : 0<(H:ℚ))]
  apply (div_le_one (by positivity)).mpr
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  have cap : (∑ r ∈ Finset.Ico H (2*H), |oldSlope r|)≤∑ _r ∈ Finset.Ico H (2*H), (1:ℚ) :=
    Finset.sum_le_sum (fun r hr => old_slope_cap (hp.trans_le (Finset.mem_Ico.mp hr).1))
  simpa [Nat.card_Ico,show 2*H-H=H by omega] using cap

/-- Every coefficient handed to the next frame has magnitude at most two. -/
theorem coefficient_cap {H : ℕ} (hp : 0<H) (n : ℕ) : |side H marks n|≤2 := by
  have g : allowed n≤1 := by
    change (if n.Coprime 6 then (1:ℚ) else 0)≤1
    split <;> norm_num
  have m : |marks n|≤1 := (marks_cap n).trans g
  by_cases inside : n≤H
  · rw [head H marks inside]
    linarith
  by_cases out : 2*H<n
  · simp [ended H marks out]
  have below : n≤2*H := le_of_not_gt out
  have after : H<n := lt_of_not_ge inside
  have w : 0≤weight H n := by
    simp only [weight,inside,below,if_false,if_true]
    positivity
  have b : 0≤bill H n := by simp [bill,after,below];positivity
  have total : weight H n+bill H n=2 := by
    simp only [weight,bill,inside,below,after,if_false,if_true,and_self]
    rw [Nat.cast_sub below,Nat.cast_mul]
    norm_num
    field_simp
    ring
  rw [side_apply]
  apply (abs_sub _ _).trans
  rw [abs_mul,abs_mul,abs_of_nonneg w,abs_of_nonneg b,←total]
  exact add_le_add (by simpa using mul_le_mul_of_nonneg_left m w)
    (by simpa using mul_le_mul_of_nonneg_left (slope_cap hp) b)

#print axioms PALRH.TaperedNewton.slope_as_average
#print axioms PALRH.TaperedNewton.coefficient_cap



private lemma side_mass {H : ℕ} (hp : 0<H) :
    (∑ d ∈ Finset.Icc 1 (2*H), |side H marks d|)≤3*(H:ℚ) := by
  let S := Finset.Icc 1 (2*H)
  have point (d : ℕ) (_hd : d∈S) : |side H marks d|≤1+(if H<d then (1:ℚ) else 0) := by
    by_cases after : H<d
    · simp only [after,if_true]
      norm_num
      exact coefficient_cap hp d
    · rw [head H marks (le_of_not_gt after)]
      have bd : allowed d≤1 := by
        change (if d.Coprime 6 then (1:ℚ) else 0)≤1
        split <;> norm_num
      simpa [after] using (marks_cap d).trans bd
  have outer : S.filter (fun d => H<d)=Finset.Ioc H (2*H) := by
    ext d
    simp only [S,Finset.mem_Icc,Finset.mem_filter,Finset.mem_Ioc]
    omega
  have card : S.card=2*H := by simp [S,Nat.card_Icc]
  have total := Finset.sum_le_sum point
  rw [Finset.sum_add_distrib,←Finset.sum_filter,outer] at total
  apply total.trans_eq
  simp [Nat.card_Ioc,card,show 2*H-H=H by omega]
  ring

theorem finite_square_cost {H : ℕ} (hp : 0<H) :
    OneTick.loss OneTick.occupied (reading H)≤
      (SquareBudget.window OneTick.occupied (reading H) H:ℝ)+9 := by
  apply (SquareBudget.loss_le_square_window_add (A:=3) H ?_).trans_eq (by norm_num)
  intro k
  have sig (d : ℕ) (hd : d∈Finset.Icc 1 (2*H)) : |signal d k|≤2/3 := by
    have p := (Finset.mem_Icc.mp hd).1
    have e := floor_and_linear p k
    rw [show signal d k=fourFloors (k/d)-(k:ℚ)/(3*d) by linarith]
    exact row_error p k
  have val : |reading H k|≤2*(H:ℚ) := by
    simp only [reading,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    have each (d : ℕ) (hd : d∈Finset.Icc 1 (2*H)) :
        |side H marks d*signal d k|≤|side H marks d| * (2/3) := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (sig d hd) (abs_nonneg _)
    have t := Finset.sum_le_sum each
    rw [←Finset.sum_mul] at t
    linarith [side_mass hp]
  have one : |OneTick.occupied k|≤1 := by unfold OneTick.occupied;split <;> norm_num
  have bound := abs_sub (OneTick.occupied k) (reading H k)
  have h1 : (1:ℚ)≤H := by exact_mod_cast hp
  exact_mod_cast (show |OneTick.occupied k-reading H k|≤3*(H:ℚ) by linarith)

#print axioms PALRH.TaperedNewton.finite_square_cost

open Filter
open scoped Topology

/-- On a squaring sequence the logarithmic change has the same limiting exponent. -/
theorem exponent_of_step {a h : ℕ → ℝ} {q : ℝ} (hn : ∀ j, h j≠0)
    (rate : Tendsto (fun j => a j/h j) atTop (𝓝 q))
    (scale : Tendsto (fun j => h (j+1)/h j) atTop (𝓝 2)) :
    Tendsto (fun j => (a (j+1)-a j)/h j) atTop (𝓝 q) := by
  have next : Tendsto (fun j => a (j+1)/h (j+1)) atTop (𝓝 q) :=
    rate.comp (tendsto_add_atTop_nat 1)
  have out := (next.mul scale).sub rate
  have point (j : ℕ) : a (j+1)/h (j+1)*(h (j+1)/h j)-a j/h j=(a (j+1)-a j)/h j := by
    field_simp [hn j,hn (j+1)]
  simpa only [point,show q*2-q=q by ring] using out

theorem eventually_rises {a h : ℕ → ℝ} {q : ℝ} (hp : ∀ j, 0<h j) (pos : 0<q)
    (rate : Tendsto (fun j => a j/h j) atTop (𝓝 q))
    (scale : Tendsto (fun j => h (j+1)/h j) atTop (𝓝 2)) :
    ∀ᶠ j in atTop, a j<a (j+1) := by
  have rise := exponent_of_step (fun j => (hp j).ne') rate scale
  filter_upwards [rise.eventually (Ioi_mem_nhds pos)] with j hj
  change 0<(a (j+1)-a j)/h j at hj
  exact sub_pos.mp ((div_pos_iff_of_pos_right (hp j)).mp hj)

#print axioms PALRH.TaperedNewton.eventually_rises

end PALRH.TaperedNewton
