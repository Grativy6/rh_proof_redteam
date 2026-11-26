import PALRH.ReferencePrice
import PALRH.OneHeadPhysical
import Mathlib.Analysis.SpecificLimits.Normed

open Finset Set Filter MeasureTheory
open scoped Topology BigOperators Classical
noncomputable section
namespace PALRH.DenseSquares
open SquarePass SquarePassBudget RectangleBalance TaperedNewton OneHead

/-- A full square pass has normalized coefficient h(r)/r^2 at the scale x/r^2. -/
def grid (T : ℕ) (h : ℕ → ℝ) (f : ℝ → ℝ) (x : ℝ) :=
  ∑ r ∈ Finset.Icc 1 T, h r/(r:ℝ)*shift r f x

def gate (r : ℕ) : ℝ := allowed r
def inverseMark (r : ℕ) : ℝ := marks r

private theorem gate_bounds (r : ℕ) : 0≤gate r ∧ gate r≤1 := by
  by_cases ok : r.Coprime 6
  · have h : allowed r=1 := by change (if r.Coprime 6 then (1:ℚ) else 0)=1; rw [if_pos ok]
    simp [gate,h]
  · have h : allowed r=0 := by change (if r.Coprime 6 then (1:ℚ) else 0)=0; rw [if_neg ok]
    simp [gate,h]

theorem grid_good (T : ℕ) (h : ℕ → ℝ) {f : ℝ → ℝ} (reg : Regular f) (quiet : Before f) :
    Regular (grid T h f) ∧ Before (grid T h f) := by
  constructor
  · intro X
    exact continuousOn_finsetSum _ (fun r hr => continuousOn_const.mul
      (shift_regular (Finset.mem_Icc.mp hr).1 reg X))
  · intro x hx
    apply Finset.sum_eq_zero
    intro r hr
    rw [shift_before (Finset.mem_Icc.mp hr).1 quiet _ hx,mul_zero]

/-- The rough Möbius weights undo the same physical square pass. -/
theorem return_on_head (T : ℕ) (tp : 0<T) {f : ℝ → ℝ} (quiet : Before f)
    {x : ℝ} (_xp : 0≤x) (inside : x≤T) :
    grid T inverseMark (grid T gate f) x=f x := by
  let u:=fun n : ℕ => f (x/(n:ℝ)^2)/(n:ℝ)^2
  have stop (n : ℕ) (large : T<n) : u n=0 := by
    have nr : (T:ℝ)<n := by exact_mod_cast large
    have n2 : (2:ℝ)≤n := by exact_mod_cast (show 2≤n by omega)
    have den : 0<(n:ℝ)^2 := by positivity
    have early : x/(n:ℝ)^2≤1/2 := (div_le_iff₀ den).mpr (by
      nlinarith [mul_nonneg (sub_nonneg.mpr n2) (Nat.cast_nonneg (α:=ℝ) n)])
    dsimp [u];rw [quiet _ early,zero_div]
  have id := ReferencePrice.invert_ray tp (by decide : 0<1) u stop
  simp only [ReferencePrice.invert,ReferencePrice.ray,mul_one] at id
  have u1 : u 1=f x := by simp [u]
  rw [u1] at id
  rw [←id]
  unfold grid
  apply Finset.sum_congr rfl
  intro d _
  rw [shift]
  rw [Finset.sum_div,Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  dsimp only [gate,inverseMark,shift,u]
  rw [Nat.cast_mul,mul_pow,show x/(d:ℝ)^2/k^2=x/((k:ℝ)^2*d^2) by ring]
  ring

def harmonic (T : ℕ) : ℝ := ∑ n ∈ Finset.Icc 1 T, 1/(n:ℝ)

theorem harmonic_pow (N : ℕ) : harmonic (2^N)≤(N:ℝ)+1 := by
  induction N with
  | zero => norm_num [harmonic]
  | succ n ih =>
    let T : ℕ:=2^n
    have tp : 0<T := by dsimp [T];positivity
    have tr : 0<(T:ℝ) := by exact_mod_cast tp
    have union : Finset.Icc 1 T ∪ Finset.Ioc T (2*T)=Finset.Icc 1 (2*T) := by
      ext r
      simp only [Finset.mem_union,Finset.mem_Icc,Finset.mem_Ioc]
      omega
    have dis : Disjoint (Finset.Icc 1 T) (Finset.Ioc T (2*T)) := Finset.disjoint_left.mpr
      (fun r a b => (Nat.not_lt_of_ge (Finset.mem_Icc.mp a).2) (Finset.mem_Ioc.mp b).1)
    have tail : (∑ r ∈ Finset.Ioc T (2*T), 1/(r:ℝ))≤1 := calc
      _ ≤ ∑ _r ∈ Finset.Ioc T (2*T), 1/(T:ℝ) := Finset.sum_le_sum (fun r hr =>
        one_div_le_one_div_of_le tr (by exact_mod_cast (Finset.mem_Ioc.mp hr).1.le))
      _ = 1 := by rw [Finset.sum_const,Nat.card_Ioc,show 2*T-T=T by omega,nsmul_eq_mul];field_simp
    rw [pow_succ',harmonic,←union,Finset.sum_union dis]
    change (∑ r ∈ Finset.Icc 1 T, 1/(r:ℝ))≤_ at ih
    push_cast
    linarith

theorem grid_balance (T : ℕ) {f : ℝ → ℝ} (reg : Regular f) (quiet : Before f)
    {C e : ℝ} (cn : 0≤C) (ep : 0<e)
    (bound : ∀ x : ℝ, 0<x → balanceOf f x≤C*(2*x)^e) {X : ℝ} (xp : 0<X) :
    balanceOf (grid T gate f) X ≤ harmonic T*(C*(2*X)^e) := by
  let I:=Finset.Icc 1 T
  have eq : balanceOf (grid T gate f) X=∑ r ∈ I,gate r/r*balanceOf f (X/(r:ℝ)^2) := by
    have each (y : ℝ) : grid T gate f y*(gain (X/y)/Real.sqrt y)=∑ r ∈ I,
        (gate r/r)*(shift r f y*(gain (X/y)/Real.sqrt y)) := by
      rw [grid,Finset.sum_mul]
      apply Finset.sum_congr rfl;intro r _;ring
    rw [balanceOf,window,setIntegral_congr_fun measurableSet_Ioc (fun y _ => each y),
      integral_finsetSum _ (fun r hr => (balance_int (shift_regular (Finset.mem_Icc.mp hr).1 reg)
        (shift_before (Finset.mem_Icc.mp hr).1 quiet) X).const_mul _)]
    apply Finset.sum_congr rfl
    intro r hr
    rw [integral_const_mul]
    congr 1
    exact window_shift _ _ (Finset.mem_Icc.mp hr).1 xp
  rw [eq,harmonic,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro r hr
  have rp : 0<r := (Finset.mem_Icc.mp hr).1
  have one : (1:ℝ)≤(r:ℝ)^2 := by exact_mod_cast (pow_pos rp 2 : 0<r^2)
  have pos : 0<(r:ℝ)^2 := by positivity
  have power := Real.rpow_le_rpow (by positivity : 0≤2*(X/(r:ℝ)^2))
    (show 2*(X/(r:ℝ)^2)≤2*X by linarith [div_le_self xp.le one]) ep.le
  calc
    _ ≤ (gate r/r)*(C*(2*X)^e) := mul_le_mul_of_nonneg_left
      ((bound _ (div_pos xp pos)).trans (mul_le_mul_of_nonneg_left power cn))
      (div_nonneg (gate_bounds r).1 (by positivity))
    _ ≤ _ := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (gate_bounds r).2 (by positivity))
      (by positivity)

theorem inverse_price {T : ℕ} (tp : 0<T) {f : ℝ → ℝ} (reg : Regular f) (quiet : Before f)
    {X : ℝ} (xp : 0<X) (inside : X≤T) :
    size f X≤harmonic T*size (grid T gate f) X := by
  let b:=grid T gate f
  let I:=Finset.Icc 1 T
  have good := grid_good T gate reg quiet
  have weight (r : ℕ) : |inverseMark r|≤1 := FourthAccounts.mark_cap r
  have each (y : ℝ) (hy : y∈Set.Ioc 0 X) : |f y| *(1/Real.sqrt y)≤
      ∑ r ∈ I,(1/(r:ℝ))*(|shift r b y| *(1/Real.sqrt y)) := by
    rw [←return_on_head T tp quiet hy.1.le (hy.2.trans inside)]
    change |∑ r ∈ I,inverseMark r/r*shift r b y| *(1/Real.sqrt y)≤_
    apply (mul_le_mul_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (by positivity : 0≤1/Real.sqrt y)).trans
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro r hr
    rw [abs_mul,abs_div,abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) r),←mul_assoc]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (weight r) (by positivity)) (abs_nonneg _)
  have total:=setIntegral_mono_on (size_int reg quiet X)
    (integrable_finsetSum _ (fun r hr => (size_int (shift_regular (Finset.mem_Icc.mp hr).1 good.1)
      (shift_before (Finset.mem_Icc.mp hr).1 good.2) X).const_mul _)) measurableSet_Ioc each
  change size f X≤∫ y in Set.Ioc 0 X,∑ r ∈ I,1/(r:ℝ)*(|shift r b y| *(1/Real.sqrt y)) at total
  rw [integral_finsetSum _ (fun r hr => (size_int (shift_regular (Finset.mem_Icc.mp hr).1 good.1)
      (shift_before (Finset.mem_Icc.mp hr).1 good.2) X).const_mul _)] at total
  apply total.trans
  rw [harmonic,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro r hr
  rw [integral_const_mul]
  change 1/(r:ℝ)*size (shift r b) X≤_
  rw [size_shift (Finset.mem_Icc.mp hr).1 _ xp]
  have big : (1:ℝ)≤(r:ℝ)^2 := by exact_mod_cast (pow_pos (Finset.mem_Icc.mp hr).1 2 : 0<r^2)
  exact mul_le_mul_of_nonneg_left (size_mono good.1 good.2 (div_le_self xp.le big)) (by positivity)

def readingAt (N : ℕ) := grid (2^N) gate (bank N (SquarePass.reading N 1))

/-- One output floor on the full square pass suffices. Its inverse can spend at
most one harmonic sum in the critical area norm. -/
theorem rh_of_dense_floors
    (known : ∀ e : ℝ, 0<e → e≤1/2 → ∃ C : ℝ, 0≤C ∧ ∀ N : ℕ,
      ∀ y ∈ Ioc (0:ℝ) ((2:ℝ)^N), -(C*y^(e-1/2))≤readingAt N y) : RiemannHypothesis := by
  apply PositiveArea.rh_of_sparse_up
  intro a ap B
  let e:=min (a/2) (1/4)
  have ep : 0<e := lt_min (by linarith) (by norm_num)
  have small : e≤1/2 := (min_le_right _ _).trans (by norm_num)
  have gap : 0<a-e := by linarith [show e≤a/2 from min_le_left _ _]
  obtain ⟨C,cn,check⟩:=known e ep small
  let D:=4*(16*pairPrice e)*(2:ℝ)^e
  let K:=8*(5*D+6*C/e)
  have dn : 0≤D := by dsimp [D];positivity [pair_price_pos ep]
  have kn : 0≤K := by dsimp [K];positivity
  let t:=(2:ℝ)^(a-e)
  have big : 1<t := Real.one_lt_rpow (by norm_num) gap
  have seq:= (tendsto_pow_const_div_const_pow_of_one_lt 2 big).const_mul (4*K)
  have ev : ∀ᶠ n : ℕ in atTop, 4*K*((n:ℝ)^2/t^n)<1 := by
    apply seq.eventually_lt_const
    simp
  obtain ⟨L,late⟩:=eventually_atTop.mp ev
  let N:=max (max B L) 1
  let H:ℝ:=2^N
  have xp : 0<H := by dsimp [H];positivity
  have one : (1:ℝ)≤N := by exact_mod_cast (le_max_right (max B L) 1)
  have cost : K*((N:ℝ)+1)^2 ≤ H^(a-e) := by
    have bound:=late N ((le_max_right B L).trans (le_max_left _ _))
    have teq : H^(a-e)=t^N := by
      dsimp [H,t]
      rw [←Real.rpow_natCast_mul (by norm_num : (0:ℝ)≤2),←Real.rpow_mul_natCast (by norm_num : (0:ℝ)≤2),mul_comm]
    rw [teq]
    have mult : 4*K*(N:ℝ)^2<t^N := by
      apply (div_lt_one (pow_pos (zero_lt_one.trans big) N)).mp
      simpa only [mul_div_assoc] using bound
    have sq:=pow_le_pow_left₀ (by positivity : 0≤(N:ℝ)+1) (by linarith : (N:ℝ)+1≤2*N) 2
    nlinarith [mul_le_mul_of_nonneg_left sq kn]
  let f:=SquarePass.reading N 1
  let b:=bank N f
  let g:=readingAt N
  have fg:=reading_good N 1
  have bg:=bank_good fg.1 fg.2 N
  have gg:=grid_good (2^N) gate bg.1 bg.2
  have covered : H≤((2^N:ℕ):ℝ) := by simp [H]
  have fund (x : ℝ) (p : 0<x) : balanceOf f x≤(16*pairPrice e)*(2*x)^e := by
    simpa [f] using balance_bound N 1 ep x p
  have bn : 0≤16*pairPrice e := mul_nonneg (by norm_num) (pair_price_pos ep).le
  have cb := fun x (p : 0<x) => bank_balance fg.1 fg.2 bn ep fund N p
  have priced := grid_balance (2^N) bg.1 bg.2 (by positivity : 0≤4*(16*pairPrice e)) ep cb xp
  have harm:=harmonic_pow N
  have hnon : 0≤harmonic (2^N) := Finset.sum_nonneg (fun _ _ => by positivity)
  have sized := CubicGaps.signed_size gg.1 gg.2 xp ep cn (check N)
  have recover1:=inverse_price (by positivity : 0<2^N) bg.1 bg.2 xp covered
  have recover2:=size_from_bank fg.1 fg.2 N xp (le_refl H)
  have recover3:=recovered_size N 1 xp (le_refl H)
  rw [pow_one] at recover3
  change size b H≤harmonic (2^N)*size g H at recover1
  change size f H≤2*size b H at recover2
  change size edge H≤4*size f H at recover3
  change size g H≤5*balanceOf g H+6*C*(H^e/e) at sized
  change balanceOf g H≤harmonic (2^N)*(4*(16*pairPrice e)*(2*H)^e) at priced
  rw [Real.mul_rpow (by norm_num) xp.le] at priced
  have hp : 0≤H^e := Real.rpow_nonneg xp.le _
  have pr : balanceOf g H≤((N:ℝ)+1)*(D*H^e) := by
    apply priced.trans
    dsimp [D]
    convert mul_le_mul_of_nonneg_right harm
      (show 0≤4*(16*pairPrice e)*(2:ℝ)^e*H^e by positivity) using 1
    ring
  have gn : 0≤size g H := by apply integral_nonneg; intro y; positivity
  have rb := recover1.trans (mul_le_mul_of_nonneg_right harm gn)
  have sg : size g H≤((N:ℝ)+1)*(5*D+6*C/e)*H^e := by
    have inc:=mul_nonneg (by positivity : 0≤(N:ℝ)) (by positivity : 0≤6*C/e*H^e)
    have eq : ((N:ℝ)+1)*(5*D+6*C/e)*H^e =
        5*(((N:ℝ)+1)*(D*H^e))+6*C*(H^e/e)+(N:ℝ)*(6*C/e*H^e) := by ring
    rw [eq]
    linarith only [sized,pr,inc]
  have rbb:=rb.trans (mul_le_mul_of_nonneg_left sg (by positivity))
  have up : PositiveArea.up H≤size edge H := by
    apply setIntegral_mono_on (PositiveArea.up_integrable H)
      (size_int edge_continuousOn (fun _ hy => edge_before hy) H) measurableSet_Ioc
    intro y _
    change max (edge y) 0/Real.sqrt y≤|edge y| *(1/Real.sqrt y)
    rw [mul_one_div]
    exact div_le_div_of_nonneg_right (max_le (le_abs_self _) (abs_nonneg _)) (Real.sqrt_nonneg _)
  have bill : PositiveArea.up H≤K*((N:ℝ)+1)^2*H^e := by
    dsimp only [K]
    nlinarith only [up,recover3,recover2,rbb]
  refine ⟨2^N,((le_max_left B L).trans (le_max_left _ _)).trans Nat.lt_two_pow_self.le,?_⟩
  push_cast
  change PositiveArea.up H≤H^a
  apply bill.trans
  simpa only [←Real.rpow_add xp,sub_add_cancel] using mul_le_mul_of_nonneg_right cost hp

#print axioms PALRH.DenseSquares.return_on_head
#print axioms PALRH.DenseSquares.inverse_price
#print axioms PALRH.DenseSquares.rh_of_dense_floors
end PALRH.DenseSquares
