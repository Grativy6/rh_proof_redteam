import PALRH.CubicFourth

open Finset Filter Set MeasureTheory
open scoped Topology BigOperators Classical
noncomputable section
namespace PALRH.OneHead
open SquarePass SquarePassBudget RectangleBalance CubicGaps

/-- This half-scale translation keeps the physical harmonic mass. -/
def half (f : ℝ → ℝ) (x : ℝ) := f (x/2)/2

def bank : ℕ → (ℝ → ℝ) → ℝ → ℝ
  | 0, f => f
  | n+1, f => fun x => f x+half (bank n f) x

theorem half_regular {f : ℝ → ℝ} (reg : Regular f) : Regular (half f) := by
  intro X
  exact ((reg (X/2)).comp (continuous_id.div_const (2:ℝ)).continuousOn
    (fun x (hx : x∈Iic X) => div_le_div_of_nonneg_right (show x≤X from hx) (by norm_num))).div_const _

theorem half_before {f : ℝ → ℝ} (quiet : Before f) : Before (half f) := by
  intro x hx
  rw [half,quiet _ (by linarith),zero_div]

theorem bank_good {f : ℝ → ℝ} (reg : Regular f) (quiet : Before f) (N : ℕ) :
    Regular (bank N f) ∧ Before (bank N f) := by
  induction N with
  | zero => exact ⟨reg,quiet⟩
  | succ n ih =>
    refine ⟨fun X => (reg X).add (half_regular ih.1 X),?_⟩
    intro x hx
    simp only [bank,quiet x hx,half_before ih.2 x hx,add_zero]

theorem last (f : ℝ → ℝ) (N : ℕ) (x : ℝ) :
    bank (N+1) f x-bank N f x=f (x/(2:ℝ)^(N+1))/(2:ℝ)^(N+1) := by
  induction N generalizing x with
  | zero => simp [bank,half]
  | succ n ih =>
    change f x+bank (n+1) f (x/2)/2-(f x+bank n f (x/2)/2)=_
    rw [show f x+bank (n+1) f (x/2)/2-(f x+bank n f (x/2)/2)=
      (bank (n+1) f (x/2)-bank n f (x/2))/2 by ring,ih]
    rw [show x/2/2^(n+1)=x/(2:ℝ)^((n+1)+1) by rw [pow_succ (2:ℝ) (n+1)];ring]
    rw [pow_succ (2:ℝ) (n+1)]
    ring

theorem recover {f : ℝ → ℝ} (N : ℕ) (quiet : Before f) {x : ℝ} (inside : x≤(2:ℝ)^N) :
    f x=bank N f x-half (bank N f) x := by
  have e := last f N x
  have small : x/(2:ℝ)^(N+1)≤1/2 := by
    apply (div_le_iff₀ (by positivity : 0<(2:ℝ)^(N+1))).mpr
    rw [pow_succ]
    linarith
  rw [quiet _ small,zero_div] at e
  change f x+half (bank N f) x-bank N f x=0 at e
  linarith

theorem window_half (K f : ℝ → ℝ) {X : ℝ} (xp : 0<X) :
    window K (half f) X=(1/Real.sqrt 2)*window K f (X/2) := by
  let g := fun t : ℝ => f t*(K ((X/2)/t)/Real.sqrt t)
  have sq := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have sp := Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)
  have eq (y : ℝ) (hy : y∈Ioc 0 X) :
      half f y*(K (X/y)/Real.sqrt y)=(1/(2*Real.sqrt 2))*g (y/2) := by
    dsimp only [half,g]
    rw [show (X/2)/(y/2)=X/y by ring,Real.sqrt_div hy.1.le]
    field_simp [(Real.sqrt_pos.mpr hy.1).ne',sp.ne']
  rw [window,setIntegral_congr_fun measurableSet_Ioc eq,integral_const_mul,
    ←intervalIntegral.integral_of_le xp.le,intervalIntegral.integral_comp_div g (by norm_num : (2:ℝ)≠0),
    zero_div,intervalIntegral.integral_of_le (by positivity : 0≤X/2),smul_eq_mul,window]
  change _=(1/Real.sqrt 2)*∫ t in Ioc 0 (X/2), g t
  ring

theorem bank_balance {f : ℝ → ℝ} (reg : Regular f) (quiet : Before f)
    {C e : ℝ} (cn : 0≤C) (ep : 0<e) (bound : ∀ X : ℝ, 0<X → balanceOf f X≤C*(2*X)^e)
    (N : ℕ) {X : ℝ} (xp : 0<X) : balanceOf (bank N f) X≤4*C*(2*X)^e := by
  induction N generalizing X with
  | zero =>
    change balanceOf f X≤_
    exact (bound X xp).trans (by nlinarith [mul_nonneg cn (Real.rpow_nonneg (by linarith : 0≤2*X) e)])
  | succ n ih =>
    have good := bank_good reg quiet n
    have eq : balanceOf (bank (n+1) f) X=balanceOf f X+(1/Real.sqrt 2)*balanceOf (bank n f) (X/2) := by
      change window gain (fun y => f y+half (bank n f) y) X=window gain f X+_*window gain (bank n f) (X/2)
      rw [←window_half _ _ xp]
      unfold window
      simp only [add_mul]
      exact integral_add (balance_int reg quiet _) (balance_int (half_regular good.1) (half_before good.2) _)
    rw [eq]
    have coef : (1/Real.sqrt 2)≤3/4 := by
      apply (div_le_iff₀ (Real.sqrt_pos.mpr (by norm_num))).mpr
      nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2),Real.sqrt_nonneg (2:ℝ)]
    have power : (2*(X/2))^e≤(2*X)^e := Real.rpow_le_rpow (by positivity) (by linarith) ep.le
    have inc := mul_le_mul_of_nonneg_right coef (mul_nonneg (by positivity : 0≤4*C) (Real.rpow_nonneg (by positivity : 0≤2*X) e))
    have step := (mul_le_mul_of_nonneg_left ((ih (X:=X/2) (by positivity)).trans
      (mul_le_mul_of_nonneg_left power (by positivity))) (by positivity : 0≤1/Real.sqrt 2))
    linarith only [bound X xp,step,inc]

theorem size_from_bank {f : ℝ → ℝ} (reg : Regular f) (quiet : Before f)
    (N : ℕ) {X : ℝ} (xp : 0<X) (inside : X≤(2:ℝ)^N) :
    size f X≤2*size (bank N f) X := by
  let b:=bank N f
  have good := bank_good reg quiet N
  have ir := size_int good.1 good.2 X
  have is := size_int (half_regular good.1) (half_before good.2) X
  have each (t : ℝ) (ht : t∈Ioc 0 X) :
      |f t| *(1/Real.sqrt t)≤|b t| *(1/Real.sqrt t)+|half b t| *(1/Real.sqrt t) := by
    rw [←add_mul,recover N quiet (ht.2.trans inside)]
    exact mul_le_mul_of_nonneg_right (abs_sub _ _) (by positivity)
  have total := setIntegral_mono_on (size_int reg quiet X) (ir.add is) measurableSet_Ioc each
  change size f X ≤ ∫ t in Ioc 0 X, |b t| *(1/Real.sqrt t)+|half b t| *(1/Real.sqrt t) at total
  rw [integral_add ir is] at total
  have ea : (fun x : ℝ => |half b x|)=half (fun y => |b y|) := by
    funext x; simp [half,abs_div]
  have hs : size (half b) X=(1/Real.sqrt 2)*size b (X/2) := by
    rw [size,ea,window_half _ _ xp,size]
  change size f X ≤ size b X+size (half b) X at total
  rw [hs] at total
  have smaller := size_mono good.1 good.2 (show X/2≤X by linarith)
  have nn : 0≤size b X := by
    apply integral_nonneg
    intro _
    positivity
  have c : 1/Real.sqrt 2≤1 := (div_le_one (Real.sqrt_pos.mpr (by norm_num))).mpr (Real.one_le_sqrt.mpr (by norm_num))
  have due := (mul_le_mul_of_nonneg_left smaller (by positivity : 0≤1/Real.sqrt 2)).trans
    (by simpa using mul_le_mul_of_nonneg_right c nn)
  change size f X≤2*size b X
  linarith only [total,due]

def BankFloors : Prop := ∀ e : ℝ, 0<e → e≤1/2 → ∃ C : ℝ, 0≤C ∧
  ∀ N : ℕ, ∃ M : ℕ, N≤M ∧ ∀ y ∈ Set.Ioc (0:ℝ) ((2:ℝ)^N),
    -(C*y^(e-1/2))≤bank M (reading M 1) y

theorem rh_of_bank_floors (known : BankFloors) : RiemannHypothesis := by
  apply PositiveArea.rh_of_sparse_up
  intro a ap B
  let e:=min (a/2) (1/4)
  have ep : 0<e := lt_min (by linarith) (by norm_num)
  have small : e≤1/2 := (min_le_right _ _).trans (by norm_num)
  have diff : 0<a-e := by linarith [show e≤a/2 from min_le_left _ _]
  obtain ⟨C,cn,lower⟩ := known e ep small
  let K:=8*(5*(4*(16*pairPrice e))*(2:ℝ)^e+6*C/e)
  let t:=(2:ℝ)^(a-e)
  have large : 1<t := Real.one_lt_rpow (by norm_num) diff
  have tends : Tendsto (fun n : ℕ => t^n) atTop atTop := tendsto_pow_atTop_atTop_of_one_lt large
  obtain ⟨M,late⟩ := eventually_atTop.mp (tends.eventually_gt_atTop K)
  let N:=max B M
  let H:=(2:ℝ)^N
  have hp : 0<H := by dsimp [H];positivity
  have cost : K≤H^(a-e) := by
    have eq : H^(a-e)=t^N := by
      dsimp only [H,t]
      rw [←Real.rpow_natCast_mul (by norm_num : (0:ℝ)≤2),←Real.rpow_mul_natCast (by norm_num : (0:ℝ)≤2),mul_comm]
    rw [eq];exact (late _ (le_max_right _ _)).le
  obtain ⟨Khead,nm,here⟩ := lower N
  let f:=reading Khead 1
  have good := reading_good Khead 1
  have bg:=bank_good good.1 good.2 Khead
  have ready : H≤(2:ℝ)^Khead := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) nm
  have gross := signed_size bg.1 bg.2 hp ep cn here
  have base (x : ℝ) (pos : 0<x) : balanceOf f x≤(16*pairPrice e)*(2*x)^e := by
    simpa [f] using balance_bound Khead 1 ep x pos
  have funded := bank_balance good.1 good.2 (mul_nonneg (by norm_num) (pair_price_pos ep).le) ep base Khead hp
  rw [Real.mul_rpow (by norm_num) hp.le] at funded
  have ret := size_from_bank good.1 good.2 Khead hp ready
  have recov := recovered_size Khead 1 hp ready
  rw [pow_one] at recov
  have up : PositiveArea.up H≤size edge H := by
    apply setIntegral_mono_on (PositiveArea.up_integrable H)
      (size_int edge_continuousOn (fun _ hy => edge_before hy) H) measurableSet_Ioc
    intro y _
    change max (edge y) 0/Real.sqrt y≤|edge y| *(1/Real.sqrt y)
    rw [mul_one_div]
    exact div_le_div_of_nonneg_right (max_le (le_abs_self _) (abs_nonneg _)) (Real.sqrt_nonneg _)
  have bill : PositiveArea.up H≤K*H^e := by
    dsimp only [K]
    change size f H≤2*size (bank Khead f) H at ret
    change size edge H≤4*size f H at recov
    linarith only [up,recov,ret,gross,funded,
      show 8*(5*((4*(16*pairPrice e))*((2:ℝ)^e*H^e))+6*C*(H^e/e))=
        8*(5*(4*(16*pairPrice e))*(2:ℝ)^e+6*C/e)*H^e by ring]
  refine ⟨2^N,(le_max_left B M).trans Nat.lt_two_pow_self.le,?_⟩
  push_cast
  change PositiveArea.up H≤H^a
  apply bill.trans
  have result := mul_le_mul_of_nonneg_right cost (Real.rpow_nonneg hp.le e)
  rwa [←Real.rpow_add hp,sub_add_cancel] at result

#print axioms PALRH.OneHead.rh_of_bank_floors
end PALRH.OneHead
