import PALRH.OrdinaryPrimeGrid

open Set Finset Filter MeasureTheory
open scoped BigOperators Topology
noncomputable section
namespace PALRH.SquarePass
open RectangleBalance

/-- Divide the physical side by a square and pay with its positive square root. -/
def shift (p : ℕ) (f : ℝ → ℝ) (x : ℝ) := f (x/(p:ℝ)^2)/p

def sweep (N p : ℕ) (f : ℝ → ℝ) (x : ℝ) := ∑ i ∈ Finset.range (N+1), shift (p^i) f x
def layer (N : ℕ) (f : ℝ → ℝ) := sweep N 2 (sweep N 3 f)
def reading (N : ℕ) : ℕ → ℝ → ℝ
  | 0 => edge
  | k+1 => layer N (reading N k)

def Regular (f : ℝ → ℝ) : Prop := ∀ X : ℝ, ContinuousOn f (Set.Iic X)
def Before (f : ℝ → ℝ) : Prop := ∀ x : ℝ, x≤1/2 → f x=0

theorem shift_regular {p : ℕ} (_hp : 0<p) {f : ℝ → ℝ} (cont : Regular f) : Regular (shift p f) := by
  intro X
  have h : ContinuousOn (fun y : ℝ => f (y/(p:ℝ)^2)) (Set.Iic X) :=
    (cont (X/(p:ℝ)^2)).comp (continuous_id.div_const _).continuousOn
      (fun y (hx : y∈Set.Iic X) => div_le_div_of_nonneg_right (show y≤X from hx) (sq_nonneg _))
  exact h.div_const _

theorem shift_before {p : ℕ} (hp : 0<p) {f : ℝ → ℝ} (early : Before f) : Before (shift p f) := by
  intro x small
  have pp : (1:ℝ)≤p := by exact_mod_cast hp
  have den : 0<(p:ℝ)^2 := by positivity
  have one : (1:ℝ)≤(p:ℝ)^2 := one_le_pow₀ pp
  rw [shift,early _ ((div_le_iff₀ den).mpr (by linarith)),zero_div]

theorem sweep_regular (N : ℕ) {p : ℕ} (hp : 0<p) {f : ℝ → ℝ} (cont : Regular f) :
    Regular (sweep N p f) := by
  intro X
  exact continuousOn_finsetSum _ (fun i _ => shift_regular (pow_pos hp i) cont X)

theorem sweep_before (N : ℕ) {p : ℕ} (hp : 0<p) {f : ℝ → ℝ} (early : Before f) :
    Before (sweep N p f) := by
  intro x hx
  apply Finset.sum_eq_zero
  exact fun i _ => shift_before (pow_pos hp i) early x hx

theorem reading_good (N k : ℕ) : Regular (reading N k) ∧ Before (reading N k) := by
  induction k with
  | zero => exact ⟨edge_continuousOn,fun _ hx => edge_before hx⟩
  | succ k old =>
    exact ⟨sweep_regular N (by decide : 0<2) (sweep_regular N (by decide : 0<3) old.1),
      sweep_before N (by decide : 0<2) (sweep_before N (by decide : 0<3) old.2)⟩

theorem shift_twice (p q : ℕ) (f : ℝ → ℝ) (x : ℝ) :
    shift p (shift q f) x=shift (p*q) f x := by
  dsimp [shift];push_cast
  rw [show x/(p:ℝ)^2/(q:ℝ)^2=x/((p:ℝ)*q)^2 by ring]
  ring

theorem shift_sweep (a p N : ℕ) (f : ℝ → ℝ) (x : ℝ) :
    shift a (sweep N p f) x=∑ i ∈ Finset.range (N+1), shift (a*p^i) f x := by
  change (∑ i ∈ Finset.range (N+1), shift (p^i) f (x/(a:ℝ)^2))/a=_
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  exact shift_twice a (p^i) f x

theorem subtract_shift (N p : ℕ) (f : ℝ → ℝ) (x : ℝ) :
    sweep N p f x-shift p (sweep N p f) x=f x-shift (p^(N+1)) f x := by
  rw [shift_sweep]
  dsimp only [sweep]
  simp_rw [←pow_succ']
  rw [Finset.sum_range_succ' (fun i => shift (p^i) f x) N,Finset.sum_range_succ (fun i => shift (p^(i+1)) f x)]
  simp [shift]

theorem on_head {p : ℕ} (atleast : 2≤p) (N : ℕ) {f : ℝ → ℝ} (early : Before f) {x : ℝ}
    (inside : x≤(2:ℝ)^N) : f x=sweep N p f x-shift p (sweep N p f) x := by
  have enough : 2*2^N≤p^(N+1) := by rw [←pow_succ']; exact Nat.pow_le_pow_left atleast _
  have pow : (2:ℝ)*2^N≤((p^(N+1):ℕ):ℝ) := by exact_mod_cast enough
  have pn : 0<((p^(N+1):ℕ):ℝ) := by exact_mod_cast pow_pos (show 0<p by omega) (N+1)
  have pn1 : 1≤((p^(N+1):ℕ):ℝ) := by exact_mod_cast (show 0<p^(N+1) from pow_pos (show 0<p by omega) _)
  have far : x/((p^(N+1):ℕ):ℝ)^2≤1/2 := (div_le_iff₀ (sq_pos_of_pos pn)).mpr (by
    nlinarith [mul_nonneg (sub_nonneg.mpr pn1) pn.le])
  rw [subtract_shift,shift,early _ far]
  simp

/-- At every real row through the head, three earlier values and the new value restore the old reading. -/
theorem inverse (N k : ℕ) {x : ℝ} (xp : 0≤x) (inside : x≤(2:ℝ)^N) :
    reading N k x=reading N (k+1) x-reading N (k+1) (x/4)/2-
      reading N (k+1) (x/9)/3+reading N (k+1) (x/36)/6 := by
  let A := reading N k
  let P := sweep N 3 A
  let F := reading N (k+1)
  have raw := (reading_good N k).2
  have old : A x=P x-shift 3 P x := on_head (by decide : 2≤3) N raw inside
  have quiet : Before P := sweep_before N (by decide : 0<3) raw
  have first : P x=F x-shift 2 F x := on_head (by decide : 2≤2) N quiet inside
  have second : P (x/9)=F (x/9)-shift 2 F (x/9) :=
    on_head (by decide : 2≤2) N quiet ((div_le_self xp (by norm_num : (1:ℝ)≤9)).trans inside)
  change A x=F x-F (x/4)/2-F (x/9)/3+F (x/36)/6
  change A x=P x-P (x/(3:ℝ)^2)/3 at old
  norm_num at old
  rw [old,first,second]
  dsimp only [shift]
  norm_num
  rw [show x/9/4=x/36 by ring]
  ring

/-- The scalar area and the fixed rectangle comparison use the same reciprocal-coordinate weight. -/
def window (K f : ℝ → ℝ) (X : ℝ) := ∫ y in Set.Ioc 0 X, f y*(K (X/y)/Real.sqrt y)
def size (f : ℝ → ℝ) (X : ℝ) := window (fun _ => 1) (fun x => |f x|) X
def balanceOf (f : ℝ → ℝ) (X : ℝ) := window gain f X

theorem window_shift (K f : ℝ → ℝ) {p : ℕ} (pp : 0<p) {X : ℝ} (xp : 0<X) :
    window K (shift p f) X=window K f (X/(p:ℝ)^2) := by
  have pr : 0<(p:ℝ) := by exact_mod_cast pp
  let g := fun t : ℝ => f t*(K ((X/(p:ℝ)^2)/t)/Real.sqrt t)
  have eq (y : ℝ) (hy : y∈Set.Ioc 0 X) :
      shift p f y*(K (X/y)/Real.sqrt y)=(1/(p:ℝ)^2)*g (y/(p:ℝ)^2) := by
    dsimp only [shift,g]
    rw [show (X/(p:ℝ)^2)/(y/(p:ℝ)^2)=X/y by field_simp,Real.sqrt_div hy.1.le,Real.sqrt_sq pr.le]
    field_simp [(Real.sqrt_pos.mpr hy.1).ne',pr.ne']
  rw [window,setIntegral_congr_fun measurableSet_Ioc eq,integral_const_mul,
    ←intervalIntegral.integral_of_le xp.le,intervalIntegral.integral_comp_div g (sq_pos_of_pos pr).ne',
    zero_div,intervalIntegral.integral_of_le (div_nonneg xp.le (sq_nonneg _)),smul_eq_mul]
  change _=∫ y in Set.Ioc 0 (X/(p:ℝ)^2), g y
  field_simp

#print axioms PALRH.SquarePass.inverse
#print axioms PALRH.SquarePass.window_shift
end PALRH.SquarePass
