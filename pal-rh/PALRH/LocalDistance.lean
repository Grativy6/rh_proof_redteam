import PALRH.ShapeObservation
import PALRH.OrderedTransport

open Finset
open scoped BigOperators

namespace PALRH.LocalDistance
open ShapeObservation

/-- The n diagonal positions have distance zero. Positive distances have two orientations. -/
def through (n h m : ℕ) := h*n+2*h*plainArea n m

def mass (n d : ℕ) := 2*((n-d)*tickAt n d)

def leftEnd (n h W p : ℕ) := if p≤W then 0 else through n h (p-W-1)
def rightEnd (n h W p : ℕ) := through n h (min n (p+W))

/-- Each source digit is sent to one free ordinal in the cube within W distance columns.
The unused capacity is smaller than one whole layer. -/
def localPlacement (n h W : ℕ) : Prop :=
  through n h n < 2*prefixJobs n n+n^2 ∧
  ∃ put : ℕ → ℕ → ℕ,
    (∀ p<n+2, ∀ t<mass n p, put p t∈Ico (leftEnd n h W p) (rightEnd n h W p)) ∧
    (∀ p<n+2, ∀ q<n+2, ∀ t<mass n p, ∀ u<mass n q, put p t=put q u → p=q ∧ t=u)

private theorem area_step (n m : ℕ) : plainArea n (m+1)=plainArea n m+(n-(m+1)) := by
  unfold plainArea;rw [sum_Icc_succ_top (by omega : 1≤m+1)]

private theorem area_full (n : ℕ) : 2*plainArea n n+n=n^2 := by
  have general (m : ℕ) (mn : m≤n) :
      2*plainArea n m+m*(m+1)=2*n*m := by
    induction m with
    | zero => simp [plainArea]
    | succ m ih =>
      have old:=ih (by omega)
      have diff:=Nat.sub_add_cancel mn
      rw [area_step]
      nlinarith only [old,diff]
  have eq:=general n le_rfl
  nlinarith only [eq]

private theorem full (n h : ℕ) : through n h n=h*n^2 := by
  have eq:=congrArg (h*·) (area_full n)
  unfold through
  nlinarith only [eq]

private theorem cumulative (n m : ℕ) : ∑ d ∈ Icc 0 m,mass n d=2*prefixJobs n m := by
  induction m with
  | zero => simp [mass,tickAt,prefixJobs]
  | succ m ih =>
    rw [sum_Icc_succ_top (by omega : 0≤m+1),ih]
    unfold prefixJobs
    rw [sum_Icc_succ_top (by omega : 1≤m+1),Nat.mul_add]
    rfl

private theorem suffix (n m : ℕ) (mn : m≤n) :
    2*prefixJobs n m+∑ d ∈ Icc (m+1) (n+1),mass n d=2*prefixJobs n n := by
  rw [←cumulative,←Finset.sum_union]
  · rw [show Icc 0 m ∪ Icc (m+1) (n+1)=Icc 0 (n+1) by ext a;simp only [mem_union,mem_Icc];omega]
    rw [sum_Icc_succ_top (by omega : 0≤n+1),cumulative]
    simp [mass]
  · apply Finset.disjoint_left.mpr
    intro a ha hb
    simp only [mem_Icc] at ha hb
    omega

private theorem monotone_through (n h : ℕ) : Monotone (through n h) := by
  apply monotone_nat_of_le_succ
  intro i;unfold through;rw [area_step,Nat.mul_add];omega

private theorem extra (n h i W : ℕ) : through n h (i+W) ≤ through n h i+2*h*n*W := by
  induction W with
  | zero => simp
  | succ W ih =>
    have more:=Nat.mul_le_mul_left (2*h) (Nat.sub_le n (i+W+1))
    rw [show i+(W+1)=i+W+1 by omega]
    simp only [through,area_step,Nat.mul_add,Nat.mul_succ] at ih ⊢
    omega

private theorem chart_limits (n h W : ℕ) :
    Monotone (leftEnd n h W) ∧ Monotone (rightEnd n h W) ∧
    ∀ p<n+2, leftEnd n h W p≤rightEnd n h W p := by
  have mono:=monotone_through n h
  refine ⟨?_,?_,?_⟩
  · intro a b ab
    unfold leftEnd
    split_ifs with h₁ h₂ h₂ <;> first | omega | exact mono (by omega)
  · intro a b ab
    exact mono (by omega)
  · intro p hp
    unfold leftEnd rightEnd
    split_ifs with hpW
    · omega
    · apply mono
      omega

/-- Only the two exposed boundary strips and the genuine unoccupied cells can change a prefix. -/
theorem crossing_bound {n h W : ℕ} (places : localPlacement n h W) (m : ℕ) (mn : m≤n) :
    let e:=n^2+2*h*n*(W+1)
    prefixJobs n m≤h*plainArea n m+e ∧ h*plainArea n m≤prefixJobs n m+e := by
  obtain ⟨slack,put,lands,inj⟩:=places
  obtain ⟨ml,mr,ok⟩:=chart_limits n h W
  have mcap:=OrderedTransport.necessary_interval ml mr ok put lands inj (i:=0) (j:=m) (by omega) (by omega)
  have ecap:=OrderedTransport.necessary_interval ml mr ok put lands inj (i:=m+1) (j:=n+1) (by omega) (by omega)
  rw [cumulative] at mcap
  have start : leftEnd n h W 0=0 := by simp [leftEnd]
  rw [start,Nat.zero_add] at mcap
  have upper := mcap.trans ((monotone_through n h (min_le_right n (m+W))).trans (extra n h m W))
  have endAt : rightEnd n h W (n+1)=through n h n := by unfold rightEnd;rw [min_eq_left (by omega)]
  rw [endAt] at ecap
  have su:=suffix n m mn
  have inner : through n h m≤leftEnd n h W (m+1)+h*n+2*h*n*W := by
    by_cases early : m<W
    · have start0 : through n h 0=h*n := by simp [through,plainArea]
      have lim:=extra n h 0 W
      simp only [Nat.zero_add,start0] at lim
      have z:=(monotone_through n h early.le).trans lim
      omega
    · have mw : W≤m := by omega
      have first : leftEnd n h W (m+1)=through n h (m-W) := by
        unfold leftEnd;rw [if_neg (by omega),show m+1-W-1=m-W by omega]
      have lim:=extra n h (m-W) W
      rw [Nat.sub_add_cancel mw] at lim
      omega
  dsimp
  unfold through at upper inner
  simp only [Nat.mul_succ]
  constructor <;> nlinarith only [upper,inner,ecap,su,slack,Nat.zero_le (h*n),Nat.zero_le (n^2),Nat.zero_le (2*h*n*W)]


/-- A board with less than one empty layer already supplies its own coarse height bound. -/
theorem measured_height {n h W : ℕ} (np : 0<n) (places : localPlacement n h W) :
    h≤11*n.sqrt := by
  have slack:=places.1
  rw [full] at slack
  have volume : (h:ℝ)*(n:ℝ)^2<2*(prefixJobs n n:ℝ)+(n:ℝ)^2 := by exact_mod_cast slack
  have cost:=prefix_calibration n n np le_rfl
  have up:=(abs_sub_le_iff.mp cost).1
  have nr : 0≤(n:ℝ) := Nat.cast_nonneg _
  have xr : 0≤(n.sqrt:ℝ) := Nat.cast_nonneg _
  have ticks : (∑ d ∈ Icc 1 n,(tickAt n d:ℝ))≤3*n+(n.sqrt:ℝ)*(2*n) := by
    linarith only [up,mul_le_mul_of_nonneg_left (theta_price n) xr]
  have weighted : (prefixJobs n n:ℝ)≤(n:ℝ)*(∑ d ∈ Icc 1 n,(tickAt n d:ℝ)) := by
    unfold prefixJobs
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le n i) (Nat.cast_nonneg _)
  have total : 2*(prefixJobs n n:ℝ)≤(6+4*(n.sqrt:ℝ))*(n:ℝ)^2 := by
    nlinarith only [weighted,mul_le_mul_of_nonneg_left ticks nr]
  have level : (h:ℝ)<7+4*(n.sqrt:ℝ) := by
    by_contra! bad
    nlinarith only [mul_le_mul_of_nonneg_right bad (sq_nonneg (n:ℝ)),volume,total]
  have root : 1≤n.sqrt := Nat.sqrt_pos.mpr np
  have round : h<7+4*n.sqrt := by exact_mod_cast level
  omega

/-- A square-root distance budget with a quadratic allowance in the board index on one
sequence of self-sized boards suffices for the usual Mathlib Riemann hypothesis. -/
theorem rh_of_local_moves (witness : ∃ B : ℕ, ∀ j : ℕ, ∃ h W : ℕ,
    localPlacement (16^(j+1)) h W ∧ W≤B*4^(j+1)*(j+1)^2) : RiemannHypothesis := by
  obtain ⟨B,boards⟩:=witness
  apply rh_of_strip_readings
  refine ⟨1+22*(B+1),?_⟩
  intro j
  obtain ⟨h,W,places,reach⟩:=boards j
  let n:ℕ:=16^(j+1)
  let x:ℕ:=4^(j+1)
  let T:ℕ:=(j+1)^2
  have sq : x^2=n := by
    dsimp [x,n];rw [←pow_mul,mul_comm (j+1) 2,pow_mul];rfl
  have xs : n.sqrt=x := by rw [←sq,Nat.sqrt_eq']
  have np : 0<n := pow_pos (by decide) _
  have hp:=measured_height np places
  rw [xs] at hp
  have T1 : 1≤T := Nat.pow_pos (Nat.succ_pos j)
  have x1 : 0<x := pow_pos (by decide) _
  have extraOne : 1≤x*T := Nat.mul_pos x1 T1
  have widen : W+1≤(B+1)*x*T := by
    change W≤B*x*T at reach
    nlinarith only [reach,extraOne]
  have bound : n^2+2*h*n*(W+1)≤(1+22*(B+1))*n^2*T := by
    have shift : 2*h*n*(W+1)≤2*(11*x)*n*((B+1)*x*T) := by gcongr
    have sim : 2*(11*x)*n*((B+1)*x*T)=22*(B+1)*n^2*T := by
      calc
        _ = 22*(B+1)*x^2*n*T := by ring
        _ = _ := by rw [sq];ring
    rw [sim] at shift
    nlinarith only [shift,Nat.mul_le_mul_left (n^2) T1]
  refine ⟨h,?_⟩
  intro m mh
  have mn : m≤n := by dsimp [n];rw [pow_succ];omega
  obtain ⟨u,v⟩:=crossing_bound places m mn
  exact ⟨u.trans (Nat.add_le_add_left bound _),v.trans (Nat.add_le_add_left bound _)⟩

#print axioms PALRH.LocalDistance.crossing_bound
#print axioms PALRH.LocalDistance.measured_height
#print axioms PALRH.LocalDistance.rh_of_local_moves

end PALRH.LocalDistance
