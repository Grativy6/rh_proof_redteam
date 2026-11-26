import PALRH.ShapeStrip

open Finset
open scoped BigOperators

noncomputable section
namespace PALRH.ShapeObservation
open ShapeStrip

/-- An integer tick is recorded exactly when its distance passes the board's factorial sieve. -/
def tickAt (n d : ℕ) : ℕ :=
  if 2≤d ∧ d.gcd n.sqrt.factorial=1 then TickBoard.ticks n n.sqrt d else 0

def prefixJobs (n m : ℕ) := ∑ d ∈ Icc 1 m, (n-d)*tickAt n d

def plainArea (n m : ℕ) := ∑ d ∈ Icc 1 m, (n-d)

private def primeLog (d : ℕ) : ℝ := if d.Prime then Real.log d else 0

private theorem theta_sum (m : ℕ) : (∑ d ∈ Icc 1 m,primeLog d)=Chebyshev.theta m := by
  simp only [Chebyshev.theta,Nat.floor_natCast,←Finset.Icc_add_one_left_eq_Ioc,
    Nat.zero_add,Finset.sum_filter,primeLog]

theorem theta_price (m : ℕ) : Chebyshev.theta m≤2*m := by
  have two:=Real.log_le_sub_one_of_pos (by norm_num : 0<(2:ℝ))
  have four : Real.log 4≤2 := by
    rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]
    norm_num at *
    linarith
  exact (Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg m)).trans
    (mul_le_mul_of_nonneg_right four (Nat.cast_nonneg _))

private theorem tick_test {n d : ℕ} (dn : d≤n) :
    (2≤d ∧ d.gcd n.sqrt.factorial=1) ↔ d.Prime ∧ n.sqrt<d := by
  constructor
  · rintro ⟨lo,h⟩
    exact (SieveFrame.factorial_test lo dn).mp h
  · intro h
    exact ⟨h.1.two_le,(SieveFrame.factorial_test h.1.two_le dn).mpr h⟩

/-- All rounding and the entire omitted small-prime prefix cost at most three board lengths. -/
theorem prefix_calibration (n m : ℕ) (np : 0<n) (mn : m≤n) :
    |(∑ d ∈ Icc 1 m,(tickAt n d:ℝ))-(n.sqrt:ℝ)*Chebyshev.theta m|≤3*n := by
  let x:=n.sqrt
  have xp : 0<x := Nat.sqrt_pos.mpr np
  have xr : 0≤(x:ℝ) := Nat.cast_nonneg _
  have mnr : (m:ℝ)≤n := by exact_mod_cast mn
  have xsq : (x:ℝ)^2≤n := by exact_mod_cast (by simpa [pow_two,x] using Nat.sqrt_le n : x^2≤n)
  have lpos (d : ℕ) : 0≤primeLog d := by
    unfold primeLog
    split_ifs with p
    · exact Real.log_nonneg (by exact_mod_cast p.one_le)
    · rfl
  have small : (∑ d ∈ Icc 1 m, if d≤x then primeLog d else 0)=Chebyshev.theta (min m x:ℕ) := by
    rw [←Finset.sum_filter,←theta_sum]
    congr 1
    ext d
    simp only [Finset.mem_filter,Finset.mem_Icc,le_min_iff]
    tauto
  have top : (∑ d ∈ Icc 1 m,(tickAt n d:ℝ))≤(m:ℝ)+((x:ℝ)+1)*Chebyshev.theta m := by
    calc
      _ ≤ ∑ d ∈ Icc 1 m,(1+((x:ℝ)+1)*primeLog d) := by
        apply Finset.sum_le_sum
        intro d hd
        have dh: d≤n := (mem_Icc.mp hd).2.trans mn
        by_cases ok : 2≤d ∧ d.gcd n.sqrt.factorial=1
        · have p:=((tick_test dh).mp ok).1
          simpa [tickAt,ok,primeLog,p,x] using TickBoard.single_upper (n:=n) xp p.pos
        · rw [tickAt,if_neg ok,Nat.cast_zero]
          positivity [lpos d]
      _ = _ := by rw [Finset.sum_add_distrib,←Finset.mul_sum,theta_sum];simp
  have lower : (x:ℝ)*Chebyshev.theta m≤
      (∑ d ∈ Icc 1 m,(tickAt n d:ℝ))+(x:ℝ)*Chebyshev.theta (min m x:ℕ) := by
    rw [←small,←theta_sum,Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro d hd
    have dh: d≤n := (mem_Icc.mp hd).2.trans mn
    by_cases ds : d≤x
    · simp [ds]
    · by_cases pr : d.Prime
      · have ok:=(tick_test dh).mpr ⟨pr,lt_of_not_ge ds⟩
        simpa [ds,primeLog,pr,tickAt,ok,x] using TickBoard.single_price xp pr.pos dh
      · simp [ds,primeLog,pr]
  have smallSlope : Chebyshev.theta (min m x:ℕ)≤2*x :=
    (theta_price _).trans (mul_le_mul_of_nonneg_left (by exact_mod_cast (min_le_right m x)) (by norm_num))
  have paid:=mul_le_mul_of_nonneg_left smallSlope xr
  change |_-(x:ℝ)*_|≤_
  exact abs_sub_le_iff.mpr ⟨by nlinarith only [top,theta_price m,mnr],
    by nlinarith only [lower,paid,xsq,show 0≤(n:ℝ) from Nat.cast_nonneg _]⟩


theorem reading (n m h : ℕ) (mn : m≤n) :
    weighted n (fun d => (tickAt n d:ℝ)-h) m=(prefixJobs n m:ℝ)-(h:ℝ)*plainArea n m := by
  unfold weighted prefixJobs plainArea
  push_cast
  rw [Finset.mul_sum,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Nat.cast_sub ((mem_Icc.mp hd).2.trans mn)]
  ring

private theorem headSquare (j : ℕ) : (4^(j+1))^2=(16:ℕ)^(j+1) := by
  rw [←pow_mul,mul_comm (j+1) 2,pow_mul];rfl

/-- On this board both the prices and the allowed error are whole numbers. -/
def stripFits (A j h : ℕ) : Prop :=
  ∀ m≤16^j, let n:=16^(j+1)
    prefixJobs n m≤h*plainArea n m+A*n^2*(j+1)^2 ∧
    h*plainArea n m≤prefixJobs n m+A*n^2*(j+1)^2

private theorem observed_slope {A j h : ℕ} (fits : stripFits A j h) {m : ℕ} (mh : m≤16^j) :
    |Chebyshev.theta m-((h:ℝ)/(4:ℝ)^(j+1))*m|≤
      4*(2*(A:ℝ)+3)*((4:ℝ)^j*((j:ℝ)+1)^2) := by
  let n:ℕ:=16^(j+1)
  let x:ℕ:=4^(j+1)
  let M:ℕ:=16^j
  let T:ℝ:=((j:ℝ)+1)^2
  have np : 0<n := pow_pos (by decide) _
  have xp : 0<(x:ℝ) := by dsimp [x];positivity
  have nx : n.sqrt=x := by change Nat.sqrt (16^(j+1))=4^(j+1);rw [←headSquare,Nat.sqrt_eq']
  have sq : (x:ℝ)^2=n := by exact_mod_cast headSquare j
  have short : 4*M≤n := by dsimp [M,n];rw [pow_succ];omega
  have Mn : M≤n := by omega
  have mn : m≤n := mh.trans Mn
  have T1 : 1≤T := by dsimp [T];nlinarith [Nat.cast_nonneg (α:=ℝ) j,sq_nonneg (j:ℝ)]
  let E:ℝ:=(A:ℝ)*n^2*T
  have E0 : 0≤E := by dsimp [E,T];positivity
  have obs (i : ℕ) (hi : i≤M) : |weighted n (fun d => (tickAt n d:ℝ)-h) i|≤E := by
    rw [reading n i h (hi.trans Mn)]
    obtain ⟨l,r⟩:=fits i hi
    have l' : (prefixJobs n i:ℝ)≤(h:ℝ)*plainArea n i+E := by dsimp [E,T];exact_mod_cast l
    have r' : (h:ℝ)*plainArea n i≤(prefixJobs n i:ℝ)+E := by dsimp [E,T];exact_mod_cast r
    exact abs_sub_le_iff.mpr ⟨by linarith only [l'],by linarith only [r']⟩
  have straight:=untilted n M np short _ E0 obs m mh
  have price : 2*E/(n:ℝ)=2*(A:ℝ)*n*T := by
    have nr : (n:ℝ)≠0 := by exact_mod_cast np.ne'
    dsimp [E];field_simp
  have flat : |(∑ d ∈ Icc 1 m,(tickAt n d:ℝ))-(h:ℝ)*m|≤2*(A:ℝ)*n*T := by
    rw [price] at straight
    simpa [plainPrefix,Finset.sum_sub_distrib,mul_comm] using straight
  have logCost:=prefix_calibration n m np mn
  rw [nx,abs_sub_comm] at logCost
  have close : |(x:ℝ)*Chebyshev.theta m-(h:ℝ)*m|≤3*n+2*(A:ℝ)*n*T := by
    calc
      _ = |((x:ℝ)*Chebyshev.theta m-(∑ d ∈ Icc 1 m,(tickAt n d:ℝ)))+
          ((∑ d ∈ Icc 1 m,(tickAt n d:ℝ))-(h:ℝ)*m)| := by ring_nf
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add logCost flat)
  have base : |Chebyshev.theta m-(h:ℝ)/x*m|≤(2*(A:ℝ)+3)*x*T := by
    apply le_of_mul_le_mul_left (a:=(x:ℝ)) _ xp
    rw [←abs_of_pos xp,←abs_mul]
    rw [abs_of_pos xp]
    have clean : (x:ℝ)*(Chebyshev.theta m-(h:ℝ)/x*m)=x*Chebyshev.theta m-(h:ℝ)*m := by
      field_simp
    rw [clean]
    apply close.trans
    rw [←sq]
    nlinarith only [mul_le_mul_of_nonneg_left T1 (show 0≤3*(x:ℝ)^2 by positivity)]
  convert base using 1 <;> dsimp [x,T] <;> push_cast
  rw [pow_succ (4:ℝ) j]
  ring

/-- Local observers may set their own integer height. Overlap on the same prime distances
forces a unique density and the zeta zero conclusion. -/
theorem from_chosen_heights (A : ℕ) (h : ℕ → ℕ) (fits : ∀ j, stripFits A j (h j)) :
    DyadicShape.limitingSlope (fun j => (h j:ℝ)/(4:ℝ)^(j+1))=1 ∧ RiemannHypothesis := by
  apply DyadicShape.infer_density_and_rh
  intro b bh _
  obtain ⟨D,dn,price⟩:=root_price b bh
  refine ⟨(4*(2*(A:ℝ)+3))*D,by positivity,?_⟩
  intro j m _ mh
  apply (observed_slope (fits j) mh).trans
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (price j) (show 0≤4*(2*(A:ℝ)+3) by positivity)

/-- A common amount of allowed bending, with no prescribed height on any board. -/
theorem rh_of_strip_readings (fit : ∃ A : ℕ, ∀ j : ℕ, ∃ h : ℕ, stripFits A j h) :
    RiemannHypothesis := by
  obtain ⟨A,all⟩:=fit
  choose h hh using all
  exact (from_chosen_heights A h hh).2

#print axioms PALRH.ShapeObservation.prefix_calibration
#print axioms PALRH.ShapeObservation.rh_of_strip_readings

end PALRH.ShapeObservation
