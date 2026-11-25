import PALRH.CarriedEdge
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset
open scoped BigOperators
noncomputable section
namespace PALRH.RectangleBalance

/-- The sum under a staircase of reciprocal square roots. -/
def harmonics (n : ℕ) : ℝ := ∑ d ∈ Finset.Icc 1 n, 1/Real.sqrt d

private lemma harmonic_step (n : ℕ) :
    harmonics (n+1)=harmonics n+1/Real.sqrt (n+1:ℕ) := by
  unfold harmonics
  rw [Finset.sum_Icc_succ_top (by omega)]

/-- Divide the rectangle difference by the square root of its scale. -/
def gain (v : ℝ) : ℝ := (⌊v⌋₊:ℝ)/Real.sqrt v-harmonics ⌊v⌋₊/2

def lowerEdge (n : ℕ) : ℝ := (n:ℝ)/Real.sqrt ((n:ℝ)+1)-harmonics n/2

private theorem increasing_lower (n : ℕ) : lowerEdge n≤lowerEdge (n+1) := by
  let t : ℝ := n
  have non : 0≤t := by dsimp [t];positivity
  have p : 0<Real.sqrt (t+1) := Real.sqrt_pos.mpr (by linarith)
  have q : 0<Real.sqrt (t+2) := Real.sqrt_pos.mpr (by linarith)
  have s1 := Real.sq_sqrt (show 0≤t+1 by linarith)
  have s2 := Real.sq_sqrt (show 0≤t+2 by linarith)
  have sq : ((t+1/2)*Real.sqrt (t+2))^2≤((t+1)*Real.sqrt (t+1))^2 := by
    rw [mul_pow,mul_pow,s1,s2]
    nlinarith
  have cmp : (t+1/2)*Real.sqrt (t+2)≤(t+1)*Real.sqrt (t+1) :=
    le_of_sq_le_sq sq (by positivity)
  have div := (div_le_div_iff₀ p q).mpr cmp
  unfold lowerEdge
  rw [harmonic_step]
  push_cast
  change t/Real.sqrt (t+1)-harmonics n/2≤(t+1)/Real.sqrt (t+1+1)-
    (harmonics n+1/Real.sqrt (t+1))/2
  rw [show t+1+1=t+2 by ring]
  have split : (t+1/2)/Real.sqrt (t+1)=t/Real.sqrt (t+1)+(1/2)*(1/Real.sqrt (t+1)) := by ring
  rw [split] at div
  linarith

theorem sharp_floor {v : ℝ} (hv : 1≤v) :
    1/Real.sqrt 2-1/2≤gain v := by
  let n:=⌊v⌋₊
  have one : 1≤n := Nat.floor_pos.mpr hv
  have positive : 0<Real.sqrt v := Real.sqrt_pos.mpr (by linarith)
  have cap : Real.sqrt v≤Real.sqrt ((n:ℝ)+1) := Real.sqrt_le_sqrt (Nat.lt_floor_add_one v).le
  have comp := div_le_div_of_nonneg_left (Nat.cast_nonneg (α:=ℝ) n) positive cap
  have b : lowerEdge n≤gain v := by dsimp only [lowerEdge,gain,n] at *; linarith
  have c := (monotone_nat_of_le_succ increasing_lower) one
  exact (show 1/Real.sqrt 2-1/2=lowerEdge 1 by norm_num [lowerEdge,harmonics]).le.trans (c.trans b)

private lemma sum_lower (n : ℕ) : 2*(Real.sqrt ((n:ℝ)+1)-1)≤harmonics n := by
  induction n with
  | zero => norm_num [harmonics]
  | succ n old =>
    rw [harmonic_step]
    push_cast
    let t : ℝ := n
    have non : 0≤t := by dsimp [t];positivity
    have u : 0<Real.sqrt (t+1) := Real.sqrt_pos.mpr (by linarith)
    have s1 := Real.sq_sqrt (show 0≤t+1 by linarith)
    have s2 := Real.sq_sqrt (show 0≤t+1+1 by linarith)
    have diff : (Real.sqrt (t+1+1)-Real.sqrt (t+1))*(Real.sqrt (t+1+1)+Real.sqrt (t+1))=1 := by nlinarith
    have le : Real.sqrt (t+1)≤Real.sqrt (t+1+1) := Real.sqrt_le_sqrt (by linarith)
    have step : 2*(Real.sqrt (t+1+1)-Real.sqrt (t+1))≤1/Real.sqrt (t+1) := by
      apply (le_div_iff₀ u).mpr
      nlinarith [mul_nonneg (sub_nonneg.mpr le) (sub_nonneg.mpr le)]
    change 2*(Real.sqrt (t+1+1)-1)≤harmonics n+1/Real.sqrt (t+1)
    change 2*(Real.sqrt (t+1)-1)≤harmonics n at old
    linarith

theorem ceiling {v : ℝ} (hv : 1≤v) : gain v≤1 := by
  let n:=⌊v⌋₊
  have non : 0≤v := by linarith
  have cap : (n:ℝ)≤v := Nat.floor_le non
  have p : 0<Real.sqrt v := Real.sqrt_pos.mpr (by linarith)
  have a : (n:ℝ)/Real.sqrt v≤Real.sqrt v := (div_le_iff₀ p).mpr (by
    rw [Real.mul_self_sqrt non];exact cap)
  have b := Real.sqrt_le_sqrt (Nat.lt_floor_add_one v).le
  have c := sum_lower n
  change (n:ℝ)/Real.sqrt v-harmonics n/2≤1
  change Real.sqrt v≤Real.sqrt ((n:ℝ)+1) at b
  linarith

theorem uniform_floor {v : ℝ} (hv : 1≤v) : 1/5≤gain v := by
  apply le_trans _ (sharp_floor hv)
  have sq := Real.sq_sqrt (show 0≤(2:ℝ) by norm_num)
  have p : 0<Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have upper : (7/10)*Real.sqrt 2≤1 := by nlinarith [sq_nonneg (10-7*Real.sqrt 2)]
  have t := (le_div_iff₀ p).mpr upper
  linarith

#print axioms PALRH.RectangleBalance.sharp_floor
#print axioms PALRH.RectangleBalance.ceiling
#print axioms PALRH.RectangleBalance.uniform_floor

open TaperedNewton

def divisorMass (n : ℕ) : ℚ := ∑ d ∈ n.divisors, marks d

private lemma supported {d : ℕ} (non : marks d≠0) : d.Coprime 6 := by
  by_contra nope
  apply non
  change (ArithmeticFunction.moebius d:ℚ)*(if d.Coprime 6 then 1 else 0)=0
  simp [nope]

private theorem peel {p : ℕ} (div6 : p∣6) {n : ℕ} (np : 0<n) (pp : 0<p) :
    divisorMass (p*n)=divisorMass n := by
  symm
  apply Finset.sum_subset
  · intro d hd
    exact Nat.mem_divisors.mpr ⟨(Nat.mem_divisors.mp hd).1.trans (dvd_mul_left n p),
      (Nat.mul_pos pp np).ne'⟩
  · intro d hd out
    by_contra nz
    have primefree := (supported nz).of_dvd_right div6
    have hit := primefree.dvd_of_dvd_mul_left (Nat.mem_divisors.mp hd).1
    exact out (Nat.mem_divisors.mpr ⟨hit,np.ne'⟩)

private theorem rough {n : ℕ} (_np : 0<n) (cop : n.Coprime 6) :
    divisorMass n=if n=1 then 1 else 0 := by
  have eq := DFunLike.congr_fun ArithmeticFunction.moebius_mul_coe_zeta n
  rw [ArithmeticFunction.coe_mul_zeta_apply,ArithmeticFunction.one_apply] at eq
  have rat : (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d:ℚ))=if n=1 then 1 else 0 := by
    by_cases yes : n=1 <;> simp only [yes,if_true,if_false] at eq ⊢ <;> exact_mod_cast eq
  rw [←rat,divisorMass]
  apply Finset.sum_congr rfl
  intro d hd
  have keep := cop.of_dvd_left (Nat.mem_divisors.mp hd).1
  change (ArithmeticFunction.moebius d:ℚ)*(if d.Coprime 6 then 1 else 0)=_
  simp [keep]

theorem smooth_source (a b : ℕ) : divisorMass (2^a*3^b)=1 := by
  induction a with
  | zero =>
    rw [pow_zero,one_mul]
    induction b with
    | zero => norm_num [rough]
    | succ b old =>
      rw [pow_succ',peel (by decide : 3∣6) (by positivity) (by decide : 0<3),old]
  | succ a old =>
    rw [pow_succ',Nat.mul_assoc,peel (by decide : 2∣6) (by positivity) (by decide : 0<2),old]

/-- The positive survivors of divisor summation have precisely the indices 2^a 3^b. -/
theorem support_exact {n : ℕ} (np : 0<n) :
    divisorMass n≠0 → ∃ a b : ℕ, n=2^a*3^b := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro nz
    by_cases two : 2∣n
    · obtain ⟨k,rfl⟩ := two
      have pos : 0<k := by omega
      rw [peel (by decide : 2∣6) pos (by decide : 0<2)] at nz
      obtain ⟨a,b,eq⟩ := ih k (by omega) pos nz
      exact ⟨a+1,b,by rw [eq,pow_succ',Nat.mul_assoc]⟩
    by_cases three : 3∣n
    · obtain ⟨k,rfl⟩ := three
      have pos : 0<k := by omega
      rw [peel (by decide : 3∣6) pos (by decide : 0<3)] at nz
      obtain ⟨a,b,eq⟩ := ih k (by omega) pos nz
      exact ⟨a,b+1,by rw [eq,pow_succ'];ring⟩
    have c2 := (Nat.prime_two.coprime_iff_not_dvd.mpr two).symm
    have c3 := (Nat.prime_three.coprime_iff_not_dvd.mpr three).symm
    have cop : n.Coprime 6 := Nat.coprime_mul_iff_right.mpr ⟨c2,c3⟩
    by_cases first : n=1
    · exact ⟨0,0,by simpa using first⟩
    · simp [rough np cop,first] at nz

theorem source_nonnegative (n : ℕ) : 0≤divisorMass n := by
  rcases n.eq_zero_or_pos with z|p
  · simp [z,divisorMass]
  by_cases zero : divisorMass n=0
  · exact zero.ge
  obtain ⟨a,b,rfl⟩ := support_exact p zero
  rw [smooth_source]
  norm_num

#print axioms PALRH.RectangleBalance.support_exact
#print axioms PALRH.RectangleBalance.smooth_source


/-- Grouping the same visits by the product of the two positive row labels. -/
theorem collect_with (N : ℕ) (f w : ℕ → ℝ) :
    (∑ r ∈ Finset.Icc 1 N, (f r/(r:ℝ))*∑ d ∈ Finset.Icc 1 (N/r), (marks d:ℝ)/d*w (r*d))
      = ∑ n ∈ Finset.Icc 1 N, (∑ d ∈ n.divisors, (marks d:ℝ)*f (n/d))/n*w n := by
  let I := Finset.Icc 1 N
  let P := (I ×ˢ I).filter (fun t : ℕ×ℕ => t.1*t.2≤N)
  let val := fun t : ℕ×ℕ => ((marks t.1:ℝ)*f t.2)/((t.1*t.2:ℕ):ℝ)*w (t.1*t.2)
  have join (t : ℕ×ℕ) (ht : t∈P) : t.1*t.2∈I := by
    obtain ⟨both,cap⟩ := Finset.mem_filter.mp ht
    obtain ⟨m,n⟩ := Finset.mem_product.mp both
    exact Finset.mem_Icc.mpr ⟨Nat.mul_pos (Finset.mem_Icc.mp m).1 (Finset.mem_Icc.mp n).1,cap⟩
  have fiber (n : ℕ) (hn : n∈I) :
      P.filter (fun t : ℕ×ℕ => t.1*t.2=n)=n.divisorsAntidiagonal := by
    ext t
    rw [Finset.mem_filter,Nat.mem_divisorsAntidiagonal]
    constructor
    · intro h; exact ⟨h.2,(show 0<n from (Finset.mem_Icc.mp hn).1).ne'⟩
    · rintro ⟨prod,non⟩
      have i : t.1 ∣ n := ⟨t.2,prod.symm⟩
      have j : t.2 ∣ n := ⟨t.1,by simpa [Nat.mul_comm] using prod.symm⟩
      have pos := (Finset.mem_Icc.mp hn).1
      have lim := (Finset.mem_Icc.mp hn).2
      exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨Finset.mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos i pos,(Nat.le_of_dvd pos i).trans lim⟩,
         Finset.mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos j pos,(Nat.le_of_dvd pos j).trans lim⟩⟩,prod ▸ lim⟩,prod⟩
  have grouped : (∑ t ∈ P, val t)=∑ n ∈ I, (∑ d ∈ n.divisors, (marks d:ℝ)*f (n/d))/n*w n := by
    rw [←Finset.sum_fiberwise_of_maps_to join val]
    apply Finset.sum_congr rfl
    intro n hn
    rw [fiber n hn]
    have point (t : ℕ×ℕ) (ht : t∈n.divisorsAntidiagonal) :
        val t=((marks t.1:ℝ)*f t.2)/n*w n := by simp only [val,(Nat.mem_divisorsAntidiagonal.mp ht).1]
    rw [Finset.sum_congr rfl point,Nat.sum_divisorsAntidiagonal (fun i j => ((marks i:ℝ)*f j)/n*w n),
      ←Finset.sum_mul,←Finset.sum_div]
  rw [←grouped]
  dsimp only [P]
  rw [Finset.sum_filter,Finset.sum_product,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  have pos := (Finset.mem_Icc.mp hr).1
  have eq : I.filter (fun d => d*r≤N)=Finset.Icc 1 (N/r) := by
    ext d
    simp only [I,Finset.mem_filter,Finset.mem_Icc,←Nat.le_div_iff_mul_le pos]
    have := Nat.div_le_self N r
    omega
  rw [Finset.mul_sum,←eq,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d _
  split
  · dsimp only [val]
    rw [Nat.mul_comm d r,Nat.cast_mul]
    ring
  · rfl

theorem collect (N : ℕ) (w : ℕ → ℝ) :
    (∑ r ∈ Finset.Icc 1 N, (1/(r:ℝ))*∑ d ∈ Finset.Icc 1 (N/r), (marks d:ℝ)/d*w (r*d))
      = ∑ n ∈ Finset.Icc 1 N, (divisorMass n:ℝ)/n*w n := by
  simpa only [divisorMass,Rat.cast_sum,mul_one] using collect_with N (fun _ => 1) w

/-- A finite weighted measurement can carry both signs while its signed balance stays bounded. -/
theorem compare_signs {ι : Type*} (I : Finset ι) (f a : ι → ℝ) {C : ℝ}
    (weights : ∀ i∈I, 1/5≤a i ∧ a i≤1)
    (balance : 0≤∑ i ∈ I, a i*f i)
    (cap : (∑ i ∈ I, a i*f i)≤C) :
    (∑ i ∈ I, max (-f i) 0)≤5*∑ i ∈ I, max (f i) 0 ∧
    (∑ i ∈ I, max (f i) 0)≤5*((∑ i ∈ I, max (-f i) 0)+C) := by
  let p := fun i => max (f i) 0
  let n := fun i => max (-f i) 0
  have split (i : ι) : a i*f i=a i*p i-a i*n i := by
    dsimp only [p,n]
    rw [←mul_sub]
    congr 1
    rcases le_total 0 (f i) with h|h
    · rw [max_eq_left h,max_eq_right (neg_nonpos.mpr h),sub_zero]
    · rw [max_eq_right h,max_eq_left (neg_nonneg.mpr h)];ring
  have cost := Finset.sum_congr (s₁:=I) rfl (fun i _ => split i)
  rw [Finset.sum_sub_distrib] at cost
  have bounds (g : ι → ℝ) (pos : ∀ i, 0≤g i) :
      (1/5)*(∑ i ∈ I, g i)≤∑ i ∈ I, a i*g i ∧
      (∑ i ∈ I, a i*g i)≤∑ i ∈ I, g i := by
    rw [Finset.mul_sum]
    constructor
    · exact Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_right (weights i hi).1 (pos i))
    · exact Finset.sum_le_sum (fun i hi => (mul_le_mul_of_nonneg_right (weights i hi).2 (pos i)).trans_eq (one_mul _))
  have hp := bounds p (fun i => le_max_right _ _)
  have hn := bounds n (fun i => le_max_right _ _)
  change _≤5*(∑ i ∈ I, p i) ∧ _≤5*((∑ i ∈ I, n i)+C)
  dsimp only [p,n] at *
  constructor <;> linarith [hp.1,hp.2,hn.1,hn.2]

#print axioms PALRH.RectangleBalance.collect
#print axioms PALRH.RectangleBalance.compare_signs


/-- A unit plateau, a linear fall from one to zero, then an exact cutoff. -/
def taper (t : ℝ) : ℝ := max 0 (min 1 (2-t))

private lemma weight_at {H : ℕ} (hp : 0<H) (d : ℕ) :
    taper ((d:ℝ)/H)=(weight H d:ℝ) := by
  have pos : 0<(H:ℝ) := by positivity
  by_cases before : d≤H
  · have one : (d:ℝ)/H≤1 := (div_le_one pos).mpr (by exact_mod_cast before)
    rw [taper,min_eq_left (by linarith),max_eq_right (by norm_num),weight,if_pos before];norm_num
  by_cases inside : d≤2*H
  · have left : 1≤(d:ℝ)/H := (one_le_div pos).mpr (by exact_mod_cast (le_of_not_ge before))
    have right : (d:ℝ)/H≤2 := (div_le_iff₀ pos).mpr (by exact_mod_cast inside)
    rw [taper,min_eq_right (by linarith),max_eq_right (by linarith),weight,if_neg before,if_pos inside]
    push_cast [Nat.cast_sub inside]
    field_simp
  · have right : 2≤(d:ℝ)/H := (le_div_iff₀ pos).mpr (by exact_mod_cast (le_of_not_ge inside))
    rw [taper,min_eq_right (by linarith),max_eq_left (by linarith),weight,if_neg before,if_neg inside]
    norm_num

def edge (x : ℝ) : ℝ := ∑ d ∈ Finset.Icc 1 ⌊2*x⌋₊, (marks d:ℝ)/d*taper (d/x)
def source (x : ℝ) : ℝ := ∑ d ∈ Finset.Icc 1 ⌊2*x⌋₊, (divisorMass d:ℝ)/d*taper (d/x)

theorem same_edge {H : ℕ} (hp : 0<H) : edge H=(slope H marks:ℝ) := by
  have cast : 2*(H:ℝ)=((2*H:ℕ):ℝ) := by push_cast;rfl
  unfold edge TaperedNewton.slope
  rw [cast,Nat.floor_natCast,Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro d _
  rw [weight_at hp,Rat.cast_div,Rat.cast_mul,Rat.cast_natCast]
  ring

/-- At a real scale every dilation of the actual edge is accounted for by a positive source. -/
theorem dilation {x : ℝ} (pos : 0<x) :
    (∑ r ∈ Finset.Icc 1 ⌊2*x⌋₊, edge (x/r)/r)=source x := by
  rw [source,←collect]
  apply Finset.sum_congr rfl
  intro r hr
  have rp : 0<r := (Finset.mem_Icc.mp hr).1
  have rp' : 0<(r:ℝ) := by exact_mod_cast rp
  rw [edge,show 2*(x/r)=(2*x)/r by ring,Nat.floor_div_natCast]
  rw [one_div,inv_mul_eq_div]
  apply congrArg (fun t : ℝ => t/r)
  apply Finset.sum_congr rfl
  intro d _
  rw [Nat.cast_mul]
  have eq : (d:ℝ)/(x/r)=((r:ℝ)*d)/x := by field_simp
  rw [eq]

theorem positive_source (x : ℝ) : 0≤source x := by
  apply Finset.sum_nonneg
  intro d _
  exact mul_nonneg (div_nonneg (by exact_mod_cast source_nonnegative d) (by positivity)) (le_max_left _ _)

#print axioms PALRH.RectangleBalance.same_edge
#print axioms PALRH.RectangleBalance.dilation


def observe (f : ℕ → ℝ) (x : ℝ) :=
   ∑ r ∈ Finset.Icc 1 ⌊2*x⌋₊, (f r/r)*edge (x/r)

theorem observe_eq (f : ℕ → ℝ) {x : ℝ} (pos : 0<x) : observe f x=
    ∑ n ∈ Finset.Icc 1 ⌊2*x⌋₊, (∑ d ∈ n.divisors, (marks d:ℝ)*f (n/d))/n*taper (n/x) := by
  rw [observe,←collect_with]
  apply Finset.sum_congr rfl
  intro r hr
  have rp : 0<r := (Finset.mem_Icc.mp hr).1
  have rp' : 0<(r:ℝ) := by exact_mod_cast rp
  rw [edge,show 2*(x/r)=(2*x)/r by ring,Nat.floor_div_natCast]
  congr 1
  apply Finset.sum_congr rfl
  intro d _
  rw [Nat.cast_mul,show (d:ℝ)/(x/r)=((r:ℝ)*d)/x by field_simp]

theorem rough_dilation {x : ℝ} (xp : 0<x) :
    observe (fun r => (allowed r:ℝ)) x=taper (1/x) := by
  rw [observe_eq _ xp]
  have inv (n : ℕ) : (∑ d ∈ n.divisors, (marks d:ℝ)*(allowed (n/d):ℝ)) =
      if n=1 then 1 else 0 := by
    have h := DFunLike.congr_fun marks_inverse n
    rw [ArithmeticFunction.mul_apply,Nat.sum_divisorsAntidiagonal (fun i j => marks i*allowed j),ArithmeticFunction.one_apply] at h
    by_cases one : n=1 <;> simp only [one,if_true,if_false] at h ⊢ <;> exact_mod_cast h
  simp_rw [inv]
  by_cases includeOne : 1≤⌊2*x⌋₊
  · rw [Finset.sum_eq_single 1]
    · norm_num
    · intro n _ hn;simp [hn]
    · simp [includeOne]
  have small : 2*x<1 := lt_of_not_ge (fun h => includeOne (Nat.floor_pos.mpr h))
  have flat : 2≤1/x := (le_div_iff₀ xp).mpr (by linarith)
  rw [show ⌊2*x⌋₊=0 by omega]
  simp only [Finset.Icc_eq_empty_of_lt (by decide : 0<1),Finset.sum_empty,taper,min_eq_right (by linarith : 2-1/x≤1),max_eq_left (by linarith : 2-1/x≤0)]

#print axioms PALRH.RectangleBalance.rough_dilation


private lemma taper_vanish {t : ℝ} (late : 2≤t) : taper t=0 := by
  unfold taper
  rw [min_eq_right (by linarith),max_eq_left (by linarith)]

lemma taper_continuous : Continuous taper := by unfold taper; fun_prop

/-- Finite representation valid on a whole interval, including its zero endpoint. -/
def atom (d : ℕ) (x : ℝ) := taper ((d:ℝ)/max x (1/4))

theorem atom_continuous (d : ℕ) : Continuous (atom d) := by
  unfold atom
  apply taper_continuous.comp
  exact continuous_const.div (continuous_id.max continuous_const) (fun x =>
    (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/4) (le_max_right x _)).ne')

private lemma atom_early {d : ℕ} (dp : 0<d) {x : ℝ} (early : 2*x≤d) : atom d x=0 := by
  have one : (1:ℝ)≤d := by exact_mod_cast dp
  apply taper_vanish
  apply (le_div_iff₀ (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/4) (le_max_right x _))).mpr
  rcases le_total x (1/4) with below|above
  · rw [max_eq_right below];linarith
  · rw [max_eq_left above];exact early

private lemma atom_agrees {d : ℕ} (dp : 0<d) {x : ℝ} (xp : 0<x) :
    atom d x=taper (d/x) := by
  by_cases large : 1/4≤x
  · rw [atom,max_eq_left large]
  have one : (1:ℝ)≤d := by exact_mod_cast dp
  have early : 2*x≤d := by linarith
  rw [atom_early dp early,taper_vanish ((le_div_iff₀ xp).mpr early)]

theorem edge_pad {X x : ℝ} (before : x≤X) :
    edge x=∑ d ∈ Finset.Icc 1 ⌊2*X⌋₊, (marks d:ℝ)/d*atom d x := by
  let inner := Finset.Icc 1 ⌊2*x⌋₊
  have seq : edge x=∑ d ∈ inner, (marks d:ℝ)/d*atom d x := by
    apply Finset.sum_congr rfl
    intro d hd
    have lo := (Finset.mem_Icc.mp hd).1
    have hi := (Finset.mem_Icc.mp hd).2
    have pos : 0<x := by
      have e : 1≤2*x := Nat.floor_pos.mp (lo.trans hi)
      linarith
    rw [atom_agrees lo pos]
  rw [seq]
  apply Finset.sum_subset
  · intro d hd
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1,(Finset.mem_Icc.mp hd).2.trans
      (Nat.floor_le_floor (by linarith))⟩
  · intro d hd miss
    have lo := (Finset.mem_Icc.mp hd).1
    have far : ⌊2*x⌋₊<d := by by_contra! h;exact miss (Finset.mem_Icc.mpr ⟨lo,h⟩)
    have early : 2*x≤d := (Nat.lt_of_floor_lt far).le
    rw [atom_early lo early,mul_zero]

theorem edge_continuousOn (X : ℝ) : ContinuousOn edge (Set.Iic X) := by
  exact (continuous_finsetSum _ (fun d _ => continuous_const.mul (atom_continuous d))).continuousOn.congr
    (fun _ hx => edge_pad hx)

theorem edge_before {x : ℝ} (early : x≤1/2) : edge x=0 := by
  rw [edge_pad (le_refl x)]
  apply Finset.sum_eq_zero
  intro d hd
  have dp := (Finset.mem_Icc.mp hd).1
  have one : (1:ℝ)≤d := by exact_mod_cast dp
  rw [atom_early dp (by linarith),mul_zero]

#print axioms PALRH.RectangleBalance.edge_before


theorem edge_pad_positive {X x : ℝ} (xp : 0<x) (before : x≤X) :
    edge x=∑ d ∈ Finset.Icc 1 ⌊2*X⌋₊, (marks d:ℝ)/d*taper (d/x) := by
  rw [edge_pad before]
  apply Finset.sum_congr rfl
  intro d hd
  rw [atom_agrees (Finset.mem_Icc.mp hd).1 xp]


theorem atom_unit (d : ℕ) (x : ℝ) : 0≤atom d x ∧ atom d x≤1 :=
  ⟨le_max_left _ _,max_le zero_le_one (min_le_left _ _)⟩

theorem atom_one {d : ℕ} (dp : 0<d) {x : ℝ} (beyond : (d:ℝ)≤x) : atom d x=1 := by
  have xp := (by exact_mod_cast dp : 0<(d:ℝ)).trans_le beyond
  rw [atom_agrees dp xp,taper,min_eq_left (by linarith [(div_le_one xp).mpr beyond]),max_eq_right zero_le_one]

theorem source_pad_positive {X x : ℝ} (xp : 0<x) (before : x≤X) :
    source x=∑ d ∈ Finset.Icc 1 ⌊2*X⌋₊, (divisorMass d:ℝ)/d*atom d x := by
  let I := Finset.Icc 1 ⌊2*x⌋₊
  have eq : source x=∑ d ∈ I, (divisorMass d:ℝ)/d*atom d x := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [atom_agrees (Finset.mem_Icc.mp hd).1 xp]
  rw [eq]
  apply Finset.sum_subset
  · intro d hd
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1,(Finset.mem_Icc.mp hd).2.trans
      (Nat.floor_le_floor (by linarith))⟩
  · intro d hd miss
    have lo := (Finset.mem_Icc.mp hd).1
    have out : ⌊2*x⌋₊<d := by by_contra! le; exact miss (Finset.mem_Icc.mpr ⟨lo,le⟩)
    simp [atom_early lo (Nat.lt_of_floor_lt out).le]

end PALRH.RectangleBalance
