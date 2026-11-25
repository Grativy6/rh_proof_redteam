import PALRH.Balanced
import Mathlib.NumberTheory.LSeries.Dirichlet

open Filter Set MeasureTheory Complex Asymptotics Finset
open scoped Topology BigOperators
noncomputable section
namespace PALRH.Octaves

def walk (n : ℕ) : ℝ := ∑ k ∈ Finset.Icc 1 n, (ArithmeticFunction.moebius k:ℝ)

private lemma walk_cap (n : ℕ) : |walk n|≤(n:ℝ) := by
  calc
    _ ≤ ∑ k ∈ Finset.Icc 1 n, |(ArithmeticFunction.moebius k:ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ ∈ Finset.Icc 1 n, (1:ℝ) := by
      apply Finset.sum_le_sum
      intro k _
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n:=k))
    _ = _ := by simp [Nat.card_Icc]

def WalkGrowth : Prop := ∀ a : ℝ, 1/2<a → ∃ C : ℝ, 0≤C ∧
  ∀ n : ℕ, |walk n| ≤ C*(n:ℝ)^a

private def trace (x : ℝ) : ℂ := walk ⌊x⁻¹⌋₊

private theorem trace_regular (budget : WalkGrowth) {s : ℂ} (hs : 1/2<s.re) :
    DifferentiableAt ℂ (mellin trace) s := by
  let b := (1/2+s.re)/2
  have high : 1/2<b := by dsimp [b]; linarith
  obtain ⟨C,hC,bound⟩ := budget b high
  apply mellin_differentiableAt_of_isBigO_rpow (a:=s.re+1) (b:=b)
  · have hi : ContinuousOn (fun x : ℝ => x⁻¹) (Ioi 0) :=
      continuousOn_id.inv₀ fun x hx => ne_of_gt hx
    apply (hi.locallyIntegrableOn measurableSet_Ioi).mono
    · exact ((measurable_of_countable (fun k : ℕ => (walk k:ℂ))).comp
        (by fun_prop : Measurable (fun x : ℝ => ⌊x⁻¹⌋₊))).aestronglyMeasurable
    · apply Filter.Eventually.of_forall
      intro x
      change ‖(walk ⌊x⁻¹⌋₊:ℂ)‖≤‖x⁻¹‖
      rw [Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs]
      by_cases hx : 0≤x⁻¹
      · exact (walk_cap _).trans ((Nat.floor_le hx).trans (le_abs_self _))
      · simp [Nat.floor_eq_zero.mpr (by linarith : x⁻¹<1),walk]
  · apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [eventually_gt_atTop (1:ℝ)] with x hx
    simp [trace,Nat.floor_eq_zero.mpr (inv_lt_one_of_one_lt₀ hx),walk]
  · linarith
  · apply Asymptotics.IsBigO.of_bound C
    filter_upwards [self_mem_nhdsWithin] with x (hx : 0<x)
    rw [Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos hx _)]
    change ‖(walk ⌊x⁻¹⌋₊:ℂ)‖ ≤ _
    rw [Complex.norm_real,Real.norm_eq_abs,Real.rpow_neg hx.le,←Real.inv_rpow hx.le]
    apply (bound _).trans
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) (Nat.floor_le (inv_nonneg.mpr hx.le))
      (by linarith)) hC
  · dsimp [b]; linarith

private def coeff (n : ℕ) : ℂ := ArithmeticFunction.moebius n

private theorem on_right {s : ℂ} (hs : 1<s.re) : riemannZeta s*(s*mellin trace s)=1 := by
  have hsum (n : ℕ) : (∑ k ∈ Finset.Icc 1 n, coeff k)=(walk n:ℂ) := by
    simp [coeff,walk]
  have hb : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, coeff k) =O[atTop] fun n => (n:ℝ)^(1:ℝ) := by
    apply isBigO_of_le _
    intro n
    simp only [hsum,Complex.norm_real,Real.norm_eq_abs,Real.rpow_one,abs_of_nonneg (show 0≤(n:ℝ) by positivity)]
    exact walk_cap n
  have hL : LSeries coeff s=s*mellin trace s := by
    have summ : LSeriesSummable coeff s := ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs
    rw [LSeries_eq_mul_integral coeff zero_le_one hs summ hb]
    congr 1
    simp only [hsum]
    let f := fun x : ℝ => (walk ⌊x⌋₊:ℂ)
    change _ = mellin (fun x => f x⁻¹) s
    rw [mellin_comp_inv,mellin]
    let g := fun x : ℝ => (x:ℂ)^(-s-1) • f x
    change _ = ∫ x in Ioi 0, g x
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (Ici_subset_Ioi.mpr (zero_lt_one : (0:ℝ)<1)) (f:=g) (by
        intro x hx
        have small : x<1 := lt_of_not_ge hx.2
        simp [g,f,Nat.floor_eq_zero.mpr small,walk]),integral_Ici_eq_integral_Ioi]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    simp only [g,f,smul_eq_mul,neg_add_rev,sub_eq_add_neg]
    ring_nf
  rw [←hL,←LSeries_one_eq_riemannZeta hs]
  exact LSeries_one_mul_Lseries_moebius hs

/-- Use the ordinary absolutely convergent Möbius series only to the right of one.
The primitive, with its actual signed growth bound, supplies analytic continuation. -/
theorem rh_of_walk_growth (budget : WalkGrowth) : RiemannHypothesis := by
  let U : Set ℂ := {z | 1/2<z.re}
  have hU : IsOpen U := isOpen_lt continuous_const continuous_re
  let F := fun z : ℂ => riemannZeta₁ z*(z*mellin trace z)
  let G := fun z : ℂ => z-1
  have hF : AnalyticOnNhd ℂ F U := by
    apply DifferentiableOn.analyticOnNhd _ hU
    intro z hz
    exact ((differentiable_riemannZeta₁ z).mul (differentiableAt_id.mul (trace_regular budget hz))).differentiableWithinAt
  have hG : AnalyticOnNhd ℂ G U := by
    apply DifferentiableOn.analyticOnNhd _ hU
    fun_prop
  have factor (z : ℂ) (h1 : z≠1) : (z-1)*riemannZeta z=riemannZeta₁ z := by
    rw [riemannZeta_eq_inv_sub_mul h1]; field_simp [sub_ne_zero.mpr h1]
  have eq : EqOn F G U :=
    hF.eqOn_of_preconnected_of_eventuallyEq hG (convex_halfSpace_re_gt _).isPreconnected
      (by norm_num [U] : (2:ℂ) ∈ U)
      (eventuallyEq_of_mem ((isOpen_lt continuous_const continuous_re).mem_nhds
        (by norm_num : (1:ℝ)<(2:ℂ).re)) (by
        intro z (hz : 1<z.re)
        have h1 : z≠1 := by rintro rfl; norm_num at hz
        dsimp [F,G]
        rw [←factor z h1,mul_assoc,on_right hz,mul_one]))
  apply rh_of_right
  intro s hs h1 zero
  have he := eq (show s ∈ U from hs)
  dsimp only [F,G] at he
  rw [←factor s h1,zero,mul_zero,zero_mul] at he
  exact h1 (sub_eq_zero.mp he.symm)

#print axioms PALRH.Octaves.rh_of_walk_growth

/-- The cost of the consecutive signed increments on one doubling window. -/
def price (A : ℕ → ℝ) (h : ℕ) : ℝ :=
  ∑ k ∈ Finset.Ioc h (2*h), (A k-A h)^2/((k:ℝ)*(k+1))

private lemma pos_price (A : ℕ → ℝ) (h : ℕ) : 0≤price A h := by
  unfold price
  exact Finset.sum_nonneg (fun k _ => by positivity)

private lemma charge (x D C : ℝ) (hD : 0<D) (comp : D≤C) : x^2≤C*(x^2/D) := by
  calc
    _ = D*(x^2/D) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right comp (by positivity)

/-- A common interval measures the difference of two saved starting values exactly.
Its length is the denominator in this transport estimate. -/
theorem overlap_price (A : ℕ → ℝ) {m n : ℕ} (mn : m≤n) :
    ((2*m-n:ℕ):ℝ)*(A n-A m)^2 ≤
      2*((2*m:ℕ):ℝ)*(((2*m:ℕ):ℝ)+1)*(price A n+price A m) := by
  let I := Finset.Ioc n (2*m)
  let C : ℝ := ((2*m:ℕ):ℝ)*(((2*m:ℕ):ℝ)+1)
  let cell := fun h k : ℕ => (A k-A h)^2/((k:ℝ)*(k+1))
  have sub (h : ℕ) (incl : I⊆Finset.Ioc h (2*h)) :
      (∑ k ∈ I, cell h k) ≤ price A h :=
    Finset.sum_le_sum_of_subset_of_nonneg incl (fun k _ _ => by dsimp [cell]; positivity)
  have ninc : I⊆Finset.Ioc n (2*n) := fun k hk =>
    Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hk).1,(Finset.mem_Ioc.mp hk).2.trans (by omega)⟩
  have minc : I⊆Finset.Ioc m (2*m) := fun k hk =>
    Finset.mem_Ioc.mpr ⟨lt_of_le_of_lt mn (Finset.mem_Ioc.mp hk).1,(Finset.mem_Ioc.mp hk).2⟩
  have term (k : ℕ) (hk : k∈I) : (A n-A m)^2≤(2*C)*(cell n k+cell m k) := by
    obtain ⟨kn,km⟩ := Finset.mem_Ioc.mp hk
    have kr : (k:ℝ)≤((2*m:ℕ):ℝ) := by exact_mod_cast km
    have cp : (k:ℝ)*(k+1) ≤ C := by dsimp [C]; gcongr
    have kp : 0<(k:ℝ) := by exact_mod_cast (by omega : 0<k)
    have pos : 0<(k:ℝ)*(k+1) := mul_pos kp (by linarith)
    have a := charge (A k-A n) _ _ pos cp
    have b := charge (A k-A m) _ _ pos cp
    dsimp only [cell]
    nlinarith [sq_nonneg (2*A k-A n-A m)]
  have sum := Finset.sum_le_sum term
  rw [Finset.sum_const,show I.card=2*m-n by simp [I,Nat.card_Ioc], nsmul_eq_mul,←Finset.mul_sum,Finset.sum_add_distrib] at sum
  have h := sum.trans (mul_le_mul_of_nonneg_left (add_le_add (sub n ninc) (sub m minc))
    (show 0≤2*C by dsimp [C]; positivity))
  simpa only [C,mul_assoc] using h

/-- Quantitative one-octave budget, with a constant depending on the chosen exponent. -/
def AllOctaves (A : ℕ → ℝ) : Prop :=
  ∀ δ : ℝ, 0<δ → ∃ C : ℝ, 0≤C ∧ ∀ h : ℕ, 0<h → price A h≤C*(h:ℝ)^δ

private lemma shorten (A : ℕ → ℝ) {u C : ℝ} (hu : 1/2<u) (hC : 0≤C)
    (cap : ∀ h : ℕ, 0<h → price A h ≤ C*(h:ℝ)^(2*u-1)) {n : ℕ} (hn : 8≤n) :
    |A n-A (3*n/4)| ≤ Real.sqrt (96*C)*(n:ℝ)^u := by
  let m := 3*n/4
  have mpos : 0<m := by dsimp [m]; omega
  have mn : m≤n := by dsimp [m]; omega
  have len : (n:ℝ)/4≤((2*m-n:ℕ):ℝ) := by
    have h : n≤4*(2*m-n) := by dsimp [m]; omega
    exact (div_le_iff₀ (by norm_num)).mpr (by exact_mod_cast (by omega : n≤(2*m-n)*4))
  have norm := overlap_price A mn
  have ne : 0<(n:ℝ) := by positivity
  have nk : 1≤(n:ℝ) := by exact_mod_cast (by omega : 1≤n)
  have mkr : ((2*m:ℕ):ℝ)≤2*(n:ℝ) := by exact_mod_cast (by omega : 2*m≤2*n)
  have area : 2*((2*m:ℕ):ℝ)*(((2*m:ℕ):ℝ)+1) ≤ 12*(n:ℝ)^2 := by
    calc
      _ ≤ 2*(2*(n:ℝ))*(2*n+1) := by gcongr
      _ ≤ _ := by nlinarith [mul_nonneg (sub_nonneg.mpr nk) ne.le]
  have high := cap n (by omega)
  have low : price A m ≤ C*(n:ℝ)^(2*u-1) := (cap m mpos).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (by positivity) (by exact_mod_cast mn) (by linarith)) hC)
  have h := (mul_le_mul_of_nonneg_right len (sq_nonneg (A n-A m))).trans
    (norm.trans (mul_le_mul area (add_le_add high low) (add_nonneg (pos_price A n) (pos_price A m)) (by positivity)))
  have exp : ((n:ℝ)^u)^2=(n:ℝ)*(n:ℝ)^(2*u-1) := by
    rw [←Real.rpow_two,←Real.rpow_mul ne.le,show u*2=1+(2*u-1) by ring,Real.rpow_add ne,Real.rpow_one]
  have square : (A n-A m)^2 ≤ (96*C)*((n:ℝ)^u)^2 := by
    rw [exp]
    apply le_of_mul_le_mul_left (a:= (n:ℝ)) _ ne
    nlinarith
  have sq := Real.sq_sqrt (show 0≤96*C by positivity)
  change |A n-A m|≤_
  apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
  rw [sq_abs,mul_pow,sq]
  exact square

/-- Overlap keeps the saved baselines from drifting. Control at all one-octave
windows gives the classical square-root-plus-epsilon growth of the signed walk. -/
theorem walk_growth_of_octaves (budget : AllOctaves walk) : WalkGrowth := by
  intro u hu
  obtain ⟨C,hC,cap⟩ := budget (2*u-1) (by linarith)
  let a := Real.sqrt (96*C)
  let q : ℝ := (3/4:ℝ)^u
  have up : 0<u := by linarith
  have qpos : 0<q := Real.rpow_pos_of_pos (by norm_num) _
  have qlt : q<1 := Real.rpow_lt_one (by norm_num) (by norm_num) up
  let D := a/(1-q)+8
  have apos : 0≤a := Real.sqrt_nonneg _
  have dpos : 8≤D := by dsimp only [D]; linarith [div_nonneg apos (by linarith : 0≤1-q)]
  have contract : a+D*q≤D := by
    have h : a/(1-q)*(1-q)=a := div_mul_cancel₀ _ (sub_ne_zero.mpr qlt.ne')
    dsimp only [D]
    nlinarith
  refine ⟨D,by linarith,?_⟩
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases zero : n=0
    · simp [zero,walk,Real.zero_rpow up.ne']
    by_cases small : n<8
    · have one : 1≤(n:ℝ)^u := Real.one_le_rpow (by exact_mod_cast (by omega : 1≤n)) up.le
      exact (walk_cap _).trans ((show (n:ℝ)≤D by exact le_trans (by exact_mod_cast (by omega : n≤8)) dpos).trans
        (le_mul_of_one_le_right (by linarith) one))
    · let m := 3*n/4
      have mlt : m<n := by dsimp [m]; omega
      have ratio : (m:ℝ) ≤ (3/4:ℝ)*n := by
        have h : 4*m≤3*n := by dsimp [m]; omega
        have rr : 4*(m:ℝ) ≤ 3*n := by exact_mod_cast h
        linarith
      have power := Real.rpow_le_rpow (show 0≤(m:ℝ) by positivity) ratio up.le
      rw [Real.mul_rpow (by norm_num : (0:ℝ)≤3/4) (by positivity)] at power
      have first : |walk n-walk m|≤a*(n:ℝ)^u := shorten walk hu hC cap (by omega)
      have head := (ih m mlt).trans (mul_le_mul_of_nonneg_left power (by linarith : 0≤D))
      have tri := abs_add_le (walk n-walk m) (walk m)
      rw [sub_add_cancel] at tri
      have finish := mul_le_mul_of_nonneg_right contract (show 0≤(n:ℝ)^u by positivity)
      dsimp only [q] at finish
      nlinarith

theorem rh_of_octaves (budget : AllOctaves walk) : RiemannHypothesis :=
  rh_of_walk_growth (walk_growth_of_octaves budget)

#print axioms PALRH.Octaves.overlap_price
#print axioms PALRH.Octaves.rh_of_octaves


/-- The finite price evaluated directly on the legal physical fit in the next octave. -/
def physicalPrice (H : ℕ) : ℚ :=
  ∑ k ∈ Finset.Ioc H (2*H), (OneTick.occupied k-
    Balanced.profile (Balanced.impulse OneTick.occupied) H 1 k)^2/((k:ℚ)*(k+1))

theorem physical_price_eq {H : ℕ} (hH : 0<H) : (physicalPrice H:ℝ)=price walk H := by
  simp only [physicalPrice,price,Rat.cast_sum,Rat.cast_div,Rat.cast_mul,Rat.cast_pow,
    Rat.cast_natCast,Rat.cast_add,Rat.cast_one]
  apply Finset.sum_congr rfl
  intro k hk
  obtain ⟨lo,hi⟩ := Finset.mem_Ioc.mp hk
  have ev := Balanced.next_octave OneTick.occupied (by simp [OneTick.occupied]) hH lo.le hi 1
  have sp : Finset.Icc 1 k=Finset.Icc 1 H ∪ Finset.Ioc H k := by
    ext n; simp only [Finset.mem_union,Finset.mem_Icc,Finset.mem_Ioc]; omega
  have dj : Disjoint (Finset.Icc 1 H) (Finset.Ioc H k) := Finset.disjoint_left.mpr
    (fun _ a b => (not_lt_of_ge (Finset.mem_Icc.mp a).2) (Finset.mem_Ioc.mp b).1)
  have row : ((OneTick.occupied k-Balanced.profile (Balanced.impulse OneTick.occupied) H 1 k:ℚ):ℝ)
      =walk k-walk H := by
    rw [ev]
    simp only [walk,sp,Finset.sum_union dj,add_sub_cancel_left,Rat.cast_sum]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Balanced.occupied_impulse (by have := (Finset.mem_Ioc.mp hd).1; omega)]
    simp [Balanced.mu]
  rw [row]

theorem rh_of_physical_octaves (funded : ∀ δ : ℝ, 0<δ → ∃ C : ℝ, 0≤C ∧
    ∀ H : ℕ, 0<H → (physicalPrice H:ℝ)≤C*(H:ℝ)^δ) : RiemannHypothesis := by
  apply rh_of_octaves
  intro δ pos
  obtain ⟨C,nonneg,paid⟩ := funded δ pos
  exact ⟨C,nonneg,fun h hh => (physical_price_eq hh) ▸ paid h hh⟩

#print axioms PALRH.Octaves.physical_price_eq
#print axioms PALRH.Octaves.rh_of_physical_octaves

end PALRH.Octaves
