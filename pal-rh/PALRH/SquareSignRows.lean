import PALRH.SquarePassBudget

open Finset Set
open scoped BigOperators
noncomputable section
namespace PALRH.SquareSignRows

open RectangleBalance SquarePass
open TaperedNewton (marks)

/-- The upper endpoint's share in reciprocal coordinates on one half-row. -/
def fraction (n : ℕ) (x : ℝ) := ((n:ℝ)+1)*(2*x-n)/(2*x)
def mix (n : ℕ) (x a b : ℝ) := (1-fraction n x)*a+fraction n x*b

private theorem fraction_range {n : ℕ} (np : 0<n) {x : ℝ} (lo : n≤2*x) (hi : 2*x≤(n:ℝ)+1) :
    0≤fraction n x ∧ fraction n x≤1 := by
  have nr : 0<(n:ℝ) := by exact_mod_cast np
  have den : 0<2*x := nr.trans_le lo
  constructor
  · exact div_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr lo)) den.le
  · apply (div_le_one den).mpr
    nlinarith [mul_nonneg nr.le (sub_nonneg.mpr hi)]

private theorem atom_mix (m : ℕ) {n : ℕ} (np : 0<n) {x : ℝ} (lo : n≤2*x) (hi : 2*x≤(n:ℝ)+1) :
    taper ((m:ℝ)/x)=mix n x (taper ((m:ℝ)/((n:ℝ)/2))) (taper ((m:ℝ)/(((n:ℝ)+1)/2))) := by
  have nr : 0<(n:ℝ) := by exact_mod_cast np
  have xp : 0<x := by linarith
  have lp : 0<(n:ℝ)/2 := by positivity
  have rp : 0<((n:ℝ)+1)/2 := by positivity
  by_cases outside : n+1≤m
  · have mr : (n:ℝ)+1≤m := by exact_mod_cast outside
    have zero (z : ℝ) (zp : 0<z) (small : 2*z≤m) : taper ((m:ℝ)/z)=0 := by
      have h := (le_div_iff₀ zp).mpr small
      rw [taper,min_eq_right (by linarith),max_eq_left (by linarith)]
    rw [zero _ xp (by linarith),zero _ lp (by linarith),zero _ rp (by linarith)]
    simp [mix]
  by_cases inside : 2*m≤n
  · have mr : 2*(m:ℝ)≤n := by exact_mod_cast inside
    have one (z : ℝ) (zp : 0<z) (big : (m:ℝ)≤z) : taper ((m:ℝ)/z)=1 := by
      rw [taper,min_eq_left (by linarith [(div_le_one zp).mpr big]),max_eq_right zero_le_one]
    rw [one _ xp (by linarith),one _ lp (by linarith),one _ rp (by linarith)]
    simp [mix]
  have lower : (m:ℝ)≤n := by exact_mod_cast (show m≤n by omega)
  have upper : (n:ℝ)+1≤2*m := by exact_mod_cast (show n+1≤2*m by omega)
  have ramp (z : ℝ) (zp : 0<z) (p : z≤m) (q : (m:ℝ)≤2*z) : taper ((m:ℝ)/z)=2-m/z := by
    rw [taper,min_eq_right (by linarith [(one_le_div zp).mpr p]),
      max_eq_right (by linarith [(div_le_iff₀ zp).mpr q])]
  rw [ramp _ xp (by linarith) (by linarith),ramp _ lp (by linarith) (by linarith),
    ramp _ rp (by linarith) (by linarith)]
  dsimp only [mix,fraction]
  field_simp [xp.ne',nr.ne',(show (n:ℝ)+1≠0 by positivity)]
  ring

/-- Every positive integer dilation uses the same two endpoint shares. -/
def OnRows (f : ℝ → ℝ) : Prop := ∀ (n d : ℕ), 0<n → 0<d → ∀ x : ℝ,
  n≤2*x → 2*x≤(n:ℝ)+1 →
    f (x/d)=mix n x (f ((n:ℝ)/2/d)) (f (((n:ℝ)+1)/2/d))

theorem edge_rows : OnRows edge := by
  intro n d np dp x lo hi
  have nr : 0<(n:ℝ) := by exact_mod_cast np
  have dr : 0<(d:ℝ) := by exact_mod_cast dp
  have xp : 0<x := by linarith
  let H:=((n:ℝ)+1)/2/d
  have hpos : 0<H := by dsimp [H];positivity
  rw [edge_pad_positive (X:=H) (div_pos xp dr) (div_le_div_of_nonneg_right (by linarith) dr.le),
    edge_pad_positive (X:=H) (div_pos (by positivity : 0<(n:ℝ)/2) dr) (div_le_div_of_nonneg_right (by linarith) dr.le),
    edge_pad_positive (X:=H) hpos le_rfl,mix,Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _
  have assoc (y : ℝ) : (m:ℝ)/(y/d)=((m*d:ℕ):ℝ)/y := by rw [div_div_eq_mul_div];push_cast;rfl
  dsimp only [H]
  simp_rw [assoc]
  rw [atom_mix (m*d) np lo hi]
  unfold mix
  ring

private theorem sweep_rows (N : ℕ) {p : ℕ} (pp : 0<p) {f : ℝ → ℝ} (old : OnRows f) :
    OnRows (sweep N p f) := by
  intro n d np dp x lo hi
  rw [sweep,sweep,sweep,mix,Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  let j := p^i
  have jp : 0<j := pow_pos pp i
  have assoc (y : ℝ) : y/d/(j:ℝ)^2=y/((d*j^2:ℕ):ℝ) := by push_cast;rw [div_div]
  change f (x/d/(j:ℝ)^2)/j=(1-fraction n x)*(f ((n:ℝ)/2/d/(j:ℝ)^2)/j)+
    fraction n x*(f (((n:ℝ)+1)/2/d/(j:ℝ)^2)/j)
  simp_rw [assoc]
  rw [old n (d*j^2) np (Nat.mul_pos dp (pow_pos jp _)) x lo hi]
  unfold mix
  ring

theorem reading_rows (N k : ℕ) : OnRows (reading N k) := by
  induction k with
  | zero => exact edge_rows
  | succ k old => exact sweep_rows N (by decide : 0<2) (sweep_rows N (by decide : 0<3) old)

theorem signs_between (N k : ℕ)
    (ticks : ∀ n : ℕ, n ∈ Finset.Icc 1 (2^(N+1)) → 0≤reading N k ((n:ℝ)/2)) :
    ∀ x ∈ Set.Ioc (0:ℝ) ((2:ℝ)^N), 0≤reading N k x := by
  intro x hx
  by_cases early : x≤1/2
  · rw [(reading_good N k).2 _ early]
  let n:=⌊2*x⌋₊
  have lo : (n:ℝ)≤2*x := Nat.floor_le (by linarith [hx.1])
  have hi : 2*x<(n:ℝ)+1 := Nat.lt_floor_add_one _
  have np : 0<n := (Nat.one_le_floor_iff _).mpr (by linarith)
  have cap : (2:ℝ)^(N+1)=((2^(N+1):ℕ):ℝ) := by push_cast;rfl
  have within : 2*x≤((2^(N+1):ℕ):ℝ) := by rw [←cap,pow_succ];linarith [hx.2]
  have last : n≤2^(N+1) := by exact_mod_cast lo.trans within
  by_cases endRow : n=2^(N+1)
  · have eq : x=(n:ℝ)/2 := by rw [←endRow] at within;linarith
    rw [eq];exact ticks n (Finset.mem_Icc.mpr ⟨np,last⟩)
  have a := ticks n (Finset.mem_Icc.mpr ⟨np,last⟩)
  have b := ticks (n+1) (Finset.mem_Icc.mpr ⟨by omega,by omega⟩)
  have line := reading_rows N k n 1 np (by decide) x lo hi.le
  simp only [Nat.cast_one,div_one] at line
  rw [line,mix]
  push_cast at b
  obtain ⟨l,h⟩ := fraction_range np lo hi.le
  exact add_nonneg (mul_nonneg (sub_nonneg.mpr h) a) (mul_nonneg l b)

/-- A fixed finite list of rational coefficients suffices throughout the sampled head. -/
def qEdge (N : ℕ) (x : ℚ) : ℚ :=
  ∑ m ∈ Finset.Icc 1 (2^(N+1) : ℕ), marks m/m*max 0 (min 1 (2-m/x))
def qSweep (N p : ℕ) (f : ℚ → ℚ) (x : ℚ) : ℚ :=
  ∑ j ∈ Finset.range (N+1), f (x/((p^j:ℕ):ℚ)^2)/(p^j:ℕ)
def qReading (N : ℕ) : ℕ → ℚ → ℚ
  | 0 => qEdge N
  | k+1 => qSweep N 2 (qSweep N 3 (qReading N k))

private theorem edge_cast (N : ℕ) {x : ℚ} (xp : 0<x) (head : x≤(2:ℚ)^N) :
    (qEdge N x:ℝ)=edge (x:ℝ) := by
  have pos : 0<(x:ℝ) := by exact_mod_cast xp
  have cap : (x:ℝ)≤(2:ℝ)^N := by exact_mod_cast head
  have side : 2*(2:ℝ)^N=((2^(N+1):ℕ):ℝ) := by push_cast;rw [pow_succ']
  rw [edge_pad_positive pos cap,side,Nat.floor_natCast,qEdge,Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro m _
  simp only [Rat.cast_mul,Rat.cast_div,Rat.cast_natCast,Rat.cast_max,Rat.cast_min,Rat.cast_zero,
    Rat.cast_one,Rat.cast_sub,Rat.cast_ofNat,taper]

private theorem sweep_cast (N : ℕ) {p : ℕ} (pp : 0<p) {f : ℚ → ℚ} {g : ℝ → ℝ}
    (equal : ∀ z : ℚ, 0<z → z≤(2:ℚ)^N → (f z:ℝ)=g (z:ℝ))
    (x : ℚ) (xp : 0<x) (head : x≤(2:ℚ)^N) :
    (qSweep N p f x:ℝ)=sweep N p g (x:ℝ) := by
  rw [qSweep,Rat.cast_sum,sweep]
  apply Finset.sum_congr rfl
  intro j _
  have jp : (1:ℚ)≤(p^j:ℕ) := by exact_mod_cast (show 1≤p^j from pow_pos pp _)
  have pos : 0<((p^j:ℕ):ℚ)^2 := by positivity
  have cap := (div_le_self xp.le (one_le_pow₀ jp (n:=2))).trans head
  rw [Rat.cast_div,equal _ (div_pos xp pos) cap,shift]
  push_cast
  rfl

theorem reading_cast (N k : ℕ) (x : ℚ) (xp : 0<x) (head : x≤(2:ℚ)^N) :
    (qReading N k x:ℝ)=reading N k (x:ℝ) := by
  induction k generalizing x with
  | zero => exact edge_cast N xp head
  | succ k old =>
    exact sweep_cast N (by decide : 0<2)
      (fun z zp zh => sweep_cast N (by decide : 0<3) old z zp zh) x xp head

/-- For any prescribed doublings per pass, every sufficiently remote starting index has a
later head whose entire finite rational list has nonnegative entries. -/
def SignCheckpoints : Prop := ∀ q : ℕ, 0<q → ∀ B : ℕ, ∃ N : ℕ, B≤N ∧ ∃ k : ℕ,
  0<k ∧ q*k≤N ∧ ∀ n : ℕ, n ∈ Finset.Icc 1 (2^(N+1)) → 0≤qReading N k ((n:ℚ)/2)

theorem rh_of_sign_checkpoints (checks : SignCheckpoints) : RiemannHypothesis := by
  apply SquarePassBudget.rh_of_real_passes
  intro q qp B
  obtain ⟨N,late,k,kp,price,rows⟩ := checks q qp B
  refine ⟨N,late,k,kp,price,signs_between N k ?_⟩
  intro n hn
  obtain ⟨np,inside⟩ := Finset.mem_Icc.mp hn
  have head : (n:ℚ)/2≤(2:ℚ)^N := by
    have ir : (n:ℚ)≤(2:ℚ)^(N+1) := by exact_mod_cast inside
    rw [pow_succ] at ir
    linarith
  have nr : 0<(n:ℚ) := by exact_mod_cast (show 0<n from np)
  have cast := reading_cast N k ((n:ℚ)/2) (by positivity) head
  push_cast at cast
  rw [←cast]
  exact_mod_cast rows n hn

#print axioms PALRH.SquareSignRows.edge_rows
#print axioms PALRH.SquareSignRows.signs_between
#print axioms PALRH.SquareSignRows.reading_cast
#print axioms PALRH.SquareSignRows.rh_of_sign_checkpoints
end PALRH.SquareSignRows
