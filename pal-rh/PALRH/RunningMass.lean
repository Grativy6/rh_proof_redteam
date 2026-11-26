import PALRH.OneHeadPhysical

open Finset
open scoped BigOperators Classical
noncomputable section
namespace PALRH.RunningMass
open TaperedNewton RectangleBalance

def mass (N x : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (N+1),
    let v : ℕ:=2^i*3^j
    (v:ℝ)*∑ d ∈ Finset.Icc 1 (x/v^2), (marks d:ℝ)

private theorem raw_positive (X : ℕ) :
    0 ≤ ∑ r ∈ Finset.Icc 1 X, ∑ d ∈ Finset.Icc 1 (X/r), (marks d:ℝ) := by
  have id := collect X (fun n => (n:ℝ))
  have eq : (∑ r ∈ Finset.Icc 1 X, ∑ d ∈ Finset.Icc 1 (X/r), (marks d:ℝ)) =
      ∑ r ∈ Finset.Icc 1 X, (1/(r:ℝ))*∑ d ∈ Finset.Icc 1 (X/r), (marks d:ℝ)/d*((r*d:ℕ):ℝ) := by
    apply Finset.sum_congr rfl
    intro r hr
    have rr : (r:ℝ)≠0 := by exact_mod_cast (show 0<r from (Finset.mem_Icc.mp hr).1).ne'
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    have dr : (d:ℝ)≠0 := by exact_mod_cast (show 0<d from (Finset.mem_Icc.mp hd).1).ne'
    rw [Nat.cast_mul];field_simp
  rw [eq,id]
  apply Finset.sum_nonneg
  intro n hn
  exact mul_nonneg (div_nonneg (by exact_mod_cast source_nonnegative n) (by positivity)) (by positivity)

theorem positive_multiples (N X : ℕ) :
    0 ≤ ∑ r ∈ Finset.Icc 1 X, mass N (X/r) := by
  unfold mass
  rw [Finset.sum_comm]
  apply Finset.sum_nonneg
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_nonneg
  intro j _
  let v : ℕ:=2^i*3^j
  change 0 ≤ ∑ r ∈ Finset.Icc 1 X, (v:ℝ)*∑ d ∈ Finset.Icc 1 (X/r/v^2), (marks d:ℝ)
  rw [←Finset.mul_sum]
  apply mul_nonneg (by positivity)
  have switch (r : ℕ) : X/r/v^2=X/v^2/r := by rw [Nat.div_div_eq_div_mul,Nat.mul_comm,Nat.div_div_eq_div_mul]
  simp_rw [switch]
  apply le_of_le_of_eq (raw_positive (X/v^2))
  apply Finset.sum_subset (Finset.Icc_subset_Icc_right (Nat.div_le_self _ _))
  intro r hr out
  have far : X/v^2<r := by
    by_contra! small
    exact out (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hr).1,small⟩)
  simp [Nat.div_eq_of_lt far]

/-- Count the rows strictly after X/T. Divisibility at the finite factorial frame
makes both endpoints of the count exact. -/
private theorem repetitions {T X k : ℕ} (tp : 0<T) (xp : 0<X) (kp : 0<k)
    (common : ∀ n : ℕ, 0<n → n≤T → n∣X) :
    (∑ r ∈ Finset.Ioc (X/T) X, (if k≤X/r then (1:ℝ) else 0)) =
      (X:ℝ)/T * max 0 ((T:ℝ)/k-1) := by
  have tr : 0<(T:ℝ) := by exact_mod_cast tp
  have kr : 0<(k:ℝ) := by exact_mod_cast kp
  have set_eq : (Finset.Ioc (X/T) X).filter (fun r => k≤X/r)=Finset.Ioc (X/T) (X/k) := by
    ext r
    simp only [Finset.mem_filter,Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨lo,hi⟩,h⟩
      have rp : 0<r := (Nat.zero_le _).trans_lt lo
      exact ⟨lo,(Nat.le_div_iff_mul_le kp).mpr (by simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le rp).mp h)⟩
    · rintro ⟨lo,hi⟩
      have rp : 0<r := (Nat.zero_le _).trans_lt lo
      exact ⟨⟨lo,hi.trans (Nat.div_le_self _ _)⟩,(Nat.le_div_iff_mul_le rp).mpr
        (by simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le kp).mp hi)⟩
  rw [←Finset.sum_filter,set_eq,Finset.sum_const,Nat.card_Ioc,nsmul_eq_mul,mul_one]
  by_cases active : k≤T
  · have order : X/T≤X/k := Nat.div_le_div_left active kp
    have divT : ((X/T:ℕ):ℝ)=(X:ℝ)/T := Nat.cast_div (common T tp le_rfl) (by exact_mod_cast tp.ne')
    have divK : ((X/k:ℕ):ℝ)=(X:ℝ)/k := Nat.cast_div (common k kp active) (by exact_mod_cast kp.ne')
    have low := (one_le_div kr).mpr (show (k:ℝ)≤T by exact_mod_cast active)
    rw [Nat.cast_sub order,divK,divT,max_eq_right (by linarith)]
    field_simp
  · have order : X/k≤X/T := Nat.div_le_div_left (le_of_not_ge active) tp
    have small := (div_le_one kr).mpr (show (T:ℝ)≤k by exact_mod_cast (le_of_not_ge active))
    rw [Nat.sub_eq_zero_of_le order,Nat.cast_zero,max_eq_left (by linarith),mul_zero]

private theorem truncate {Z T v : ℕ} (before : Z≤T) (vp : 0<v) :
    (∑ d ∈ Finset.Icc 1 (Z/v^2),(marks d:ℝ)) =
      ∑ d ∈ Finset.Icc 1 T, (marks d:ℝ)*(if d*v^2≤Z then 1 else 0) := by
  calc
    _ = ∑ d ∈ Finset.Icc 1 (Z/v^2), (marks d:ℝ)*(if d*v^2≤Z then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro d hd
      simp [(Nat.le_div_iff_mul_le (pow_pos vp 2)).mp (Finset.mem_Icc.mp hd).2]
    _ = _ := by
      apply Finset.sum_subset (Finset.Icc_subset_Icc_right ((Nat.div_le_self _ _).trans before))
      intro d hd out
      have no : ¬d*v^2≤Z := fun h => out (Finset.mem_Icc.mpr
        ⟨(Finset.mem_Icc.mp hd).1,(Nat.le_div_iff_mul_le (pow_pos vp 2)).mpr h⟩)
      simp [no]

/-- The remaining rectangle measures a single primitive on the same physical labels. -/
theorem factorial_price (N T : ℕ) (tp : 0<T) :
    (∑ r ∈ Finset.Ioc (T.factorial/T) T.factorial, mass N (T.factorial/r)) =
      ((T.factorial:ℕ):ℝ)/T *
        ∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (N+1), ∑ d ∈ Finset.Icc 1 T,
          let v : ℕ:=2^i*3^j
          (v:ℝ)*(marks d:ℝ)*max 0 ((T:ℝ)/(d*v^2:ℕ)-1) := by
  let X:=T.factorial
  have xp : 0<X := Nat.factorial_pos _
  have common (n : ℕ) (np : 0<n) (nt : n≤T) : n∣X := Nat.dvd_factorial np nt
  unfold mass
  rw [Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  let v : ℕ:=2^i*3^j
  have vp : 0<v := by dsimp [v];positivity
  have row (r : ℕ) (hr : r∈Finset.Ioc (X/T) X) : (∑ d ∈ Finset.Icc 1 (X/r/v^2), (marks d:ℝ)) =
      ∑ d ∈ Finset.Icc 1 T, (marks d:ℝ)*(if d*v^2≤X/r then 1 else 0) := by
    have rp : 0<r := (Nat.zero_le _).trans_lt (Finset.mem_Ioc.mp hr).1
    have high : X/r<T := by
      apply (Nat.div_lt_iff_lt_mul rp).mpr
      by_contra! h
      exact (Nat.not_le_of_gt (Finset.mem_Ioc.mp hr).1) ((Nat.le_div_iff_mul_le tp).mpr
        (by simpa [Nat.mul_comm] using h))
    exact truncate high.le vp
  change (∑ r ∈ Finset.Ioc (X/T) X, (v:ℝ)*∑ d ∈ Finset.Icc 1 (X/r/v^2),(marks d:ℝ))=_
  rw [Finset.sum_congr rfl (fun r hr => congrArg ((v:ℝ)*·) (row r hr))]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  have dp : 0<d := (Finset.mem_Icc.mp hd).1
  change (∑ r ∈ Finset.Ioc (X/T) X, (v:ℝ)*((marks d:ℝ)*(if d*v^2≤X/r then 1 else 0))) =
    (X:ℝ)/T*((v:ℝ)*(marks d:ℝ)*max 0 ((T:ℝ)/(d*v^2:ℕ)-1))
  simp_rw [←mul_assoc]
  rw [←Finset.mul_sum,repetitions tp xp (Nat.mul_pos dp (pow_pos vp 2)) common]
  ring

def running (n : ℕ) := mass (Nat.log 2 n+1) n

private theorem extend_mass {N K n : ℕ} (nk : N≤K) (covered : n≤2^N) : mass N n=mass K n := by
  let term:=fun i j : ℕ =>
    let v : ℕ := 2^i*3^j
    (v:ℝ)*∑ d ∈ Finset.Icc 1 (n/v^2),(marks d:ℝ)
  have late (k : ℕ) (beyond : N<k) : n<2^k := by
    have step : 2^N<2^(N+1) := by rw [pow_succ];have := Nat.two_pow_pos N;omega
    exact covered.trans_lt (step.trans_le (Nat.pow_le_pow_right (by decide) (by omega)))
  have off (i j : ℕ) (out : N < i ∨ N < j) : term i j=0 := by
    let v : ℕ:=2^i*3^j
    have vp : 0<v := by dsimp [v];positivity
    have vlarge : n<v := by
      rcases out with h|h
      · exact (late i h).trans_le (Nat.le_mul_of_pos_right _ (by positivity))
      · exact (late j h).trans_le ((Nat.pow_le_pow_left (by decide : 2≤3) j).trans
          (Nat.le_mul_of_pos_left _ (by positivity)))
    have square : v≤v^2 := by simpa [pow_two] using Nat.le_mul_of_pos_right v vp
    change (v:ℝ)*∑ d ∈ Finset.Icc 1 (n/v^2),(marks d:ℝ)=0
    simp [Nat.div_eq_of_lt (vlarge.trans_le square)]
  change (∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (N+1),term i j)=
    ∑ i ∈ Finset.range (K+1), ∑ j ∈ Finset.range (K+1),term i j
  have inc : Finset.range (N+1)⊆Finset.range (K+1) := Finset.range_mono (by omega)
  calc
    _ = ∑ i ∈ Finset.range (N+1),∑ j ∈ Finset.range (K+1),term i j := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_subset inc
      intro j _ hj
      simp only [Finset.mem_range,not_lt] at hj
      exact off i j (Or.inr (by omega))
    _ = _ := by
      apply Finset.sum_subset inc
      intro i _ hi
      simp only [Finset.mem_range,not_lt] at hi
      exact Finset.sum_eq_zero (fun j _ => off i j (Or.inl (by omega)))

theorem canonical {N n : ℕ} (inside : n≤2^N) : mass N n=running n := by
  let L:=Nat.log 2 n+1
  have high : n≤2^L := (Nat.lt_pow_succ_log_self (by decide : 1<2) n).le
  exact (extend_mass (le_max_left N L) inside).trans (extend_mass (le_max_right N L) high).symm

theorem price_normalized {j N : ℕ} (jp : 0<j) (inside : j^4≤2^N) :
    (OneHeadPhysical.primitive j:ℝ)=
      ∑ i ∈ Finset.range (N+1), ∑ k ∈ Finset.range (N+1), ∑ d ∈ Finset.Icc 1 (2*j^4),
        let v : ℕ := 2^i*3^k
        (v:ℝ)*(marks d:ℝ)*max 0 (((2*j^4:ℕ):ℝ)/(d*v^2:ℕ)-1) := by
  let H:=j^4
  have hp : 0<H := pow_pos jp _
  have hr : 0<(H:ℝ) := by exact_mod_cast hp
  have hx : (H:ℝ)=(j:ℝ)^4 := by simp [H]
  rw [OneHeadPhysical.price_of_primitive jp inside,←hx,OneHeadPhysical.cap_at_head N H hr le_rfl (by exact_mod_cast inside),
    OneHeadPhysical.visit,Finset.mul_sum]
  apply Finset.sum_congr rfl;intro i _
  rw [Finset.mul_sum];apply Finset.sum_congr rfl;intro k _
  rw [Finset.mul_sum];apply Finset.sum_congr rfl;intro d hd
  let v : ℕ := 2^i*3^k
  let z : ℝ := ((d*v^2:ℕ):ℝ)
  have dp : 0<d := (Finset.mem_Icc.mp hd).1
  have dr : 0<(d:ℝ) := by exact_mod_cast dp
  have vp : 0<v := by dsimp [v];positivity
  have vr : 0<(v:ℝ) := by exact_mod_cast vp
  have zp : 0<z := by dsimp [z];positivity
  change (H:ℝ)*((marks d:ℝ)/(d*(v:ℝ))*max 0 (2-z/H))=(v:ℝ)*(marks d:ℝ)*max 0 (((2*H:ℕ):ℝ)/z-1)
  rw [show ((2*H:ℕ):ℝ)=2*(H:ℝ) by push_cast;rfl]
  have e1 : (H:ℝ)*max 0 (2-z/H)=max 0 (2*H-z) := by rw [mul_max_of_nonneg _ _ hr.le,mul_zero];congr 1;field_simp
  have e2 : z*max 0 (2*H/z-1)=max 0 (2*H-z) := by rw [mul_max_of_nonneg _ _ zp.le,mul_zero];congr 1;field_simp
  calc
    _ = (marks d:ℝ)/(d*(v:ℝ))*((H:ℝ)*max 0 (2-z/H)) := by ring
    _ = _ := by
      rw [e1,←e2]
      dsimp only [z]
      push_cast
      field_simp

theorem split_divisor_rows (X T : ℕ) (f : ℕ → ℝ) :
    (∑ r ∈ Finset.Icc 1 X, f r) =
      (∑ r ∈ Finset.Icc 1 (X/T), f r) + ∑ r ∈ Finset.Ioc (X/T) X, f r := by
  have union : Finset.Icc 1 (X/T) ∪ Finset.Ioc (X/T) X=Finset.Icc 1 X := by
    ext r
    simp only [Finset.mem_union,Finset.mem_Icc,Finset.mem_Ioc]
    constructor
    · rintro (⟨low,high⟩|⟨low,high⟩)
      · exact ⟨low,high.trans (Nat.div_le_self _ _)⟩
      · exact ⟨(Nat.zero_le _).trans_lt low,high⟩
    · rintro ⟨low,high⟩
      by_cases left : r≤X/T
      · exact Or.inl ⟨low,left⟩
      · exact Or.inr ⟨lt_of_not_ge left,high⟩
  have dis : Disjoint (Finset.Icc 1 (X/T)) (Finset.Ioc (X/T) X) := Finset.disjoint_left.mpr
    (fun r a b => (Nat.not_lt_of_ge (Finset.mem_Icc.mp a).2) (Finset.mem_Ioc.mp b).1)
  rw [←union,Finset.sum_union dis]

/-- A negative ordinary running integer suffices. The factorial rectangle is used
only for the finite arithmetic implication and is never enumerated. -/
theorem rh_of_running_nonpositive
    (condition : ∃ B : ℕ, ∀ n : ℕ, B≤n → running n≤0) : RiemannHypothesis := by
  obtain ⟨B,late⟩:=condition
  apply OneHeadPhysical.rh_of_primitive_sign
  refine ⟨max 1 B,?_⟩
  intro j past
  have jp : 0<j := (le_max_left 1 B).trans past
  let T:=2*j^4
  let X:=T.factorial
  let N:=Nat.log 2 X+1
  have tp : 0<T := by dsimp [T];positivity
  have xp : 0<X := Nat.factorial_pos _
  have tX : T≤X := Nat.le_of_dvd xp (Nat.dvd_factorial tp le_rfl)
  have enough : X≤2^N := (Nat.lt_pow_succ_log_self (by decide : 1<2) X).le
  have jh : j≤j^4 := by
    simpa using (Nat.pow_le_pow_right jp (by decide : 1≤4))
  have jt : j^4≤T := by dsimp [T];omega
  have far : B≤T := ((le_max_right 1 B).trans past).trans (jh.trans jt)
  have neg : (∑ r ∈ Finset.Icc 1 (X/T),mass N (X/r))≤0 := by
    apply Finset.sum_nonpos
    intro r hr
    have rp : 0<r := (Finset.mem_Icc.mp hr).1
    rw [canonical ((Nat.div_le_self X r).trans enough)]
    apply late
    exact far.trans ((Nat.le_div_iff_mul_le rp).mpr (by
      simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le tp).mp (Finset.mem_Icc.mp hr).2))
  have whole := positive_multiples N X
  rw [split_divisor_rows X T] at whole
  have non : 0≤∑ r ∈ Finset.Ioc (X/T) X,mass N (X/r) := by linarith
  rw [factorial_price N T tp] at non
  have val:=price_normalized (N:=N) jp (jt.trans (tX.trans enough))
  rw [←val] at non
  have xr : 0<(X:ℝ)/(T:ℝ) := by positivity
  have q : 0≤(OneHeadPhysical.primitive j:ℝ) := nonneg_of_mul_nonneg_right non xr
  exact_mod_cast q

#print axioms PALRH.RunningMass.positive_multiples
#print axioms PALRH.RunningMass.factorial_price
#print axioms PALRH.RunningMass.rh_of_running_nonpositive
end PALRH.RunningMass
