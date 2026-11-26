import PALRH.ReflectedCarry

open Finset Set
open scoped BigOperators Classical
noncomputable section
namespace PALRH.EvenWindows
open RectangleBalance TaperedNewton CubicQuadrature SquarePass

/-- The time-weighted potential of the unsigned distance to both sides of the same divider. -/
def energy (T d : ℕ) : ℝ := if d≤T then
  ((T%d:ℕ):ℝ)^2*((d:ℝ)-(T%d:ℕ))^2/(4*(d:ℝ)*T^2) else 0
def parent (T d : ℕ) : ℝ := if d≤T then ((T:ℝ)-d)^2/(4*d) else 0

theorem cube_count (T d : ℝ) (k : ℕ) :
    4*d*(∑ n ∈ Finset.Icc 1 k,(T-n*d)^3)=T^2*(T-d)^2-(T-k*d)^2*(T-(k+1)*d)^2 := by
  induction k with
  | zero => simp
  | succ k old =>
    rw [Finset.sum_Icc_succ_top (by omega),mul_add,old]
    push_cast;ring

theorem even_identity {T d : ℕ} (tp : 0<T) (dp : 0<d) :
    parent T d-(T:ℝ)*profile T (CubicWeights.cubic T) d=energy T d := by
  have tr : 0<(T:ℝ) := by exact_mod_cast tp
  have dr : 0<(d:ℝ) := by exact_mod_cast dp
  by_cases active : d≤T
  · let k:=T/d
    let I:=Finset.Icc 1 k
    have shrink : profile T (CubicWeights.cubic T) d=∑ n ∈ I,CubicWeights.cubic T (n*d) := by
      symm
      apply Finset.sum_subset (fun n hn => Finset.mem_Icc.mpr
        ⟨(Finset.mem_Icc.mp hn).1,((Finset.mem_Icc.mp hn).2).trans (Nat.div_le_self _ _)⟩)
      intro n hn out
      have big : T/d<n := by by_contra! h;exact out (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1,h⟩)
      exact CubicWeights.cubic_stop tp _ ((Nat.div_lt_iff_lt_mul dp).mp big).le
    have each (n : ℕ) (hn : n∈I) : CubicWeights.cubic T (n*d)=((T:ℝ)-n*d)^3/T^3 := by
      have good:=(Nat.le_div_iff_mul_le dp).mp (Finset.mem_Icc.mp hn).2
      have low : (n:ℝ)*d/T≤1 := (div_le_one tr).mpr (by exact_mod_cast good)
      rw [CubicWeights.cubic,Nat.cast_mul,max_eq_right (sub_nonneg.mpr low)]
      field_simp
    have r : (T:ℝ)-(k:ℝ)*d=(T%d:ℕ) := by
      have div : ((T%d:ℕ):ℝ)+(d:ℝ)*(k:ℝ)=T := by exact_mod_cast Nat.mod_add_div T d
      linarith
    have next : (T:ℝ)-((k:ℝ)+1)*d= -(d-(T%d:ℕ)) := by linarith
    have eq:=cube_count (T:ℝ) (d:ℝ) k
    rw [r,next] at eq
    rw [parent,energy,if_pos active,if_pos active,shrink,Finset.sum_congr rfl each,←Finset.sum_div]
    field_simp
    dsimp only [I]
    simp only [mul_comm,mul_assoc] at eq ⊢
    linarith
  · have gone : profile T (CubicWeights.cubic T) d=0 := Finset.sum_eq_zero (fun n hn =>
      CubicWeights.cubic_stop tp _ ((le_of_not_ge active).trans (Nat.le_mul_of_pos_left _ (Finset.mem_Icc.mp hn).1)))
    simp [parent,energy,active,gone]

def price (T N : ℕ) (b : ℕ → ℝ) :=
  ∑ a ∈ Finset.range (N+1), ∑ c ∈ Finset.range (N+1),
    let p : ℕ:=2^a*3^c
    (p:ℝ)*∑ d ∈ Finset.Icc 1 T, (marks d:ℝ)*(b (d*p^2)-b (2*(d*p^2)))

theorem quadrature {T : ℕ} (N : ℕ) {b : ℕ → ℝ} (stop : ∀ i : ℕ, T ≤ i → b i=0) :
    (∑ n ∈ Finset.Icc 1 T,cost b n*reading N 1 ((n:ℝ)/2))=price T N b := by
  let I:=Finset.Icc 1 T
  let J:=Finset.range (N+1)
  have row (n : ℕ) : cost b n*reading N 1 ((n:ℝ)/2)=
      ∑ a ∈ J, ∑ c ∈ J, cost b n*shift (2^a*3^c) edge ((n:ℝ)/2) := by
    change cost b n*sweep N 2 (sweep N 3 edge) ((n:ℝ)/2)=_
    rw [sweep,Finset.mul_sum];apply Finset.sum_congr rfl;intro a _;rw [shift_sweep,Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun n _ => row n),Finset.sum_comm,price]
  apply Finset.sum_congr rfl;intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl;intro c _
  let p:ℕ:=2^a*3^c
  have pp : 0<p := Nat.mul_pos (pow_pos (by decide) _) (pow_pos (by decide) _)
  have pr : 0<(p:ℝ) := by exact_mod_cast pp
  have map (n : ℕ) : cost b n*shift p edge ((n:ℝ)/2)=cost b n*edge ((n:ℝ)/2/((p^2:ℕ):ℝ))/p := by
    rw [shift,Nat.cast_pow];ring
  rw [Finset.sum_congr rfl (fun n _ =>map n),←Finset.sum_div,CubicCarry.dilated_rows b (pow_pos pp 2) stop]
  simp only [Nat.mul_assoc, Nat.cast_pow]
  change (p:ℝ)^2*_ /p=(p:ℝ)*_
  field_simp
  rfl

def total (T N : ℕ) := (T:ℝ)*
    (∑ a ∈ Finset.range (N+1), ∑ c ∈ Finset.range (N+1),
      let p:ℕ:=2^a*3^c
      (p:ℝ)*CubicCarry.response T (CubicWeights.cubic T) (p^2))+price T N (energy T)

theorem census {T : ℕ} (tp : 0<T) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 T,cost (parent T) n*reading N 1 ((n:ℝ)/2))=total T N := by
  have stop (i : ℕ) (large : T ≤ i) : parent T i=0 := by
    rcases large.lt_or_eq with h|h
    · simp [parent,not_le.mpr h]
    · simp [←h,parent]
  rw [quadrature N stop,total,price,price,Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl;intro a _
  rw [Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl;intro c _
  let p:ℕ:=2^a*3^c
  have pp : 0<p := Nat.mul_pos (pow_pos (by decide) _) (pow_pos (by decide) _)
  let w:=fun n : ℕ => CubicWeights.cubic T (n*p^2)
  have quiet (i : ℕ) (large : T ≤ i) : w i=0 := CubicWeights.cubic_stop tp _ (large.trans (Nat.le_mul_of_pos_right _ (pow_pos pp 2)))
  have closed (i : ℕ) (large : T ≤ i) : profile T w i=0 := Finset.sum_eq_zero
    (fun k hk => quiet _ (large.trans (Nat.le_mul_of_pos_left _ (Finset.mem_Icc.mp hk).1)))
  have agree (i : ℕ) : profile T (CubicWeights.cubic T) (i*p^2)=profile T w i := by simp [profile,w,Nat.mul_assoc]
  have pay : CubicCarry.response T (CubicWeights.cubic T) (p^2)=
      ∑ d ∈ Finset.Icc 1 T, (marks d:ℝ)*(profile T w d-profile T w (2*d)) := by
    rw [←actual_rows _ closed,full_grid quiet];rfl
  change (p:ℝ)*(∑ d ∈ Finset.Icc 1 T, _)=(T:ℝ)*((p:ℝ)*CubicCarry.response T (CubicWeights.cubic T) (p^2))+(p:ℝ)*_
  rw [pay,mul_left_comm,←mul_add]
  apply congrArg (fun x : ℝ => (p:ℝ)*x)
  rw [Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  have dp : 0<d := (Finset.mem_Icc.mp hd).1
  have e:=even_identity tp (Nat.mul_pos dp (pow_pos pp 2))
  have f:=even_identity tp (Nat.mul_pos (show 0<2*d by omega) (pow_pos pp 2))
  rw [agree] at e f
  simp only [Nat.mul_assoc] at f ⊢
  nlinarith only [congrArg (fun x : ℝ => (marks d:ℝ)*x) e,
    congrArg (fun x : ℝ => (marks d:ℝ)*x) f]

private theorem slope_inside {T n : ℕ} (np : 0<n) (inside : n<T) :
    CubicQuadrature.slope (parent T) n=((T:ℝ)^2-(n:ℝ)*(n+1))/8 := by
  have nr : 0<(n:ℝ) := by exact_mod_cast np
  rw [CubicQuadrature.slope,parent,if_pos inside.le,parent,if_pos (by omega)]
  push_cast;field_simp;ring

private theorem slope_out {T n : ℕ} (away : T≤n) : CubicQuadrature.slope (parent T) n=0 := by
  have a : parent T n=0 := by
    rcases away.lt_or_eq with h|h
    · simp [parent,not_le.mpr h]
    · simp [parent,←h]
  have b : parent T (n+1)=0 := by simp [parent,show ¬n+1≤T by omega]
  rw [CubicQuadrature.slope,a,b];ring

theorem weight_at {T n : ℕ} (np : 2≤n) :
    cost (parent T) n=if n<T then (n:ℝ)/4 else if n=T then (n:ℝ)/8 else 0 := by
  have pr : 0<n-1 := by omega
  have cast : ((n-1:ℕ):ℝ)=(n:ℝ)-1 := by rw [Nat.cast_sub (by omega : 1≤n),Nat.cast_one]
  rw [cost]
  by_cases before : n<T
  · rw [if_pos before,slope_inside pr (by omega),slope_inside (by omega) before,cast];ring
  by_cases hit : n=T
  · subst T
    rw [if_neg (by omega),if_pos rfl,slope_inside pr (by omega),slope_out le_rfl,cast];ring
  rw [if_neg before,if_neg hit,slope_out (by omega : T≤n-1),slope_out (by omega : T≤n)];ring

#print axioms PALRH.EvenWindows.even_identity
#print axioms PALRH.EvenWindows.census
#print axioms PALRH.EvenWindows.weight_at
def cellWeight (A B n : ℕ) : ℝ :=
  if A≤n ∧ n≤B then (if n=A ∨ n=B then (n:ℝ)/8 else (n:ℝ)/4) else 0

private theorem difference_weight {A B n : ℕ} (np : 2≤n) (ab : A<B) :
    cost (parent B) n-cost (parent A) n=cellWeight A B n := by
  rw [weight_at np,weight_at np,cellWeight]
  rcases lt_trichotomy n A with l|eq|u
  · rw [if_pos (l.trans ab),if_pos l,if_neg (by omega)];ring
  · subst n
    rw [if_pos ab,if_neg (by omega),if_pos rfl,if_pos (by omega),if_pos (Or.inl rfl)];ring
  rcases lt_trichotomy n B with l|eq|u'
  · rw [if_pos l,if_neg (by omega),if_neg (by omega),if_pos (by omega),if_neg (by omega)];ring
  · subst n
    simp [ab.ne',not_lt.mpr ab.le]
  · simp [not_lt.mpr u'.le,not_lt.mpr u.le,u'.ne',u.ne',not_le.mpr u']

theorem actual_interval (N : ℕ) {A B : ℕ} (ap : 2≤A) (ab : A<B) :
    total B N-total A N=∑ n ∈ Finset.Icc A B,cellWeight A B n*reading N 1 ((n:ℝ)/2) := by
  have pos : 0<A := by omega
  have pad : (∑ n ∈ Finset.Icc 1 A,cost (parent A) n*reading N 1 ((n:ℝ)/2))=
      ∑ n ∈ Finset.Icc 1 B,cost (parent A) n*reading N 1 ((n:ℝ)/2) := by
    apply Finset.sum_subset (fun n hn => Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hn).1,((Finset.mem_Icc.mp hn).2).trans ab.le⟩)
    intro n hn out
    have big : A<n := by by_contra! h;exact out (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1,h⟩)
    rw [weight_at (by omega : 2≤n),if_neg (by omega),if_neg (by omega),zero_mul]
  rw [←census (by omega : 0<B) N,←census pos N,pad,←Finset.sum_sub_distrib]
  have each (n : ℕ) (hn : n∈Finset.Icc 1 B) :
      cost (parent B) n*reading N 1 ((n:ℝ)/2)-cost (parent A) n*reading N 1 ((n:ℝ)/2)=
      cellWeight A B n*reading N 1 ((n:ℝ)/2) := by
    by_cases first : n=1
    · subst n
      have z:= (reading_good N 1).2 (1/2) le_rfl
      simp only [Nat.cast_one,z,mul_zero,sub_zero]
    have np:0<n := (Finset.mem_Icc.mp hn).1
    rw [←sub_mul,difference_weight (by omega) ab]
  rw [Finset.sum_congr rfl each]
  symm
  apply Finset.sum_subset (fun n hn => Finset.mem_Icc.mpr
    ⟨(show 1≤A by omega).trans (Finset.mem_Icc.mp hn).1,(Finset.mem_Icc.mp hn).2⟩)
  intro n hn absent
  have drop : ¬(A≤n ∧ n≤B) := fun h => absent (Finset.mem_Icc.mpr h)
  simp [cellWeight,drop]

theorem finds_reading (N : ℕ) {A B : ℕ} (ap : 2≤A) (ab : A<B) {C : ℝ} (cn : 0≤C)
    (budget : -(C*((B-A:ℕ):ℝ)*A/8)≤total B N-total A N) :
    ∃ n ∈ Finset.Icc A B, -C≤reading N 1 ((n:ℝ)/2) := by
  let I:=Finset.Icc A B
  have low (n : ℕ) (hn : n∈I) : (A:ℝ)/8≤cellWeight A B n := by
    have pair:=Finset.mem_Icc.mp hn
    rw [cellWeight,if_pos pair];split_ifs <;> linarith [show (A:ℝ)≤n by exact_mod_cast pair.1,Nat.cast_nonneg (α:=ℝ) n]
  have sum:=Finset.sum_le_sum low
  rw [Finset.sum_const,nsmul_eq_mul] at sum
  have enough : B-A≤I.card := by dsimp [I];rw [Nat.card_Icc];omega
  have mass := (mul_le_mul_of_nonneg_right (by exact_mod_cast enough : ((B-A:ℕ):ℝ)≤I.card)
    (show 0≤(A:ℝ)/8 by positivity)).trans sum
  by_contra! no
  have shrink : (∑ n ∈ I,cellWeight A B n*reading N 1 ((n:ℝ)/2))<∑ n ∈ I,cellWeight A B n*(-C) := by
    apply Finset.sum_lt_sum
    · intro n hn;exact mul_le_mul_of_nonneg_left (no n hn).le ((by positivity : 0≤(A:ℝ)/8).trans (low n hn))
    · refine ⟨A,Finset.mem_Icc.mpr ⟨le_rfl,ab.le⟩,?_⟩
      have pos : 0<(A:ℝ) := by exact_mod_cast (show 0<A by omega)
      exact mul_lt_mul_of_pos_left (no _ (Finset.mem_Icc.mpr ⟨le_rfl,ab.le⟩))
        ((by positivity : 0<(A:ℝ)/8).trans_le (low _ (Finset.mem_Icc.mpr ⟨le_rfl,ab.le⟩)))
  rw [←Finset.sum_mul] at shrink
  rw [actual_interval N ap ab] at budget
  nlinarith [mul_le_mul_of_nonneg_right mass cn]

/-- A square-root-width interval may pay a bounded amount per normalized physical row. -/
theorem rh_of_window_budget {K : ℝ} (kn : 0≤K) (checks : ∃ B : ℕ, ∀ j : ℕ, B≤j → 0<j →
    let H:=j^4
    let L:=Nat.log 2 (H+j^2)+1;
    -(K*(H:ℝ))≤total (2*(H+j^2)) L-total (2*H) L) : RiemannHypothesis := by
  apply CubicFourth.rh_of_fourth_floor (A:=2*K+6) (by linarith)
  obtain ⟨B,pay⟩:=checks
  refine ⟨B,?_⟩
  intro N j late jp covered
  let H:=j^4
  let L:=Nat.log 2 (H+j^2)+1
  let A:=2*H
  let T:=2*(H+j^2)
  have hp : 0<H := pow_pos jp _
  have jr : 0<(j:ℝ) := by exact_mod_cast jp
  have hr : 0<(H:ℝ) := by exact_mod_cast hp
  have v : (H:ℝ)=(j:ℝ)^4 := by simp [H]
  have ap : 2≤A := by dsimp [A];omega
  have ab : A<T := by dsimp [A,T];have h : 0<j^2 := pow_pos jp 2;omega
  have width : T-A=2*j^2 := by dsimp [A,T];omega
  have realCost : (2*K/(j:ℝ)^2)*((T-A:ℕ):ℝ)*A/8=K*H := by
    rw [width];dsimp only [A];push_cast;field_simp;ring
  have payment := pay j late jp
  change -(K*(H:ℝ))≤total T L-total A L at payment
  rw [←realCost] at payment
  obtain ⟨n,hn,good⟩:=finds_reading L ap ab (by positivity : 0≤2*K/(j:ℝ)^2) payment
  obtain ⟨past,up⟩:=Finset.mem_Icc.mp hn
  have p : (H:ℝ)≤(n:ℝ)/2 := by
    have s:(2:ℝ)*H≤n := by exact_mod_cast past
    linarith
  have b : (n:ℝ)/2≤(H:ℝ)+(j:ℝ)^2 := by
    have s:(n:ℝ)≤2*((H:ℝ)+(j:ℝ)^2) := by exact_mod_cast up
    linarith
  have diff:=CubicGaps.one_pass_relative L hr p
  have size : ((n:ℝ)/2-H)/H≤1/(j:ℝ)^2 := by
    rw [v];apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    rw [v] at b
    nlinarith [mul_le_mul_of_nonneg_right b (sq_nonneg (j:ℝ))]
  have allowed : H≤2^L := (Nat.le_add_right H (j^2)).trans (Nat.lt_pow_succ_log_self (by decide : 1<2) _).le
  have r1:=CubicFourth.extend_pass (le_max_left N L) hr.le (by exact_mod_cast covered)
  have r2:=CubicFourth.extend_pass (le_max_right N L) hr.le (by exact_mod_cast allowed)
  rw [←v,r1,←r2,add_div]
  have d:=(le_abs_self _).trans diff
  have q:=mul_le_mul_of_nonneg_left size (by norm_num : (0:ℝ)≤6)
  rw [mul_one_div] at q
  linarith only [q,d,good]

#print axioms PALRH.EvenWindows.actual_interval
#print axioms PALRH.EvenWindows.finds_reading
#print axioms PALRH.EvenWindows.rh_of_window_budget

end PALRH.EvenWindows
