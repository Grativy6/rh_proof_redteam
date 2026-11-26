import PALRH.ReflectedCarry

open Finset
open scoped Classical BigOperators
noncomputable section
namespace PALRH.ReferencePrice
open TaperedNewton RectangleBalance

def ray (T : ℕ) (u : ℕ → ℝ) (d : ℕ) :=
  ∑ k ∈ Finset.Icc 1 T, (allowed k:ℝ)*u (k*d)

def invert (T : ℕ) (f : ℕ → ℝ) (d : ℕ) :=
  ∑ k ∈ Finset.Icc 1 T, (marks k:ℝ)*f (k*d)

private theorem collect_gate (T : ℕ) (tp : 1≤T) (v : ℕ → ℝ)
    (stop : ∀ n, T<n → v n=0) :
    (∑ r ∈ Finset.Icc 1 T, (allowed r:ℝ) *
      ∑ k ∈ Finset.Icc 1 T, (marks k:ℝ)*v (r*k)) = v 1 := by
  have isolated (n : ℕ) : (∑ d ∈ n.divisors, (marks d:ℝ)*(allowed (n/d):ℝ)) =
      if n=1 then 1 else 0 := by
    have h := DFunLike.congr_fun marks_inverse n
    rw [ArithmeticFunction.mul_apply,Nat.sum_divisorsAntidiagonal (fun i j => marks i*allowed j),
      ArithmeticFunction.one_apply] at h
    by_cases one : n=1 <;> simp only [one,if_true,if_false] at h ⊢ <;> exact_mod_cast h
  have shrink (r : ℕ) (hr : r∈Finset.Icc 1 T) :
      (∑ k ∈ Finset.Icc 1 T, (marks k:ℝ)*v (r*k)) =
      ∑ k ∈ Finset.Icc 1 (T/r), (marks k:ℝ)*v (r*k) := by
    symm
    apply Finset.sum_subset (Finset.Icc_subset_Icc_right (Nat.div_le_self T r))
    intro k hk out
    have pr : 0<r := (Finset.mem_Icc.mp hr).1
    have hit : T<r*k := by
      by_contra! inside
      apply out
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hk).1,(Nat.le_div_iff_mul_le pr).mpr
        (by simpa [Nat.mul_comm] using inside)⟩
    rw [stop _ hit,mul_zero]
  calc
    _ = ∑ r ∈ Finset.Icc 1 T, ((allowed r:ℝ)/r) *
        ∑ k ∈ Finset.Icc 1 (T/r), (marks k:ℝ)/k * (((r*k:ℕ):ℝ)*v (r*k)) := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [shrink r hr,Finset.mul_sum,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have rr : (r:ℝ)≠0 := by exact_mod_cast (show 0<r from (Finset.mem_Icc.mp hr).1).ne'
      have kr : (k:ℝ)≠0 := by exact_mod_cast (show 0<k from (Finset.mem_Icc.mp hk).1).ne'
      rw [Nat.cast_mul]
      field_simp
    _ = _ := by
      rw [collect_with T (fun r => (allowed r:ℝ)) (fun n => (n:ℝ)*v n)]
      simp_rw [isolated]
      rw [Finset.sum_eq_single 1]
      · simp
      · intro n _ hn
        simp [hn]
      · simp [Finset.mem_Icc,tp]

/-- The rough divisor operator is inverted on each actual physical ray. -/
theorem invert_ray {T d : ℕ} (tp : 0<T) (dp : 0<d) (u : ℕ → ℝ)
    (stop : ∀ n, T<n → u n=0) : invert T (ray T u) d=u d := by
  have trunc (n : ℕ) (large : T<n) : u (n*d)=0 :=
    stop _ (large.trans_le (Nat.le_mul_of_pos_right _ dp))
  have eq := collect_gate T tp (fun n => u (n*d)) trunc
  simp only [one_mul] at eq
  rw [invert]
  simp_rw [ray,Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ r ∈ Finset.Icc 1 T, (allowed r:ℝ) * ∑ k ∈ Finset.Icc 1 T,
          (marks k:ℝ)*u (r*k*d) := by
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [Nat.mul_assoc]
      ring
    _ = _ := eq

theorem inverted_residual {T d : ℕ} (tp : 0<T) (dp : 0<d) (p u : ℕ → ℝ)
    (stop : ∀ n, T<n → u n=0) :
    invert T (fun n => p n-ray T u n) d = invert T p d-u d := by
  change (∑ k ∈ Finset.Icc 1 T, (marks k:ℝ)*(p (k*d)-ray T u (k*d))) = _
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  change invert T p d - invert T (ray T u) d = _
  rw [invert_ray tp dp u stop]

/-- A negative inverse value forces a positive residual on the sign-reversed ray. -/
theorem negative_ray {T d : ℕ} (tp : 0<T) (dp : 0<d) (p u : ℕ → ℝ)
    (stop : ∀ n, T<n → u n=0) {η : ℝ} (bad : invert T p d ≤ -η) (kept : 0≤u d) :
    η ≤ ∑ k ∈ Finset.Icc 1 T, max 0 (-((marks k:ℝ)*(p (k*d)-ray T u (k*d)))) := by
  have id := inverted_residual tp dp p u stop
  change (∑ k ∈ Finset.Icc 1 T, (marks k:ℝ)*(p (k*d)-ray T u (k*d))) = _ at id
  calc
    _ ≤ -(∑ k ∈ Finset.Icc 1 T, (marks k:ℝ)*(p (k*d)-ray T u (k*d))) := by linarith
    _ = ∑ k ∈ Finset.Icc 1 T, -((marks k:ℝ)*(p (k*d)-ray T u (k*d))) := by rw [Finset.sum_neg_distrib]
    _ ≤ _ := Finset.sum_le_sum (fun _ _ => le_max_right _ _)

theorem absolute_margin {ι : Type*} (I : Finset ι) (z : ι → ℝ) (source : ℝ) :
    (source + ∑ i ∈ I, z i) - (source - ∑ i ∈ I, |z i|) =
      2 * ∑ i ∈ I, max 0 (z i) := by
  rw [Finset.mul_sum,show (source + ∑ i ∈ I, z i) - (source-∑ i ∈ I, |z i|) =
      (∑ i ∈ I, z i)+(∑ i ∈ I, |z i|) by ring, ←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases pos : 0≤z i
  · rw [abs_of_nonneg pos,max_eq_right pos]; ring
  · rw [abs_of_neg (lt_of_not_ge pos),max_eq_left (le_of_lt (lt_of_not_ge pos))]; ring

/-- At the actual tapered target the inverse on d is the earlier raw reading. -/
theorem inverse_is_edge {H d : ℕ} (hp : 0<H) (dp : 0<d) :
    invert (2*H) (fun n => ReflectedCells.ramp (2*H) n-ReflectedCells.ramp (2*H) (2*n)) d =
      ((H:ℝ)/(2*d))*edge ((H:ℝ)/d) := by
  have hr : 0<(H:ℝ) := by exact_mod_cast hp
  have dr : 0<(d:ℝ) := by exact_mod_cast dp
  have d1 : (1:ℝ)≤d := by exact_mod_cast dp
  rw [invert,edge_pad_positive (div_pos hr dr) (div_le_self hr.le d1),
    show 2*(H:ℝ)=((2*H:ℕ):ℝ) by push_cast;ring,Nat.floor_natCast,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have kp : 0<k := (Finset.mem_Icc.mp hk).1
  have kr : (k:ℝ)≠0 := by exact_mod_cast kp.ne'
  rw [ReflectedCells.ramp_difference hp (Nat.mul_pos kp dp),Nat.cast_mul,
    show (k:ℝ)/((H:ℝ)/d)=(k:ℝ)*d/H by field_simp]
  field_simp

theorem actual_prime_sign {q k : ℕ} (prime : q.Prime) (rough : q.Coprime 6) (apart : q.Coprime k) :
    marks (q*k) = -marks k := by
  change (ArithmeticFunction.moebius (q*k):ℚ)*(if (q*k).Coprime 6 then 1 else 0)=
    -((ArithmeticFunction.moebius k:ℚ)*(if k.Coprime 6 then 1 else 0))
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime apart,
    ArithmeticFunction.moebius_apply_prime prime]
  have gate : (q*k).Coprime 6 ↔ k.Coprime 6 := ⟨fun h => (Nat.coprime_mul_iff_left.mp h).2,
    fun h => Nat.coprime_mul_iff_left.mpr ⟨rough,h⟩⟩
  by_cases ok : k.Coprime 6
  · rw [if_pos (gate.mpr ok),if_pos ok]; push_cast; ring
  · rw [if_neg (fun h => ok (gate.mp h)),if_neg ok]; simp

def forced (H d : ℕ) := invert (2*H)
  (fun n => ReflectedCells.ramp (2*H) n-ReflectedCells.ramp (2*H) (2*n)) d

def cut (H N K : ℕ) (early : Bool) :=
  ∑ a ∈ Finset.range (N+1), ∑ b ∈ Finset.range (N+1),
    let v := 2^a*3^b
    if decide (2*H≤K*v^2)=early then (v:ℝ)*forced H (v^2) else 0

theorem true_split (H N K : ℕ) (hp : 0<H) :
    (H:ℝ)/2*SquarePass.reading N 1 H = cut H N K true + cut H N K false := by
  have expan : SquarePass.reading N 1 H = ∑ a ∈ Finset.range (N+1), ∑ b ∈ Finset.range (N+1),
      SquarePass.shift (2^a*3^b) edge H := by
    change SquarePass.sweep N 2 (SquarePass.sweep N 3 edge) H=_
    rw [SquarePass.sweep]
    apply Finset.sum_congr rfl
    intro a _
    rw [SquarePass.shift_sweep]
  rw [expan,Finset.mul_sum,cut,cut,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  let v : ℕ := 2^a*3^b
  have vp : 0<v := by dsimp [v]; positivity
  have vr : (v:ℝ)≠0 := by exact_mod_cast vp.ne'
  change (H:ℝ)/2*SquarePass.shift v edge H =
    (if decide (2*H≤K*v^2)=true then (v:ℝ)*forced H (v^2) else 0)+
    (if decide (2*H≤K*v^2)=false then (v:ℝ)*forced H (v^2) else 0)
  have same : (H:ℝ)/2*SquarePass.shift v edge H=(v:ℝ)*forced H (v^2) := by
    rw [forced,inverse_is_edge hp (pow_pos vp 2),SquarePass.shift,Nat.cast_pow]
    field_simp
  by_cases chosen : 2*H≤K*v^2 <;> simpa [chosen] using same

/-- The earlier true rays can pay a chosen credit at every fourth power. -/
theorem rh_of_remaining_rays (K : ℕ) (credit : ℕ → ℝ) {C : ℝ} (cn : 0≤C)
    (checks : ∃ B : ℕ, ∀ N j : ℕ, B≤j → 0<j → j^4≤2^N →
      credit j≤cut (j^4) N K true ∧ -credit j-C*(j:ℝ)^2≤cut (j^4) N K false) :
    RiemannHypothesis := by
  obtain ⟨B,late⟩ := checks
  apply CubicFourth.rh_of_fourth_floor (A:=2*C) (by positivity)
  refine ⟨B,?_⟩
  intro N j past jp inside
  have split := true_split (j^4) N K (pow_pos jp _)
  push_cast at split
  obtain ⟨paid,due⟩ := late N j past jp inside
  have jr : 0<(j:ℝ) := by exact_mod_cast jp
  apply le_of_mul_le_mul_left (a:=(j:ℝ)^4/2) _ (by positivity)
  calc
    (j:ℝ)^4/2 * (-(2*C/(j:ℝ)^2)) = -(C*(j:ℝ)^2) := by field_simp
    _ ≤ _ := by linarith only [split,paid,due]

#print axioms PALRH.ReferencePrice.true_split
#print axioms PALRH.ReferencePrice.rh_of_remaining_rays
#print axioms PALRH.ReferencePrice.inverse_is_edge
#print axioms PALRH.ReferencePrice.actual_prime_sign
#print axioms PALRH.ReferencePrice.invert_ray
#print axioms PALRH.ReferencePrice.negative_ray
#print axioms PALRH.ReferencePrice.absolute_margin
end PALRH.ReferencePrice
