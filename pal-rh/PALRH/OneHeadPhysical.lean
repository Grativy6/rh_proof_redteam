import PALRH.OneHeadSamples

open Finset Set
open scoped BigOperators Classical
noncomputable section
namespace PALRH.OneHeadPhysical
open SquarePass SquareSignRows RectangleBalance TaperedNewton OneHead OneHeadSamples

def visit (N H : ℕ) (f : ℕ → ℝ) :=
  ∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (N+1), ∑ d ∈ Finset.Icc 1 (2*H),
    let v:=2^i*3^j
    (marks d:ℝ)/((d:ℝ)*(v:ℕ))*f (d*v^2)

private theorem actual {x : ℝ} {H : ℕ} (N : ℕ) (xp : 0<x) (inside : x≤H) :
    reading N 1 x=visit N H (fun n => taper ((n:ℝ)/x)) := by
  change sweep N 2 (sweep N 3 edge) x=_
  rw [sweep,visit]
  apply Finset.sum_congr rfl
  intro i _
  rw [shift_sweep]
  apply Finset.sum_congr rfl
  intro j _
  let v : ℕ:=2^i*3^j
  have vp : 0<v := by dsimp [v];positivity
  have vr : 0<(v:ℝ) := by exact_mod_cast vp
  have big : (1:ℝ)≤(v:ℝ)^2 := by exact_mod_cast (pow_pos vp 2 : 0<v^2)
  change shift v edge x=_
  rw [shift,edge_pad_positive (X:=(H:ℝ)) (div_pos xp (sq_pos_of_pos vr)) ((div_le_self xp.le big).trans inside),
    show 2*(H:ℝ)=((2*H:ℕ):ℝ) by push_cast;ring,Nat.floor_natCast,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d _
  change ((marks d:ℝ)/d*taper ((d:ℝ)/(x/(v:ℝ)^2)))/v=(marks d:ℝ)/(d*(v:ℝ))*taper (((d*v^2:ℕ):ℝ)/x)
  rw [show (d:ℝ)/(x/(v:ℝ)^2)=((d*v^2:ℕ):ℝ)/x by push_cast;field_simp]
  ring

private theorem visit_add_half (N H : ℕ) (f g : ℕ → ℝ) :
    visit N H f+visit N H g/2=visit N H (fun n => f n+g n/2) := by
  unfold visit
  simp only [Finset.sum_div,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl;intro i _
  apply Finset.sum_congr rfl;intro j _
  apply Finset.sum_congr rfl;intro d _
  ring

private theorem visit_congr {N H : ℕ} {f g : ℕ → ℝ} (eq : ∀ n : ℕ, 0<n → f n=g n) :
    visit N H f=visit N H g := by
  unfold visit
  apply Finset.sum_congr rfl;intro i _
  apply Finset.sum_congr rfl;intro j _
  apply Finset.sum_congr rfl;intro d hd
  have dp : 0<d := (Finset.mem_Icc.mp hd).1
  dsimp
  rw [eq _ (by positivity)]

private theorem taper_cap (z : ℝ) : taper z=max 0 (2-z)-max 0 (1-z) := by
  unfold taper
  rcases le_or_gt z 1 with a|a
  · rw [min_eq_left (by linarith),max_eq_right zero_le_one,max_eq_right (by linarith),
      max_eq_right (by linarith)]
    ring
  · rw [min_eq_right (by linarith),max_eq_left (by linarith : 1-z≤0),sub_zero]

private theorem half_max (a : ℝ) : max 0 a/2=max 0 (a/2) := by
  by_cases pos : 0≤a
  · rw [max_eq_right pos,max_eq_right (by positivity)]
  · rw [max_eq_left (le_of_not_ge pos),max_eq_left (by linarith)];ring

private theorem cap_sum (N M H : ℕ) {x : ℝ} (xp : 0<x) (inside : x≤H) :
    bank M (reading N 1) x=visit N H (fun d => max 0 (2-(d:ℝ)/x)-max 0 (1/(2:ℝ)^M-d/x)) := by
  induction M generalizing x with
  | zero =>
    simpa only [bank,pow_zero,div_one,taper_cap] using actual N xp inside
  | succ m ih =>
    change reading N 1 x+bank m (reading N 1) (x/2)/2=_
    rw [actual N xp inside,ih (by positivity : 0<x/2) (by linarith),visit_add_half]
    apply visit_congr
    intro d _
    rw [taper_cap,sub_div,half_max,half_max]
    have u : (2-(d:ℝ)/(x/2))/2=1-d/x := by ring
    have v : (1/(2:ℝ)^m-(d:ℝ)/(x/2))/2=1/2^(m+1)-d/x := by rw [pow_succ];ring
    rw [u,v];ring

theorem cap_at_head (N H : ℕ) {x : ℝ} (xp : 0<x) (small : x≤H) (inside : x≤(2:ℝ)^N) :
    bank N (reading N 1) x = visit N H (fun d => max 0 (2-(d:ℝ)/x)) := by
  rw [cap_sum N N H xp small]
  apply visit_congr
  intro d dp
  have dr : (1:ℝ)≤d := by exact_mod_cast dp
  have st : 1/(2:ℝ)^N ≤ (d:ℝ)/x := (one_div_le_one_div_of_le xp inside).trans
    (div_le_div_of_nonneg_right dr xp.le)
  rw [max_eq_left (sub_nonpos.mpr st),sub_zero]

private theorem same_bank {N M : ℕ} (nm : N≤M) {x : ℝ} (xp : 0≤x) (inside : x≤(2:ℝ)^N) :
    bank N (reading N 1) x=bank M (reading M 1) x := by
  rw [bank_sum,bank_sum]
  calc
    _ = ∑ i ∈ Finset.range (N+1), reading M 1 (x/(2:ℝ)^i)/(2:ℝ)^i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [CubicFourth.extend_pass nm (by positivity : 0≤x/2^i)
        ((div_le_self xp (one_le_pow₀ (by norm_num : (1:ℝ)≤2))).trans inside)]
    _ = _ := by
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro i _ out
      have more : N+1 ≤ i := by simpa only [Finset.mem_range,not_lt] using out
      have pow : 2*(2:ℝ)^N≤(2:ℝ)^i := by
        rw [mul_comm,←pow_succ]
        exact pow_le_pow_right₀ (by norm_num) more
      have stop : x/(2:ℝ)^i≤1/2 := (div_le_iff₀ (by positivity)).mpr (by linarith)
      rw [(reading_good M 1).2 _ stop,zero_div]

/-- One unnormalized finite rational number at each physical fourth-power root.
Its argument is 2*j^4. -/
def primitive (j : ℕ) : ℚ :=
  let H:=j^4
  let N:=Nat.log 2 H+1
  ∑ i ∈ Finset.range (N+1), ∑ b ∈ Finset.range (N+1), ∑ d ∈ Finset.Icc 1 (2*H),
    let v : ℕ:=2^i*3^b
    (marks d)/((d:ℚ)*v)*max 0 (2*(H:ℚ)-(d*v^2:ℕ))

theorem price_of_primitive {N j : ℕ} (jp : 0<j) (inside : j^4≤2^N) :
    (primitive j:ℝ)=(j:ℝ)^4*bank N (reading N 1) ((j:ℝ)^4) := by
  let H:=j^4
  let L:=Nat.log 2 H+1
  have hp : 0<H := pow_pos jp _
  have hr : 0<(H:ℝ) := by exact_mod_cast hp
  have enough : H≤2^L := (Nat.lt_pow_succ_log_self (by decide : 1<2) H).le
  have short : (H:ℝ)≤(2:ℝ)^N := by exact_mod_cast inside
  have long : (H:ℝ)≤(2:ℝ)^L := by exact_mod_cast enough
  have e1:=same_bank (le_max_left N L) hr.le short
  have e2:=same_bank (le_max_right N L) hr.le long
  have eq := e1.trans e2.symm
  have hcast : (H:ℝ)=(j:ℝ)^4 := by simp [H]
  rw [←hcast,eq,cap_at_head L H hr le_rfl long,visit]
  unfold primitive
  push_cast
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl;intro i _
  apply Finset.sum_congr rfl;intro b _
  apply Finset.sum_congr rfl;intro d _
  have rescale (w z c : ℝ) (positive : 0<c) :
      w*max 0 (2*c-z) = c*(w*max 0 (2-z/c)) := by
    have eq : c*max 0 (2-z/c)=max 0 (2*c-z) := by
      rw [mul_max_of_nonneg _ _ positive.le,mul_zero]
      congr 1
      field_simp
    rw [←eq]
    ring
  rw [←hcast]
  exact rescale _ _ _ hr

theorem rh_of_primitive_floor {C : ℝ} (cn : 0≤C)
    (checks : ∃ B : ℕ, ∀ j : ℕ, B≤j → 0<j → -C*(j:ℝ)^2≤(primitive j:ℝ)) :
    RiemannHypothesis := by
  obtain ⟨B,late⟩:=checks
  apply rh_of_bank_fourths cn
  refine ⟨B,?_⟩
  intro N j past jp inside
  have r:=late j past jp
  rw [price_of_primitive jp inside] at r
  have jr : 0<(j:ℝ) := by exact_mod_cast jp
  apply le_of_mul_le_mul_left (a:=(j:ℝ)^4) _ (by positivity)
  apply le_trans _ r
  apply le_of_eq
  field_simp

theorem rh_of_primitive_sign (checks : ∃ B : ℕ, ∀ j : ℕ, B≤j → 0≤primitive j) :
    RiemannHypothesis := by
  obtain ⟨B,late⟩:=checks
  apply rh_of_primitive_floor (C:=0) le_rfl
  refine ⟨B,?_⟩
  intro j past _
  simpa using (show 0≤(primitive j:ℝ) by exact_mod_cast late j past)

#print axioms PALRH.OneHeadPhysical.cap_at_head
#print axioms PALRH.OneHeadPhysical.price_of_primitive
#print axioms PALRH.OneHeadPhysical.rh_of_primitive_floor
#print axioms PALRH.OneHeadPhysical.rh_of_primitive_sign
end PALRH.OneHeadPhysical
