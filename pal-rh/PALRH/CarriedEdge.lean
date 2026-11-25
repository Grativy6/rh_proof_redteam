import PALRH.TaperedNewton

open Finset
open scoped BigOperators
noncomputable section
namespace PALRH.CarriedEdge
open TaperedNewton

/-- The outermost coefficient records all the slope paid by the frame. -/
theorem endpoint {H : ℕ} (hp : 0<H) (f : AF) :
    side H f (2*H) = -2*slope H f := by
  change weight H (2*H)*f (2*H)-bill H (2*H)*slope H f=_
  simp only [weight,bill,show ¬2*H≤H by omega,show H<2*H by omega,le_refl,if_false,if_true,
    and_self,Nat.sub_self,Nat.cast_zero,zero_div,zero_mul,zero_sub,Nat.cast_mul,Nat.cast_ofNat]
  field_simp

/-- Only a row's own past divisors can contribute to its physical count. -/
private lemma cropped {H k : ℕ} (hp : 0<H) (inside : k≤2*H) :
    reading H k=∑ d ∈ Finset.Icc 1 k, side H marks d*fourFloors (k/d) := by
  rw [reading_is_count hp]
  symm
  apply Finset.sum_subset (fun d hd => Finset.mem_Icc.mpr
    ⟨(Finset.mem_Icc.mp hd).1,(Finset.mem_Icc.mp hd).2.trans inside⟩)
  intro d hd out
  have far : k<d := by by_contra! bad;exact out (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1,bad⟩)
  simp [Nat.div_eq_of_lt far,fourFloors]

private theorem raw_read {k : ℕ} (kp : 0<k) :
    (∑ d ∈ Finset.Icc 1 k, marks d*fourFloors (k/d))=1 := by
  have h := agrees_on_head kp kp le_rfl
  rw [cropped kp (by omega),OneTick.occupied,if_neg kp.ne'] at h
  apply Eq.trans _ h
  apply Finset.sum_congr rfl
  intro d hd
  rw [head k marks (Finset.mem_Icc.mp hd).2]

def residual (H k : ℕ) : ℚ := 1-reading H k

theorem strip {H k : ℕ} (hp : 0<H) (lo : H≤k) (hi : k≤2*H) :
    residual H k=∑ d ∈ Finset.Icc (H+1) k, (marks d-side H marks d) := by
  unfold residual
  rw [←raw_read (hp.trans_le lo),cropped hp hi,←Finset.sum_sub_distrib]
  have point (d : ℕ) (hd : d∈Finset.Icc 1 k) :
      marks d*fourFloors (k/d)-side H marks d*fourFloors (k/d)=
      if H<d then marks d-side H marks d else 0 := by
    by_cases inside : d≤H
    · simp [head H marks inside,show ¬H<d by omega]
    · have after : H<d := lt_of_not_ge inside
      have pos := (Finset.mem_Icc.mp hd).1
      have lower : 1≤k/d := (Nat.le_div_iff_mul_le pos).mpr (by simpa using (Finset.mem_Icc.mp hd).2)
      have upper : k/d<2 := (Nat.div_lt_iff_lt_mul pos).mpr (by omega)
      norm_num [show k/d=1 by omega,fourFloors,after]
  have interval : (Finset.Icc 1 k).filter (fun d => H<d)=Finset.Icc (H+1) k := by
    ext d;simp only [Finset.mem_filter,Finset.mem_Icc];omega
  rw [Finset.sum_congr rfl point,←Finset.sum_filter,interval]

theorem read_next_mark {H k : ℕ} (hp : 0<H) (lo : H≤k) (hi : k+1≤2*H) :
    residual H (k+1)-residual H k=marks (k+1)-side H marks (k+1) := by
  rw [strip hp (by omega) hi,strip hp lo (by omega),Finset.sum_Icc_succ_top (by omega)]
  ring

private lemma even_mark (H : ℕ) : marks (2*H)=0 := by
  have no : ¬(2*H).Coprime 6 := by
    intro yes
    have div : 2 ∣ (2*H).gcd 6 := Nat.dvd_gcd (by simp) (by decide)
    rw [show (2*H).gcd 6=1 from yes] at div
    norm_num at div
  change (ArithmeticFunction.moebius (2*H):ℚ)*(if (2*H).Coprime 6 then 1 else 0)=0
  simp [no]

/-- The same slope can be read using just the last two physical rows. -/
theorem last_two_rows {H : ℕ} (hp : 0<H) :
    residual H (2*H)-residual H (2*H-1)=2*slope H marks := by
  have eq : 2*H-1+1=2*H := by omega
  have h := read_next_mark hp (k:=2*H-1) (by omega) (by omega)
  rw [eq,even_mark,endpoint hp] at h
  linarith

/-- The successor's scalar reading uses the same two previously balanced lists. -/
theorem scalar_update {H J K : ℕ} (hH : 0<H) (hJ : 0<J) (keepH : 2*H≤K) (keepJ : 2*J≤K)
    (allowed_cut : 2*K<(H+1)*(J+1)) :
    slope K marks = -slope K (side H marks*side J marks*allowed) := by
  have eq := DFunLike.congr_fun (mixed_update (m:=marks) (g:=allowed) marks_inverse hH hJ keepH keepJ allowed_cut) (2*K)
  have kpos : 0<K := by omega
  have sub (f g : AF) (d : ℕ) : (f-g) d=f d-g d := by
    simp [sub_eq_add_neg,ArithmeticFunction.add_apply,ArithmeticFunction.neg_apply]
  rw [sub,ArithmeticFunction.add_apply,ended H marks (by omega),ended J marks (by omega),endpoint kpos,endpoint kpos] at eq
  linarith

#print axioms PALRH.CarriedEdge.read_next_mark
#print axioms PALRH.CarriedEdge.last_two_rows
#print axioms PALRH.CarriedEdge.scalar_update

private lemma admissible_parent {K : ℕ} (large : 8≤K) :
    0<Nat.sqrt (2*K) ∧ 2*Nat.sqrt (2*K)≤K ∧
    2*K<(Nat.sqrt (2*K)+1)*(Nat.sqrt (2*K)+1) := by
  let H := Nat.sqrt (2*K)
  have before := Nat.lt_succ_sqrt (2*K)
  have left := Nat.sqrt_le (2*K)
  have four : 4≤H := Nat.le_sqrt.mpr (by omega)
  have wide : 2*H≤K := by
    change H*H≤2*K at left
    nlinarith [Nat.mul_le_mul_right H four]
  exact ⟨by omega,wide,before⟩

theorem canonical_update {K : ℕ} (large : 8≤K) :
    slope K marks = -slope K
      (side (Nat.sqrt (2*K)) marks*side (Nat.sqrt (2*K)) marks*allowed) := by
  obtain ⟨hp,wide,before⟩ := admissible_parent large
  exact scalar_update hp hp wide wide before

/-- The unweighted signed count between the two boundaries. -/
def band (H : ℕ) : ℚ := ∑ d ∈ Finset.Ioc H (2*H), marks d

private lemma expanded_weight {H n : ℕ} (hp : 0<H) (top : n≤2*H) :
    weight H n=if n≤H then 1 else 2-(n:ℚ)/H := by
  by_cases front : n≤H
  · simp [weight,front]
  simp only [weight,front,top,if_false,if_true,Nat.cast_sub top,Nat.cast_mul,Nat.cast_ofNat]
  field_simp

/-- The change of the carried rational number has only the signed band and one new mark. -/
theorem step {H : ℕ} (hp : 0<H) :
    slope (H+1) marks-slope H marks=
      band H/((H:ℚ)*(H+1))+marks (2*H+1)/(((2*H+1:ℕ):ℚ)*(H+1)) := by
  let S := Finset.Icc 1 (2*H)
  let term := fun h d : ℕ => weight h d*marks d/d
  have diff (d : ℕ) (hd : d∈S) :
      term (H+1) d-term H d=if H<d then marks d/((H:ℚ)*(H+1)) else 0 := by
    have top := (Finset.mem_Icc.mp hd).2
    have dp := (Finset.mem_Icc.mp hd).1
    dsimp only [term]
    rw [expanded_weight (by omega) (by omega),expanded_weight hp top]
    by_cases front : d≤H
    · simp [front,show d≤H+1 by omega,show ¬H<d by omega]
    have far : H<d := by omega
    have line : (if d≤H+1 then (1:ℚ) else 2-(d:ℚ)/(H+1:ℕ))=2-(d:ℚ)/(H+1:ℕ) := by
      split
      · have deq : d=H+1 := by omega
        subst d
        field_simp
        ring
      · rfl
    rw [line,if_neg front,if_pos far]
    push_cast
    field_simp
    ring
  have gate : S.filter (fun d => H<d)=Finset.Ioc H (2*H) := by
    ext d;simp only [S,Finset.mem_Icc,Finset.mem_filter,Finset.mem_Ioc];omega
  have old : (∑ d ∈ S, (term (H+1) d-term H d))=band H/((H:ℚ)*(H+1)) := by
    rw [Finset.sum_congr rfl diff,←Finset.sum_filter,gate,←Finset.sum_div,band]
  have penult : term (H+1) (2*H+1)=marks (2*H+1)/(((2*H+1:ℕ):ℚ)*(H+1)) := by
    dsimp only [term]
    simp only [weight,show ¬2*H+1≤H+1 by omega,show 2*H+1≤2*(H+1) by omega,if_false,if_true,
      show 2*(H+1)-(2*H+1)=1 by omega,Nat.cast_one,Nat.cast_add,div_eq_mul_inv,mul_inv_rev]
    ring
  have endzero : term (H+1) (2*H+1+1)=0 := by
    simp [term,weight,show ¬2*H+1+1≤H+1 by omega,show 2*H+1+1≤2*(H+1) by omega,
      show 2*(H+1)-(2*H+1+1)=0 by omega]
  change (∑ d ∈ Finset.Icc 1 (2*(H+1)), term (H+1) d)-(∑ d ∈ S, term H d)=_
  rw [show 2*(H+1)=2*H+1+1 by omega,Finset.sum_Icc_succ_top (by omega),Finset.sum_Icc_succ_top (by omega),endzero,penult]
  rw [Finset.sum_sub_distrib] at old
  dsimp only [S] at old ⊢
  linarith

#print axioms PALRH.CarriedEdge.canonical_update
#print axioms PALRH.CarriedEdge.step


theorem band_step {H : ℕ} (hp : 0<H) :
    band (H+1)=band H+marks (2*H+1)-marks (H+1) := by
  let M := fun t : ℕ => ∑ d ∈ Finset.Icc 1 t, marks d
  have inc (t : ℕ) : M (t+1)=M t+marks (t+1) := Finset.sum_Icc_succ_top (by omega) _
  have separate (h : ℕ) (p : 0<h) : band h=M (2*h)-M h := by
    have join : Finset.Icc 1 h ∪ Finset.Ioc h (2*h)=Finset.Icc 1 (2*h) := by
      ext d;simp only [Finset.mem_union,Finset.mem_Icc,Finset.mem_Ioc];omega
    have dis : Disjoint (Finset.Icc 1 h) (Finset.Ioc h (2*h)) := by
      rw [Finset.disjoint_left]
      intro d hd he
      exact (not_lt_of_ge (Finset.mem_Icc.mp hd).2) (Finset.mem_Ioc.mp he).1
    have sum := Finset.sum_union (f:=fun d => marks d) dis
    rw [join] at sum
    change _=M (2*h)-M h
    dsimp only [band,M]
    linarith
  rw [separate _ (by omega),separate H hp,show 2*(H+1)=2*H+1+1 by omega,inc,inc,inc]
  rw [show 2*H+1+1=2*(H+1) by omega,even_mark]
  ring

#print axioms PALRH.CarriedEdge.band_step


private lemma mark_unit (n : ℕ) : |marks n|≤1 := by
  change |(ArithmeticFunction.moebius n:ℚ)*(if n.Coprime 6 then 1 else 0)|≤1
  split
  · rw [mul_one]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n:=n)
  · norm_num

theorem band_cap (H : ℕ) : |band H|≤H := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  have t : (∑ d ∈ Finset.Ioc H (2*H), |marks d|)≤∑ _d ∈ Finset.Ioc H (2*H), (1:ℚ) :=
    Finset.sum_le_sum (fun d _ => mark_unit d)
  simpa [Nat.card_Ioc,show 2*H-H=H by omega] using t

/-- The scalar has uniformly bounded second difference on every arithmetic input here. -/
theorem curvature {H : ℕ} (hp : 0<H) :
    |(slope (H+2) marks-slope (H+1) marks)-(slope (H+1) marks-slope H marks)|≤
      6/((H:ℚ)*(H+1)) := by
  let h : ℚ := H
  have p : 0<h := by dsimp [h];positivity
  let a := marks (2*H+1)-marks (H+1)
  let b := marks (2*(H+1)+1)
  let c := marks (2*H+1)
  have ea : |a|≤2 := (abs_sub _ _).trans (by linarith [mark_unit (2*H+1),mark_unit (H+1)])
  have eb : |b|≤1 := mark_unit _
  have ec : |c|≤1 := mark_unit _
  have bd : |band H|≤h := band_cap H
  have formula :
      ((slope (H+2) marks-slope (H+1) marks)-(slope (H+1) marks-slope H marks))*(h*(h+1)) =
      (h/(h+2))*a-2*(band H/(h+2))+
        (h*(h+1)/((2*(h+1)+1)*(h+2)))*b-(h/(2*h+1))*c := by
    rw [step (H:=H+1) (by omega),step hp,band_step hp]
    dsimp only [h,a,b,c]
    push_cast
    field_simp
    ring
  have rad (u v z : ℚ) (hu : 0≤u) (hv : 0<v) (le : u≤v) : |(u/v)*z|≤|z| := by
    rw [abs_mul,abs_of_nonneg (div_nonneg hu hv.le)]
    exact (mul_le_mul_of_nonneg_right ((div_le_one hv).mpr le) (abs_nonneg z)).trans_eq (one_mul _)
  have a1 := (rad h (h+2) a p.le (by linarith) (by linarith)).trans ea
  have b1 := (rad (h*(h+1)) ((2*(h+1)+1)*(h+2)) b (by positivity) (by positivity)
    (by nlinarith [sq_nonneg h])).trans eb
  have c1 := (rad h (2*h+1) c p.le (by linarith) (by linarith)).trans ec
  have d1 : |band H/(h+2)|≤1 := by
    rw [abs_div,abs_of_pos (by linarith : 0<h+2)]
    exact (div_le_one (by linarith)).mpr (by linarith)
  have t1 := abs_le.mp a1
  have t2 := abs_le.mp b1
  have t3 := abs_le.mp c1
  have t4 := abs_le.mp d1
  change _≤6/(h*(h+1))
  apply (le_div_iff₀ (by positivity)).mpr
  rw [←abs_of_pos (by positivity : 0<h*(h+1)),←abs_mul,formula,abs_le]
  constructor <;> linarith

#print axioms PALRH.CarriedEdge.curvature


def velocity (H : ℕ) : ℚ := slope (H+1) marks-slope H marks

private lemma velocity_span {H : ℕ} (hp : 0<H) (j : ℕ) :
    |velocity (H+j)-velocity H|≤(j:ℚ)*(6/((H:ℚ)*(H+1))) := by
  induction j with
  | zero => simp
  | succ j old =>
    have bend := curvature (H:=H+j) (by omega)
    change |velocity (H+j+1)-velocity (H+j)|≤_ at bend
    have small : 6/(((H+j:ℕ):ℚ)*((H+j:ℕ)+1))≤6/((H:ℚ)*(H+1)) := by
      push_cast
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      nlinarith [Nat.cast_nonneg (α:=ℚ) j,Nat.cast_nonneg (α:=ℚ) H,
        mul_nonneg (Nat.cast_nonneg (α:=ℚ) j) (Nat.cast_nonneg (α:=ℚ) H),sq_nonneg (j:ℚ)]
    have eq : velocity (H+(j+1))-velocity H =
        (velocity (H+j+1)-velocity (H+j))+(velocity (H+j)-velocity H) := by rw [Nat.add_assoc];ring
    rw [eq]
    apply (abs_add_le _ _).trans
    push_cast
    linarith [bend.trans small]

private lemma tangent_error {H : ℕ} (hp : 0<H) (j : ℕ) :
    |slope (H+j) marks-slope H marks-(j:ℚ)*velocity H|≤
      (j:ℚ)^2*(6/((H:ℚ)*(H+1))) := by
  let D : ℚ := 6/((H:ℚ)*(H+1))
  have pos : 0≤D := by dsimp [D];positivity
  induction j with
  | zero => simp
  | succ j old =>
    have eq : slope (H+(j+1)) marks-slope H marks-((j+1:ℕ):ℚ)*velocity H =
        (slope (H+j) marks-slope H marks-(j:ℚ)*velocity H)+(velocity (H+j)-velocity H) := by
      unfold velocity;rw [←Nat.add_assoc H j 1];push_cast;ring
    rw [eq]
    apply (abs_add_le _ _).trans
    have spread := velocity_span hp j
    change _≤(j:ℚ)^2*D at old
    change _≤(j:ℚ)*D at spread
    change _≤((j+1:ℕ):ℚ)^2*D
    push_cast
    nlinarith [mul_nonneg (Nat.cast_nonneg (α:=ℚ) j) pos]

/-- Every intervening integer is within the displayed cost of its chord between two sampled frames. -/
theorem chord {H L k : ℕ} (hp : 0<H) (length_pos : 0<L) (inside : k≤L) :
    |slope (H+k) marks-slope H marks-
      ((k:ℚ)/L)*(slope (H+L) marks-slope H marks)|≤
      2*(L:ℚ)^2*(6/((H:ℚ)*(H+1))) := by
  let D : ℚ := 6/((H:ℚ)*(H+1))
  let err := fun j : ℕ => slope (H+j) marks-slope H marks-(j:ℚ)*velocity H
  have small : |err k|≤(L:ℚ)^2*D := by
    apply (tangent_error hp k).trans
    apply mul_le_mul_of_nonneg_right _ (by positivity : 0≤6/((H:ℚ)*(H+1)))
    exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast inside) _
  have length := tangent_error hp L
  change |err L|≤(L:ℚ)^2*D at length
  have frac : 0≤(k:ℚ)/L := by positivity
  have one : (k:ℚ)/L≤1 := (div_le_one (by positivity)).mpr (by exact_mod_cast inside)
  have eq : slope (H+k) marks-slope H marks-((k:ℚ)/L)*(slope (H+L) marks-slope H marks)=
      err k-((k:ℚ)/L)*err L := by dsimp [err];field_simp;ring
  rw [eq]
  apply (abs_sub _ _).trans
  rw [abs_mul,abs_of_nonneg frac]
  have hit := mul_le_mul_of_nonneg_right one (abs_nonneg (err L))
  change _≤2*(L:ℚ)^2*D
  linarith

#print axioms PALRH.CarriedEdge.chord


theorem fourth_gap {j : ℕ} (positive : 0<j) : (j+1)^4-j^4≤15*j^3 := by
  have e : (j+1)^4=j^4+4*j^3+6*j^2+4*j+1 := by ring
  have a : j^2≤j^3 := Nat.pow_le_pow_right positive (by decide)
  have b : j≤j^3 := by simpa using (Nat.pow_le_pow_right positive (by decide : 1≤3))
  have c : 1≤j^3 := Nat.one_le_pow _ _ positive
  omega

/-- The interpolation price between fourth powers is at most a constant times j to the minus two. -/
theorem fourth_chord {j k : ℕ} (positive : 0<j) (inside : k≤(j+1)^4-j^4) :
    let H:=j^4
    let L:=(j+1)^4-j^4
    |slope (H+k) marks-slope H marks-
      ((k:ℚ)/L)*(slope (H+L) marks-slope H marks)|≤2700/(j:ℚ)^2 := by
  dsimp only
  let L := (j+1)^4-j^4
  have length : 0<L := by dsimp [L];exact Nat.sub_pos_of_lt (Nat.pow_lt_pow_left (by omega) (by decide))
  apply (chord (H:=j^4) (by positivity) length inside).trans
  have lbound : (L:ℚ)≤15*(j:ℚ)^3 := by exact_mod_cast fourth_gap positive
  change 2*(L:ℚ)^2*(6/(((j^4:ℕ):ℚ)*(((j^4:ℕ):ℚ)+1)))≤_
  rw [Nat.cast_pow]
  have c : 6/((j:ℚ)^4*((j:ℚ)^4+1))≤6/((j:ℚ)^4*(j:ℚ)^4) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    nlinarith [show 0≤(j:ℚ)^4 by positivity]
  have l2 := pow_le_pow_left₀ (Nat.cast_nonneg (α:=ℚ) L) lbound 2
  apply (mul_le_mul (mul_le_mul_of_nonneg_left l2 (by norm_num : (0:ℚ)≤2)) c
    (by positivity) (by positivity)).trans_eq
  field_simp
  ring

#print axioms PALRH.CarriedEdge.fourth_chord


/-- The cost of the individual newly admitted odd marks in the unit update. -/
def lastCharge (h : ℕ) : ℚ := marks (2*h+1)/(((2*h+1:ℕ):ℚ)*(h+1))

theorem odd_tail (r : ℕ) : Summable (fun n : ℕ => |(lastCharge (n+r+1):ℝ)|) ∧
    (∑' n : ℕ, |(lastCharge (n+r+1):ℝ)|)≤1/(2*((r:ℝ)+1)) := by
  have bound (n : ℕ) : |(lastCharge (n+r+1):ℝ)|≤rowWeight (n+r)*(1/2) := by
    let h := n+r+1
    have hp : 0<h := by omega
    have mark : |(marks (2*h+1):ℝ)|≤1 := by exact_mod_cast mark_unit (2*h+1)
    have den : 0<((2*h+1:ℕ):ℝ)*((h:ℝ)+1) := by positivity
    change |(lastCharge h:ℝ)|≤_
    simp only [lastCharge,Rat.cast_div,Rat.cast_mul,Rat.cast_natCast,Rat.cast_add,Rat.cast_one,
      abs_div,abs_of_pos den]
    apply (div_le_div_of_nonneg_right mark den.le).trans
    have eq : rowWeight (n+r)=1/((h:ℝ)*((h:ℝ)+1)) := by
      dsimp [rowWeight,h];push_cast;ring_nf
    rw [eq]
    push_cast
    apply (div_le_iff₀ (by positivity)).mpr
    field_simp
    nlinarith [show 0≤(h:ℝ) by positivity]
  have major : Summable (fun n : ℕ => rowWeight (n+r)*(1/2)) :=
    ((summable_nat_add_iff r).mpr rowWeight_hasSum.summable).mul_right _
  have summed := Summable.of_nonneg_of_le (fun n => abs_nonneg _) bound major
  refine ⟨summed,(summed.tsum_le_tsum bound major).trans_eq ?_⟩
  rw [tsum_mul_right,rowWeight_tail]
  field_simp

#print axioms PALRH.CarriedEdge.odd_tail

end PALRH.CarriedEdge
