import PALRH.ReflectedCells

open Finset Set
open scoped BigOperators Classical
noncomputable section
namespace PALRH.ReflectedCarry
open RectangleBalance TaperedNewton CubicQuadrature ReflectedCells SquarePass

def source (T N : ℕ) : ℝ :=
  ∑ a ∈ Finset.range (N+1), ∑ b ∈ Finset.range (N+1),
    ((2^a*3^b:ℕ):ℝ)*CubicCarry.response T (ReflectedCells.weight T) ((2^a*3^b)^2)

def charge (keep : ℕ → Prop) [DecidablePred keep] (T N : ℕ) : ℝ :=
  ∑ a ∈ Finset.range (N+1), ∑ b ∈ Finset.range (N+1),
    let p : ℕ :=2^a*3^b
    (p:ℝ)*∑ d ∈ Finset.Icc 1 T, if keep (d*p^2) then
      (marks d:ℝ)*(residue T (d*p^2)-residue T (2*(d*p^2))) else 0

private theorem folded_profile (T : ℕ) (p : ℕ) (tp : 0<T) (pp : 0<p) :
    (∑ d ∈ Finset.Icc 1 T, (marks d:ℝ)*(profile T (ReflectedCells.weight T) (d*p^2)-
      profile T (ReflectedCells.weight T) (2*(d*p^2))))=
      CubicCarry.response T (ReflectedCells.weight T) (p^2) := by
  let w:=fun k : ℕ => ReflectedCells.weight T (k*p^2)
  have stop (i : ℕ) (large : T ≤ i) : w i=0 := weight_stop tp _ (large.trans (Nat.le_mul_of_pos_right _ (pow_pos pp 2)))
  have off (i : ℕ) (large : T ≤ i) : profile T w i=0 :=
    Finset.sum_eq_zero (fun r hr => stop _ (large.trans (Nat.le_mul_of_pos_left _ (Finset.mem_Icc.mp hr).1)))
  have same (d : ℕ) : profile T (ReflectedCells.weight T) (d*p^2)=profile T w d := by simp [profile,w,Nat.mul_assoc]
  simp_rw [←Nat.mul_assoc 2 _ (p^2),same]
  rw [←actual_rows _ off,full_grid stop]
  rfl

private theorem single (H p : ℕ) (hp : 0<H) (pp : 0<p) :
    (H:ℝ)/2*shift p edge H =
      (p:ℝ)*CubicCarry.response (2*H) (ReflectedCells.weight (2*H)) (p^2)+
      (p:ℝ)*∑ d ∈ Finset.Icc 1 (2*H), (marks d:ℝ)*(residue (2*H) (d*p^2)-residue (2*H) (2*(d*p^2))) := by
  have pr : 0<(p:ℝ) := by exact_mod_cast pp
  have hr : 0<(H:ℝ) := by exact_mod_cast hp
  have pq : (1:ℝ)≤(p:ℝ)^2 := by exact_mod_cast (show 1≤p^2 from pow_pos pp 2)
  have tp : 0<2*H := by omega
  rw [←folded_profile _ p tp pp,←mul_add,←Finset.sum_add_distrib,Finset.mul_sum,
    shift,edge_pad_positive (X:=(H:ℝ)) (div_pos hr (sq_pos_of_pos pr)) (div_le_self hr.le pq),
    show 2*(H:ℝ)=((2*H:ℕ):ℝ) by push_cast;rfl,Nat.floor_natCast,Finset.sum_div,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have dp : 0<d := (Finset.mem_Icc.mp hd).1
  have dr : 0<(d:ℝ) := by exact_mod_cast dp
  let k:=d*p^2
  have kp : 0<k := Nat.mul_pos dp (pow_pos pp 2)
  have v:=cell_identity (T:=2*H) (d:=k) tp kp
  have w:=cell_identity (T:=2*H) (d:=2*k) tp (by omega)
  have rr:=ramp_difference hp kp
  have total : profile (2*H) (ReflectedCells.weight (2*H)) k-profile (2*H) (ReflectedCells.weight (2*H)) (2*k)+
      (residue (2*H) k-residue (2*H) (2*k))=(H:ℝ)/(2*k)*taper ((k:ℝ)/H) := by linarith
  rw [←mul_add,total]
  dsimp only [k];push_cast
  rw [show (d:ℝ)/((H:ℝ)/(p:ℝ)^2)=((d:ℝ)*p^2)/H by field_simp]
  field_simp

theorem identity (N H : ℕ) (hp : 0<H) :
    (H:ℝ)/2*reading N 1 H=source (2*H) N + charge (fun _ => True) (2*H) N := by
  have expan : reading N 1 H=∑ a ∈ Finset.range (N+1), ∑ b ∈ Finset.range (N+1), shift (2^a*3^b) edge H := by
    change sweep N 2 (sweep N 3 edge) H=_
    rw [sweep]
    apply Finset.sum_congr rfl;intro a _;rw [shift_sweep]
  rw [expan,Finset.mul_sum,source,charge,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl;intro a _
  rw [Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  simpa only [if_true] using single H (2^a*3^b) hp (by positivity)

theorem divide (N T : ℕ) (keep : ℕ→Prop) [DecidablePred keep] :
    charge (fun _ => True) T N=charge keep T N+charge (fun d => ¬keep d) T N := by
  unfold charge
  rw [←Finset.sum_add_distrib];apply Finset.sum_congr rfl;intro a _
  rw [←Finset.sum_add_distrib];apply Finset.sum_congr rfl;intro b _
  rw [←mul_add,←Finset.sum_add_distrib];apply congrArg;apply Finset.sum_congr rfl
  intro d _
  by_cases k : keep (d*(2^a*3^b)^2) <;> simp [k]

#print axioms PALRH.ReflectedCarry.identity
#print axioms PALRH.ReflectedCarry.divide
theorem mark_price (N T D : ℕ) {C : ℝ} (cn : 0≤C)
    {v : ℕ → ℝ} (cap : ∀ k : ℕ, 0<k → k≤D → |v k|≤C) :
    (∑ a ∈ Finset.range (N+1), ∑ b ∈ Finset.range (N+1),
      let p : ℕ := 2^a*3^b
      (p:ℝ)*∑ d ∈ Finset.Icc 1 T, |if d*p^2≤D then (marks d:ℝ)*v (d*p^2) else 0|)≤3*D*C := by
  let J:=Finset.range (N+1)
  have cell (a b : ℕ) :
      let p : ℕ := 2^a*3^b
      (p:ℝ)*(∑ d ∈ Finset.Icc 1 T, |if d*p^2≤D then (marks d:ℝ)*v (d*p^2) else 0|)≤
        ((D:ℝ)*C)*(1/(2:ℝ))^a*(1/(3:ℝ))^b := by
    let p : ℕ := 2^a*3^b
    have pp : 0<p := Nat.mul_pos (pow_pos (by decide) a) (pow_pos (by decide) b)
    have pr : 0<(p:ℝ) := by exact_mod_cast pp
    let I:=(Finset.Icc 1 T).filter (fun d => d*p^2≤D)
    have sub : I⊆Finset.Icc 1 (D/p^2) := fun d hd => Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1,
        (Nat.le_div_iff_mul_le (pow_pos pp 2)).mpr (Finset.mem_filter.mp hd).2⟩
    have count : (I.card:ℝ)≤(D:ℝ)/(p:ℝ)^2 := by
      have card : I.card≤D/p^2 := by simpa [Nat.card_Icc] using Finset.card_le_card sub
      apply (le_div_iff₀ (sq_pos_of_pos pr)).mpr
      exact_mod_cast ((Nat.le_div_iff_mul_le (pow_pos pp 2)).mp card)
    have each (d : ℕ) (hd : d∈Finset.Icc 1 T) :
        |if d*p^2≤D then (marks d:ℝ)*v (d*p^2) else 0| ≤ (if d∈I then C else 0) := by
      by_cases small : d*p^2≤D
      · rw [if_pos small,if_pos (Finset.mem_filter.mpr ⟨hd,small⟩),abs_mul]
        simpa using mul_le_mul (FourthAccounts.mark_cap d)
          (cap _ (Nat.mul_pos (Finset.mem_Icc.mp hd).1 (pow_pos pp 2)) small) (abs_nonneg _) zero_le_one
      · simp [I,small]
    have sum:=Finset.sum_le_sum each
    rw [←Finset.sum_filter] at sum
    have eq : (Finset.Icc 1 T).filter (fun d => d∈I)=I := by ext d;simp [I]
    rw [eq,Finset.sum_const,nsmul_eq_mul] at sum
    have top:=mul_le_mul_of_nonneg_left (sum.trans (mul_le_mul_of_nonneg_right count cn)) pr.le
    apply top.trans_eq
    dsimp [p];push_cast
    rw [one_div_pow,one_div_pow]
    field_simp
  apply (Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => cell a b))).trans
  simp_rw [←Finset.mul_sum]
  rw [←Finset.sum_mul,←Finset.mul_sum]
  have pa:=SquarePassBudget.finite_geometric (by norm_num : 0≤1/(2:ℝ)) (by norm_num) N
  have pb:=SquarePassBudget.finite_geometric (by norm_num : 0≤1/(3:ℝ)) (by norm_num) N
  have total:=mul_le_mul (mul_le_mul_of_nonneg_left pa (by positivity : 0≤(D:ℝ)*C)) pb
    (Finset.sum_nonneg (fun _ _ => by positivity)) (by positivity)
  apply total.trans_eq
  ring

theorem old_charge (N H D : ℕ) (hp : 0<H) :
    |charge (fun k => k≤D) (2*H) N|≤15*(D:ℝ)^3/(4*(H:ℝ)^2) := by
  let T:=2*H
  let v:=fun k => residue T k-residue T (2*k)
  have tp : 0<T := by dsimp [T];omega
  have tr : 0<(T:ℝ) := by exact_mod_cast tp
  have hr : 0<(H:ℝ) := by exact_mod_cast hp
  have localPrice (k : ℕ) (kp : 0<k) (kd : k≤D) : |v k|≤5*((D:ℝ)/T)^2 := by
    have one:=residue_cap tp kp
    have two:=residue_cap tp (show 0<2*k by omega)
    have le : ((k:ℝ)/T)^2≤((D:ℝ)/T)^2 := pow_le_pow_left₀ (by positivity)
      (div_le_div_of_nonneg_right (by exact_mod_cast kd) tr.le) 2
    push_cast at two
    rw [show (2*(k:ℝ)/T)^2=4*((k:ℝ)/T)^2 by ring] at two
    apply (abs_sub _ _).trans
    nlinarith
  have paid:=mark_price N T D (by positivity : 0≤5*((D:ℝ)/T)^2) localPrice
  unfold charge
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply (Finset.sum_le_sum (fun a _ => (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun b _ =>
    (le_of_eq (abs_mul _ _)).trans (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (abs_nonneg _)))))).trans
  simp only [abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) _)]
  exact paid.trans_eq (by dsimp [T];push_cast;field_simp;ring)

def cutoff (j : ℕ) := Nat.findGreatest (fun k => k^3≤j^10) (j^4)

/-- Only high product labels retain a signed obligation; a fixed root-scale debt from the rest is automatic. -/
theorem rh_of_retained (condition : ∃ B : ℕ, ∀ j : ℕ, B≤j → 0<j →
    let H:=j^4
    let N:=Nat.log 2 H+1
    0≤source (2*H) N+charge (fun k => cutoff j<k) (2*H) N) : RiemannHypothesis := by
  obtain ⟨B,late⟩:=condition
  apply CubicFourth.rh_of_fourth_floor (A:=8) (by norm_num)
  refine ⟨B,?_⟩
  intro N j jb jp inside
  let H:=j^4
  let L:=Nat.log 2 H+1
  let D:=cutoff j
  have hp : 0<H := pow_pos jp _
  have jr : 0<(j:ℝ) := by exact_mod_cast jp
  have enough : H≤2^L := (Nat.lt_pow_succ_log_self (by decide : 1<2) H).le
  have x : (H:ℝ)≤(2:ℝ)^N := by exact_mod_cast inside
  have y : (H:ℝ)≤(2:ℝ)^L := by exact_mod_cast enough
  have r1:=CubicFourth.extend_pass (le_max_left N L) (Nat.cast_nonneg (α:=ℝ) H) x
  have r2:=CubicFourth.extend_pass (le_max_right N L) (Nat.cast_nonneg (α:=ℝ) H) y
  have same : reading N 1 H=reading L 1 H := r1.trans r2.symm
  have det:=identity L H hp
  have split:=divide L (2*H) (fun k => k≤D)
  simp only [not_le] at split
  rw [split] at det
  have retained : 0≤source (2*H) L+charge (fun k => D<k) (2*H) L := late j jb jp
  have cost:= (neg_le_abs (charge (fun k => k≤D) (2*H) L)).trans (old_charge L H D hp)
  have power : D^3≤j^10 := Nat.findGreatest_spec (P:=fun k : ℕ => k^3≤j^10) (Nat.zero_le _) (by simp)
  have paid : 15*(D:ℝ)^3/(4*(H:ℝ)^2)≤(15/4:ℝ)*(j:ℝ)^2 := by
    apply (div_le_iff₀ (by positivity : 0<4*(H:ℝ)^2)).mpr
    dsimp [H];push_cast
    have q : (D:ℝ)^3≤(j:ℝ)^10 := by exact_mod_cast power
    nlinarith only [q]
  have floor : -((15/4:ℝ)*(j:ℝ)^2)≤(H:ℝ)/2*reading L 1 H := by linarith
  have castH : (H:ℝ)=(j:ℝ)^4 := by simp [H]
  rw [←castH,same]
  rw [←neg_div]
  apply (div_le_iff₀ (sq_pos_of_pos jr)).mpr
  by_contra! bad
  have r:=mul_lt_mul_of_pos_right bad (sq_pos_of_pos jr)
  have v : (H:ℝ)=(j:ℝ)^4 := by simp [H]
  rw [v] at floor r
  nlinarith only [floor,r,sq_pos_of_pos jr]

#print axioms PALRH.ReflectedCarry.old_charge
#print axioms PALRH.ReflectedCarry.rh_of_retained
end PALRH.ReflectedCarry
