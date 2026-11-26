import PALRH.EvenWindows

open Finset Set
open scoped BigOperators Classical
noncomputable section
namespace PALRH.EvenRemainders
open EvenWindows TaperedNewton

def arch (T d : ℕ) : ℝ := ((T%d:ℕ):ℝ)*((d:ℝ)-(T%d:ℕ))

private theorem arch_bounds (T : ℕ) {d : ℕ} (dp : 0<d) : 0≤arch T d ∧ arch T d≤(d:ℝ)^2 := by
  have m : (T%d:ℕ)≤d := (Nat.mod_lt T dp).le
  have mr : ((T%d:ℕ):ℝ)≤d := by exact_mod_cast m
  unfold arch
  exact ⟨mul_nonneg (by positivity) (sub_nonneg.mpr mr),
    by nlinarith [mul_nonneg (sub_nonneg.mpr mr) (show 0≤(d:ℝ) by positivity),sq_nonneg ((T%d:ℕ):ℝ)]⟩

private theorem arch_tick (T : ℕ) {d : ℕ} (dp : 0<d) : |arch (T+1) d-arch T d|≤d := by
  have low:=Nat.mod_lt T dp
  have rr : ((T+1)%d)=(T%d+1)%d := (Nat.mod_add_mod T d 1).symm
  by_cases hit : T%d+1=d
  · have old : ((T%d:ℕ):ℝ)+1=d := by exact_mod_cast hit
    rw [arch,arch,rr,hit,Nat.mod_self,Nat.cast_zero,zero_mul,zero_sub,abs_neg,
      abs_of_nonneg (mul_nonneg (Nat.cast_nonneg (T%d)) (by linarith))]
    nlinarith
  · have inside : T%d+1<d := by omega
    rw [arch,arch,rr,Nat.mod_eq_of_lt inside,Nat.cast_add,Nat.cast_one,abs_le]
    have m : ((T%d:ℕ):ℝ)+1≤d := by exact_mod_cast inside.le
    constructor <;> nlinarith [Nat.cast_nonneg (α:=ℝ) (T%d)]

theorem arch_span {A B d : ℕ} (ab : A≤B) (dp : 0<d) :
    |arch B d-arch A d|≤((B:ℝ)-A)*d := by
  obtain ⟨k,rfl⟩:=Nat.exists_eq_add_of_le ab
  induction k with
  | zero => simp
  | succ k ih =>
    have t:=arch_tick (A+k) dp
    have eq : arch (A+(k+1)) d-arch A d=(arch (A+k+1) d-arch (A+k) d)+(arch (A+k) d-arch A d) := by rw [Nat.add_assoc];ring
    rw [eq]
    apply (abs_add_le _ _).trans
    have old:=ih (Nat.le_add_right A k)
    push_cast at old ⊢
    linarith

theorem energy_change {A B d : ℕ} (dp : 0<d) (da : d≤A) (ab : A≤B) :
    |EvenWindows.energy B d-EvenWindows.energy A d|≤((B:ℝ)-A)*((d:ℝ)/A)^2 := by
  have dr : 0<(d:ℝ) := by exact_mod_cast dp
  have da' : (d:ℝ)≤A := by exact_mod_cast da
  have ab' : (A:ℝ)≤B := by exact_mod_cast ab
  have ap:=dr.trans_le da'
  have bp:=ap.trans_le ab'
  have len:=sub_nonneg.mpr ab'
  let l:=arch A d
  let r:=arch B d
  have lp : 0≤l := (arch_bounds A dp).1
  have rp : 0≤r := (arch_bounds B dp).1
  have lu : l≤(d:ℝ)^2 := (arch_bounds A dp).2
  have ru : r≤(d:ℝ)^2 := (arch_bounds B dp).2
  have first : |r^2-l^2|≤((B:ℝ)-A)*d*(2*(d:ℝ)^2) := by
    rw [show r^2-l^2=(r-l)*(r+l) by ring,abs_mul,abs_of_nonneg (add_nonneg rp lp)]
    exact mul_le_mul (arch_span ab dp) (by linarith) (add_nonneg rp lp) (mul_nonneg len dr.le)
  have id {T : ℕ} (dt : d≤T) : EvenWindows.energy T d=(arch T d)^2/(4*d*(T:ℝ)^2) := by
    rw [EvenWindows.energy,if_pos dt,arch,mul_pow]
  rw [id (da.trans ab),id da]
  change |r^2/(4*d*(B:ℝ)^2)-l^2/(4*d*(A:ℝ)^2)|≤_
  have eq : r^2/(4*d*(B:ℝ)^2)-l^2/(4*d*(A:ℝ)^2)=
      (r^2-l^2)/(4*d*(B:ℝ)^2)-l^2*((B:ℝ)-A)*(B+A)/(4*d*(A:ℝ)^2*(B:ℝ)^2) := by field_simp;ring
  rw [eq]
  apply (abs_sub _ _).trans
  rw [abs_div,abs_of_pos (show 0<4*(d:ℝ)*B^2 by positivity),
    abs_of_nonneg (show 0≤l^2*((B:ℝ)-A)*(B+A)/(4*d*(A:ℝ)^2*B^2) by positivity)]
  have a : |r^2-l^2|/(4*d*(B:ℝ)^2)≤((B:ℝ)-A)*((d:ℝ)/A)^2/2 := calc
    _ ≤ (((B:ℝ)-A)*d*(2*(d:ℝ)^2))/(4*d*B^2) := div_le_div_of_nonneg_right first (by positivity)
    _ = ((B:ℝ)-A)*((d:ℝ)/B)^2/2 := by field_simp;ring
    _ ≤ _ := by gcongr
  have b : l^2*((B:ℝ)-A)*(B+A)/(4*d*(A:ℝ)^2*(B:ℝ)^2)≤((B:ℝ)-A)*((d:ℝ)/A)^2/2 := calc
    _ ≤ ((d:ℝ)^2)^2*((B:ℝ)-A)*(2*B)/(4*d*(A:ℝ)^2*(B:ℝ)^2) := by gcongr; linarith
    _ = (((B:ℝ)-A)*((d:ℝ)/A)^2/2)*((d:ℝ)/B) := by field_simp;ring
    _ ≤ _ := mul_le_of_le_one_right (by positivity) ((div_le_one bp).mpr (da'.trans ab'))
  linarith

def aggregate (T N : ℕ) (f : ℕ→ℝ) := ∑ a ∈ Finset.range (N+1), ∑ b ∈ Finset.range (N+1),
  let p:ℕ:=2^a*3^b
  (p:ℝ)*∑ d ∈ Finset.Icc 1 T, (marks d:ℝ)*f (d*p^2)

def variation (A B k : ℕ) := (EvenWindows.energy B k-EvenWindows.energy A k)-(EvenWindows.energy B (2*k)-EvenWindows.energy A (2*k))
def base (T N : ℕ) := (T:ℝ)*∑ a ∈ Finset.range (N+1), ∑ b ∈ Finset.range (N+1),
  let p:ℕ:=2^a*3^b
  (p:ℝ)*CubicCarry.response T (CubicWeights.cubic T) (p^2)
def retained (A B N D : ℕ) := base B N-base A N+
  aggregate B N (fun k => if D<k then variation A B k else 0)

private theorem energy_off {A i : ℕ} (large : A ≤ i) : EvenWindows.energy A i=0 := by
  rcases large.lt_or_eq with h|h
  · simp [EvenWindows.energy,not_le.mpr h]
  · subst i;simp [EvenWindows.energy]

theorem split_window {A B : ℕ} (ab : A≤B) (N D : ℕ) :
    total B N-total A N=retained A B N D+
      aggregate B N (fun k => if k≤D then variation A B k else 0) := by
  have pad : price A N (EvenWindows.energy A)=price B N (EvenWindows.energy A) := by
    unfold price
    apply Finset.sum_congr rfl;intro a _
    apply Finset.sum_congr rfl;intro b _
    apply congrArg
    apply Finset.sum_subset (fun d hd => Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1,((Finset.mem_Icc.mp hd).2).trans ab⟩)
    intro d hd out
    have past : A<d := by by_contra! no;exact out (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1,no⟩)
    have p : A≤d*(2^a*3^b)^2 := past.le.trans (Nat.le_mul_of_pos_right _ (by positivity))
    rw [energy_off p,energy_off (by omega : A≤2*(d*(2^a*3^b)^2)),sub_self,mul_zero]
  change (base B N+price B N (EvenWindows.energy B))-(base A N+price A N (EvenWindows.energy A))=_
  rw [pad,retained]
  have rest : price B N (EvenWindows.energy B)-price B N (EvenWindows.energy A)=
      aggregate B N (fun k => if D<k then variation A B k else 0)+
      aggregate B N (fun k => if k≤D then variation A B k else 0) := by
    unfold price aggregate
    rw [←Finset.sum_sub_distrib,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl;intro a _
    rw [←Finset.sum_sub_distrib,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl;intro b _
    rw [←mul_sub,←mul_add,←Finset.sum_sub_distrib,←Finset.sum_add_distrib]
    apply congrArg
    apply Finset.sum_congr rfl
    intro d _
    let k:=d*(2^a*3^b)^2
    change (marks d:ℝ)*(EvenWindows.energy B k-EvenWindows.energy B (2*k))-
      (marks d:ℝ)*(EvenWindows.energy A k-EvenWindows.energy A (2*k))=
      (marks d:ℝ)*(if D<k then variation A B k else 0)+(marks d:ℝ)*(if k≤D then variation A B k else 0)
    by_cases past : D<k
    · simp only [if_pos past,if_neg (not_le.mpr past),mul_zero,add_zero,variation];ring
    · simp only [if_neg past,if_pos (le_of_not_gt past),mul_zero,zero_add,variation];ring
  linarith

theorem early_price {A B D : ℕ} (ap : 0<A) (ab : A≤B) (safe : 2*D≤A) (N : ℕ) :
    |aggregate B N (fun k => if k≤D then variation A B k else 0)|≤15*((B:ℝ)-A)*D^3/(A:ℝ)^2 := by
  let C:=5*((B:ℝ)-A)*((D:ℝ)/A)^2
  have len : 0≤(B:ℝ)-A := sub_nonneg.mpr (by exact_mod_cast ab)
  have ar : 0<(A:ℝ) := by exact_mod_cast ap
  have each (k : ℕ) (kp : 0<k) (kd : k≤D) : |variation A B k|≤C := by
    have u:=energy_change kp (by omega : k≤A) ab
    have v:=energy_change (by omega : 0<2*k) (by omega : 2*k≤A) ab
    push_cast at v
    rw [show (2*(k:ℝ)/A)^2=4*((k:ℝ)/A)^2 by ring] at v
    have grow := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity : 0≤(k:ℝ)/A) (div_le_div_of_nonneg_right (by exact_mod_cast kd : (k:ℝ)≤D) ar.le) 2) len
    apply (abs_sub _ _).trans
    dsimp [C]
    nlinarith
  have paid:=ReflectedCarry.mark_price N B D (show 0≤C by dsimp [C];positivity) each
  unfold aggregate
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply (Finset.sum_le_sum (fun a _ => (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun b _ =>
    (le_of_eq (abs_mul _ _)).trans (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (abs_nonneg _)))))).trans
  simp only [abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) _),mul_ite,mul_zero]
  exact paid.trans_eq (by dsimp [C];field_simp;ring)

theorem rh_of_even_remainders (checks : ∃ J : ℕ, ∀ j : ℕ, J≤j → 0<j →
    let H:=j^4
    let N:=Nat.log 2 (H+j^2)+1
    0≤retained (2*H) (2*(H+j^2)) N (ReflectedCarry.cutoff j)) : RiemannHypothesis := by
  apply rh_of_window_budget (K:=8) (by norm_num)
  obtain ⟨J,ok⟩:=checks
  refine ⟨J,?_⟩
  intro j late jp
  let H:=j^4
  let A:=2*H
  let B:=2*(H+j^2)
  let N:=Nat.log 2 (H+j^2)+1
  let D:=ReflectedCarry.cutoff j
  have hp : 0<H := pow_pos jp 4
  have ap : 0<A := Nat.mul_pos (by decide) hp
  have ab : A≤B := by dsimp [A,B];omega
  have inside : D≤H := Nat.findGreatest_le _
  have power : D^3≤j^10 := Nat.findGreatest_spec (P:=fun k : ℕ => k^3≤j^10) (Nat.zero_le _) (by simp)
  have charge:=(neg_le_abs _).trans (early_price ap ab (by dsimp [A];omega : 2*D≤A) N)
  have cap : 15*((B:ℝ)-A)*D^3/(A:ℝ)^2≤8*(H:ℝ) := by
    have ar : 0<(A:ℝ) := by exact_mod_cast ap
    apply (div_le_iff₀ (sq_pos_of_pos ar)).mpr
    dsimp [A,B,H];push_cast
    have low : (D:ℝ)^3≤(j:ℝ)^10 := by exact_mod_cast power
    nlinarith only [mul_le_mul_of_nonneg_left low (sq_nonneg (j:ℝ)),pow_nonneg (Nat.cast_nonneg (α:=ℝ) j) 12]
  have current : 0≤retained A B N D := ok j late jp
  change -(8*(H:ℝ))≤total B N-total A N
  linarith [split_window ab N D]

#print axioms PALRH.EvenRemainders.arch_span
#print axioms PALRH.EvenRemainders.energy_change
#print axioms PALRH.EvenRemainders.early_price
#print axioms PALRH.EvenRemainders.rh_of_even_remainders
end PALRH.EvenRemainders
