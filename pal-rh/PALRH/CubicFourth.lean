import PALRH.CubicCarry

open Finset Set
open scoped BigOperators Classical
noncomputable section
namespace PALRH.CubicFourth
open RectangleBalance SquarePass SquarePassBudget TaperedNewton

private theorem count_band (I : Finset ℕ) {a b : ℝ} (ap : 0≤a) (ab : a≤b) :
    ((I.filter (fun d : ℕ => a≤d ∧ (d:ℝ)≤b)).card:ℝ)≤b-a+1 := by
  let D:=I.filter (fun d : ℕ => a≤d ∧ (d:ℝ)≤b)
  by_cases empty : D=∅
  · change (D.card:ℝ)≤_;rw [empty];simp;linarith
  obtain ⟨d,hd⟩ := Finset.nonempty_iff_ne_empty.mpr empty
  have sub : D⊆Finset.Icc ⌈a⌉₊ ⌊b⌋₊ := by
    intro n hn
    have both := (Finset.mem_filter.mp hn).2
    exact Finset.mem_Icc.mpr ⟨Nat.ceil_le.mpr both.1,Nat.le_floor both.2⟩
  have pair := Finset.mem_Icc.mp (sub hd)
  have price := Finset.card_le_card sub
  rw [Nat.card_Icc] at price
  have r : (D.card:ℝ)≤(⌊b⌋₊:ℝ)+1-⌈a⌉₊ := by
    apply (le_sub_iff_add_le).mpr
    exact_mod_cast (show D.card+⌈a⌉₊≤⌊b⌋₊+1 by omega)
  change (D.card:ℝ)≤_
  linarith [Nat.floor_le (ap.trans ab),Nat.le_ceil a]

/-- A taper has no interpolation defect unless its corner lies inside the frame. -/
theorem seed_chord {a x b t : ℝ} (ap : 0<a) (lo : a≤x) (hi : x≤b)
    (tn : 0≤t) (tu : t≤1) (same : 1/x=(1-t)/a+t/b) :
    |edge x-((1-t)*edge a+t*edge b)|≤((b-a)/(a*b))*(3*(b-a)+2) := by
  have xp:=ap.trans_le lo
  have bp:=xp.trans_le hi
  let I:=Finset.Icc 1 ⌊2*b⌋₊
  let r:= (b-a)/(a*b)
  have rn : 0≤r := div_nonneg (sub_nonneg.mpr (lo.trans hi)) (mul_pos ap bp).le
  let w:=fun (d : ℕ) (y : ℝ) => taper (d/y)
  let E:=fun d : ℕ => (marks d:ℝ)/d*(w d x-((1-t)*w d a+t*w d b))
  have expansion : edge x-((1-t)*edge a+t*edge b)=∑ d ∈ I,E d := by
    rw [edge_pad_positive xp hi,edge_pad_positive ap (lo.trans hi),edge_pad_positive bp le_rfl,
      Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl;intro d _;dsimp [w,E];ring
  let A:=I.filter (fun d : ℕ => a≤d ∧ (d:ℝ)≤b)
  let B:=I.filter (fun d : ℕ => 2*a≤d ∧ (d:ℝ)≤2*b)
  have zero (d : ℕ) (da : d∉A) (db : d∉B) (di : d∈I) : E d=0 := by
    have first : ¬(a≤(d:ℝ) ∧ (d:ℝ)≤b) := fun h => da (Finset.mem_filter.mpr ⟨di,h⟩)
    have second : ¬(2*a≤(d:ℝ) ∧ (d:ℝ)≤2*b) := fun h => db (Finset.mem_filter.mpr ⟨di,h⟩)
    have one {v : ℝ} (vp : 0<v) (p : (d:ℝ)≤v) : w d v=1 := by
      dsimp [w,taper];rw [min_eq_left (by linarith [(div_le_one vp).mpr p]),max_eq_right zero_le_one]
    have out {v : ℝ} (vp : 0<v) (p : 2*v≤d) : w d v=0 := by
      dsimp [w,taper];have h := (le_div_iff₀ vp).mpr p
      rw [min_eq_right (by linarith),max_eq_left (by linarith)]
    have ramp {v : ℝ} (vp : 0<v) (h1 : v≤d) (h2 : (d:ℝ)≤2*v) : w d v=2-d/v := by
      dsimp [w,taper]
      rw [min_eq_right (by linarith [(one_le_div vp).mpr h1]),max_eq_right (by linarith [(div_le_iff₀ vp).mpr h2])]
    dsimp only [E]
    by_cases early : (d:ℝ)≤a
    · rw [one ap early,one xp (early.trans lo),one bp (early.trans (lo.trans hi))];ring
    by_cases late : 2*b≤d
    · rw [out bp late,out xp (by linarith),out ap (by linarith)];ring
    have left : b≤d := by by_contra! h;exact first ⟨(le_of_not_ge early),h.le⟩
    have right : (d:ℝ)≤2*a := by by_contra! h;exact second ⟨h.le,(le_of_not_ge late)⟩
    rw [ramp xp (hi.trans left) (by linarith),ramp ap ((lo.trans hi).trans left) right,
      ramp bp left (by linarith)]
    rw [show (d:ℝ)/x=(d:ℝ)*(1/x) by ring,same]
    ring
  have each (d : ℕ) (di : d∈I) : |E d|≤r := by
    have dr : 0<(d:ℝ) := by exact_mod_cast (show 0<d from (Finset.mem_Icc.mp di).1)
    have inc {v z : ℝ} (vp : 0<v) (order : v≤z) : w d v≤w d z := by
      dsimp [w,taper];apply max_le_max_left;apply min_le_min_left
      linarith [div_le_div_of_nonneg_left dr.le vp order]
    have p:=inc ap lo
    have q:=inc xp hi
    have bounds : |w d x-((1-t)*w d a+t*w d b)|≤w d b-w d a := by
      rw [abs_le]
      constructor <;> nlinarith [mul_nonneg tn (sub_nonneg.mpr (p.trans q)),
        mul_nonneg (sub_nonneg.mpr tu) (sub_nonneg.mpr (p.trans q))]
    have lip:=FourthAccounts.taper_lip ((d:ℝ)/b) (d/a)
    rw [abs_of_nonneg (sub_nonneg.mpr (p.trans q) : 0≤w d b-w d a),
      abs_of_nonpos (sub_nonpos.mpr (div_le_div_of_nonneg_left dr.le ap (lo.trans hi)))] at lip
    rw [show |E d|=|(marks d:ℝ)|/d*|w d x-((1-t)*w d a+t*w d b)| by simp [E,abs_mul,abs_div,abs_of_pos dr]]
    apply (mul_le_mul (div_le_div_of_nonneg_right (FourthAccounts.mark_cap d) dr.le) (bounds.trans lip)
      (abs_nonneg _) (by positivity)).trans_eq
    dsimp [r];field_simp;ring
  have boundA := count_band I ap.le (lo.trans hi)
  have boundB := count_band I (show 0≤2*a by linarith) (show 2*a≤2*b by linarith)
  have cover (d : ℕ) (di : d∈I) : |E d|≤(if d∈A then r else 0)+(if d∈B then r else 0) := by
    by_cases u : d∈A <;> by_cases v : d∈B
    · simp only [if_pos u,if_pos v];linarith [each d di]
    · simpa [u,v] using each d di
    · simpa [u,v] using each d di
    · simp [u,v,zero d u v di]
  rw [expansion]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply (Finset.sum_le_sum cover).trans
  rw [Finset.sum_add_distrib,←Finset.sum_filter,←Finset.sum_filter]
  have sa : I.filter (fun d => d∈A)=A := by ext d;simp [A]
  have sb : I.filter (fun d => d∈B)=B := by ext d;simp [B]
  rw [sa,sb,Finset.sum_const,Finset.sum_const,nsmul_eq_mul,nsmul_eq_mul]
  change (A.card:ℝ)≤b-a+1 at boundA
  change (B.card:ℝ)≤2*b-2*a+1 at boundB
  nlinarith [mul_le_mul_of_nonneg_right (add_le_add boundA boundB) rn]

#print axioms PALRH.CubicFourth.seed_chord
def defect (f : ℝ → ℝ) (a x b t : ℝ) := f x-((1-t)*f a+t*f b)

set_option maxHeartbeats 600000 in
private theorem shifted_fourth (p : ℕ) (pp : 0<p) {j x t : ℝ} (jp : 1≤j)
    (lo : j^4≤x) (hi : x≤(j+1)^4) (tn : 0≤t) (tu : t≤1)
    (same : 1/x=(1-t)/j^4+t/(j+1)^4) :
    |defect (shift p edge) (j^4) x ((j+1)^4) t|≤2000/(j^2*Real.sqrt p) := by
  let H:=j^4
  let Y:=(j+1)^4
  let L:=Y-H
  have jpos : 0<j := by linarith
  have hp : 0<H := by dsimp [H];positivity
  have yp : 0<Y := by dsimp [Y];positivity
  have xp : 0<x := hp.trans_le lo
  have hy : H≤Y := lo.trans hi
  have ln : 0≤L := sub_nonneg.mpr hy
  have pr : 0<(p:ℝ) := by exact_mod_cast pp
  have pu : 1≤(p:ℝ) := by exact_mod_cast pp
  have dn : 0<(p:ℝ)^2 := sq_pos_of_pos pr
  have sq := Real.sq_sqrt pr.le
  have sp := Real.sqrt_pos.mpr pr
  have su : 1≤Real.sqrt p := Real.one_le_sqrt.mpr pu
  by_cases early : Y/(p:ℝ)^2≤1/2
  · have h := edge_before ((div_le_div_of_nonneg_right hi dn.le).trans early)
    have a := edge_before ((div_le_div_of_nonneg_right hy dn.le).trans early)
    change |edge (x/(p:ℝ)^2)/p-((1-t)*(edge (H/(p:ℝ)^2)/p)+t*(edge (Y/(p:ℝ)^2)/p))|≤_
    rw [a,h,edge_before early];simp;positivity
  have span : L≤15*j^3 := by
    dsimp [L,Y,H]
    have j2 : j≤j^2 := by nlinarith [mul_nonneg jpos.le (sub_nonneg.mpr jp)]
    have j3 : j^2≤j^3 := by nlinarith [mul_nonneg (sq_nonneg j) (sub_nonneg.mpr jp)]
    nlinarith
  have ycap : Y≤16*j^4 := by
    have h := pow_le_pow_left₀ (by positivity : 0≤j+1) (by linarith : j+1≤2*j) 4
    dsimp [Y];nlinarith
  have p2 : (p:ℝ)^2<2*Y := by linarith [(lt_div_iff₀ dn).mp (lt_of_not_ge early)]
  have pcap : (p:ℝ)≤6*j^2 := by
    by_contra! bad
    have h:=mul_self_lt_mul_self (by positivity : 0≤6*j^2) bad
    nlinarith
  have scap : Real.sqrt p≤3*j := (Real.sqrt_le_left (by positivity)).mpr (by nlinarith [sq_nonneg j])
  have mix : 1/(x/(p:ℝ)^2)=(1-t)/(H/(p:ℝ)^2)+t/(Y/(p:ℝ)^2) := by
    calc
      _ = (p:ℝ)^2*(1/x) := by field_simp
      _ = _ := by rw [same];dsimp only [H,Y];field_simp
  have raw := seed_chord (div_pos hp dn) (div_le_div_of_nonneg_right lo dn.le)
    (div_le_div_of_nonneg_right hi dn.le) tn tu mix
  have same_def : defect (shift p edge) H x Y t =
      (edge (x/(p:ℝ)^2)-((1-t)*edge (H/(p:ℝ)^2)+t*edge (Y/(p:ℝ)^2)))/p := by
    dsimp [defect,shift];ring
  change |defect (shift p edge) H x Y t|≤_
  rw [same_def,abs_div,abs_of_pos pr]
  apply (div_le_div_of_nonneg_right raw pr.le).trans
  have form : (Y/(p:ℝ)^2-H/(p:ℝ)^2)/(H/(p:ℝ)^2*(Y/(p:ℝ)^2))*
      (3*(Y/(p:ℝ)^2-H/(p:ℝ)^2)+2)/p =
      (L*(3*L/Real.sqrt p+2*p*Real.sqrt p)/(H*Y))/Real.sqrt p := by
    dsimp only [L];field_simp [sp.ne',hp.ne',yp.ne',pr.ne'];rw [sq];ring
  rw [form,show 2000/(j^2*Real.sqrt p)=(2000/j^2)/Real.sqrt p by ring]
  apply div_le_div_of_nonneg_right _ sp.le
  apply (div_le_div_iff₀ (mul_pos hp yp) (sq_pos_of_pos jpos)).mpr
  have pprod := mul_le_mul pcap scap sp.le (by positivity)
  have brace : 3*L/Real.sqrt p+2*p*Real.sqrt p≤81*j^3 := by
    have h := div_le_self (by positivity : 0≤3*L) su
    nlinarith
  have total := mul_le_mul span brace (by positivity) (by positivity)
  have scaled := mul_le_mul_of_nonneg_right total (sq_nonneg j)
  have bulk := mul_le_mul_of_nonneg_left hy hp.le
  dsimp only [H] at bulk ⊢
  nlinarith

private theorem root_power (p : ℝ) (pn : 0≤p) (i : ℕ) : Real.sqrt (p^i)=(Real.sqrt p)^i := by
  induction i with
  | zero => simp
  | succ i old => rw [pow_succ,Real.sqrt_mul (by positivity),old,pow_succ]

private theorem one_pass (N : ℕ) (x : ℝ) : reading N 1 x=
    ∑ a ∈ Finset.range (N+1), ∑ b ∈ Finset.range (N+1), shift (2^a*3^b) edge x := by
  change sweep N 2 (sweep N 3 edge) x=_
  rw [sweep]
  apply Finset.sum_congr rfl;intro a _;rw [shift_sweep]

def factor (p : ℕ) := 1/(1-1/Real.sqrt p)
def totalPrice := 2000*factor 2*factor 3

private theorem factor_pos {p : ℕ} (pp : 1<p) : 0<factor p := by
  have pos : 1<Real.sqrt p := by simpa using Real.sqrt_lt_sqrt (by norm_num : (0:ℝ)≤1) (by exact_mod_cast pp : (1:ℝ)<p)
  exact div_pos zero_lt_one (sub_pos.mpr ((div_lt_one (by linarith)).mpr pos))

theorem total_pos : 0<totalPrice := mul_pos (mul_pos (by norm_num) (factor_pos (by decide))) (factor_pos (by decide))

private theorem root_sum (N p : ℕ) (pp : 1<p) :
    (∑ i ∈ Finset.range (N+1), (1/Real.sqrt p)^i)≤factor p := by
  have pos : 1<Real.sqrt p := by simpa using Real.sqrt_lt_sqrt (by norm_num : (0:ℝ)≤1) (by exact_mod_cast pp : (1:ℝ)<p)
  exact finite_geometric (by positivity) ((div_lt_one (by linarith)).mpr pos) _

theorem pass_chord (N : ℕ) {j x t : ℝ} (jp : 1≤j)
    (lo : j^4≤x) (hi : x≤(j+1)^4) (tn : 0≤t) (tu : t≤1)
    (same : 1/x=(1-t)/j^4+t/(j+1)^4) :
    |defect (reading N 1) (j^4) x ((j+1)^4) t|≤totalPrice/j^2 := by
  let J:=Finset.range (N+1)
  let f:=fun a b : ℕ => shift (2^a*3^b) edge
  let d:=fun a b : ℕ => defect (f a b) (j^4) x ((j+1)^4) t
  let r:=1/Real.sqrt 2
  let s:=1/Real.sqrt 3
  have identity : defect (reading N 1) (j^4) x ((j+1)^4) t=∑ a ∈ J, ∑ b ∈ J, d a b := by
    rw [defect,one_pass,one_pass,one_pass]
    simp only [Finset.mul_sum,←Finset.sum_add_distrib,←Finset.sum_sub_distrib]
    rfl
  have each (a b : ℕ) : |d a b|≤(2000/j^2)*r^a*s^b := by
    apply (shifted_fourth (2^a*3^b) (by positivity) jp lo hi tn tu same).trans_eq
    dsimp [r,s]
    push_cast
    rw [Real.sqrt_mul (by positivity),root_power 2 (by norm_num),root_power 3 (by norm_num)]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  rw [identity]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply (Finset.sum_le_sum (fun a _ => (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum (fun b _ => each a b)))).trans
  simp_rw [←Finset.mul_sum]
  rw [←Finset.sum_mul,←Finset.mul_sum]
  have a:=root_sum N 2 (by decide)
  have b:=root_sum N 3 (by decide)
  have rn : 0≤∑ i ∈ J,s^i := Finset.sum_nonneg (fun _ _ => by dsimp [s];positivity)
  have p:=mul_le_mul (mul_le_mul_of_nonneg_left a (by positivity : 0≤2000/j^2)) b rn
    (mul_nonneg (by positivity) (factor_pos (by decide : 1<2)).le)
  exact p.trans_eq (by unfold totalPrice;ring)

#print axioms PALRH.CubicFourth.pass_chord
private theorem interpolation {a x b : ℝ} (ap : 0<a) (lo : a≤x) (hi : x≤b) (strict : a<b) :
    ∃ t : ℝ, 0≤t ∧ t≤1 ∧ 1/x=(1-t)/a+t/b := by
  have xp:=ap.trans_le lo
  have pos : 0<1/a-1/b := sub_pos.mpr (one_div_lt_one_div_of_lt ap strict)
  let t:=(1/a-1/x)/(1/a-1/b)
  have h1:=one_div_le_one_div_of_le ap lo
  have h2:=one_div_le_one_div_of_le xp hi
  have used : t*(1/a-1/b)=1/a-1/x := div_mul_cancel₀ _ pos.ne'
  refine ⟨t,div_nonneg (by linarith) pos.le,(div_le_one pos).mpr (by linarith),?_⟩
  rw [show (1-t)/a+t/b=1/a-t*(1/a-1/b) by ring,used];ring

/-- Only the rational sign of the first complete square pass at sufficiently late fourth powers. -/
def FourthSigns : Prop := ∃ B : ℕ, ∀ N j : ℕ, B≤j → 0<j → j^4≤2^N →
    0≤SquareSignRows.qReading N 1 ((j:ℚ)^4)

theorem rh_of_fourth_signs (checks : FourthSigns) : RiemannHypothesis := by
  obtain ⟨B,sign⟩ := checks
  apply CubicGaps.rh_of_first_pass_floors
  intro e ep small
  let C:=4*totalPrice+3*((B:ℝ)+1)^2+3
  have cn : 0<C := by dsimp [C];positivity [total_pos]
  have c3 : 3≤C := by dsimp [C];nlinarith [total_pos,sq_nonneg ((B:ℝ)+1)]
  have cost : 4*totalPrice≤C := by dsimp [C];nlinarith [sq_nonneg ((B:ℝ)+1)]
  refine ⟨C,cn.le,?_⟩
  intro N
  let K:=N+4
  refine ⟨K,by dsimp [K];omega,?_⟩
  intro x hx
  have xp:=hx.1
  have amplitude' := neg_le_abs (reading K 1 x) |>.trans (amplitude K 1 x xp)
  norm_num at amplitude'
  by_cases tiny : x<1
  · have more : 1≤x^(e-1/2) := by
      simpa using Real.rpow_le_rpow_of_nonpos xp tiny.le (sub_nonpos.mpr small)
    nlinarith [mul_le_mul_of_nonneg_left more cn.le]
  have x1:=le_of_not_gt tiny
  let root:=Real.sqrt (Real.sqrt x)
  have root_unit : 1≤root := Real.one_le_sqrt.mpr (Real.one_le_sqrt.mpr x1)
  have rt : root^4=x := by
    have a:=Real.sq_sqrt (Real.sqrt_nonneg x)
    have b:=Real.sq_sqrt xp.le
    dsimp [root];rw [show (4:ℕ)=2*2 by norm_num,pow_mul,a,b]
  let j:=⌊root⌋₊
  have jp : 0<j := (Nat.one_le_floor_iff _).mpr root_unit
  have jr : (1:ℝ)≤j := by exact_mod_cast jp
  have jpos : 0<(j:ℝ) := by positivity
  have lo : (j:ℝ)^4≤x := (pow_le_pow_left₀ (by positivity) (Nat.floor_le (zero_le_one.trans root_unit)) 4).trans_eq rt
  have hi : x<((j:ℝ)+1)^4 := rt.symm.trans_lt (pow_lt_pow_left₀ (Nat.lt_floor_add_one root)
    (zero_le_one.trans root_unit) (by decide : 4≠0))
  have sr : Real.sqrt x≤((j:ℝ)+1)^2 := (Real.sqrt_le_left (by positivity)).mpr (by nlinarith)
  have four : Real.sqrt x≤4*(j:ℝ)^2 := sr.trans (by nlinarith [sq_nonneg ((j:ℝ)-1)])
  have floor : -(C/Real.sqrt x)≤reading K 1 x := by
    by_cases active : B≤j
    · have lasted : ((j:ℝ)+1)^4≤(2:ℝ)^K := calc
        _ ≤ (2*(j:ℝ))^4 := pow_le_pow_left₀ (by positivity) (by linarith) _
        _ = (j:ℝ)^4*16 := by ring
        _ ≤ (2:ℝ)^N*16 := mul_le_mul_of_nonneg_right (lo.trans hx.2) (by norm_num)
        _ = _ := by simp [K,pow_add];ring
      have at_root (i : ℕ) (above : B ≤ i) (ip : 0 < i) (within : (i:ℝ)^4≤(2:ℝ)^K) :
          0≤reading K 1 ((i:ℝ)^4) := by
        have pos : 0<(i:ℚ)^4 := by positivity
        have rat : (i:ℚ)^4≤(2:ℚ)^K := by exact_mod_cast within
        have cast := SquareSignRows.reading_cast K 1 _ pos rat
        push_cast at cast
        rw [←cast]
        exact_mod_cast sign K i above ip (by exact_mod_cast within)
      have first:=at_root j active jp (lo.trans (hi.le.trans lasted))
      have last:=at_root (j+1) (by omega) (by omega) (by simpa using lasted)
      push_cast at last
      obtain ⟨t,tn,tu,same⟩:=interpolation (by positivity : 0<(j:ℝ)^4) lo hi.le (lo.trans_lt hi)
      have bend:=pass_chord K jr lo hi.le tn tu same
      have lower:=neg_le_abs (defect (reading K 1) ((j:ℝ)^4) x ((j+1:ℝ)^4) t) |>.trans bend
      dsimp only [defect] at lower
      have ratio : totalPrice/(j:ℝ)^2≤C/Real.sqrt x := by
        apply (div_le_div_iff₀ (sq_pos_of_pos jpos) (Real.sqrt_pos.mpr xp)).mpr
        nlinarith [mul_le_mul_of_nonneg_left four total_pos.le,
          mul_le_mul_of_nonneg_right cost (sq_nonneg (j:ℝ))]
      nlinarith [mul_nonneg (sub_nonneg.mpr tu) first,mul_nonneg tn last]
    · have before : (j:ℝ)≤B := by exact_mod_cast (le_of_not_ge active)
      have sm := pow_le_pow_left₀ (show 0≤(j:ℝ)+1 by positivity)
        (by linarith : (j:ℝ)+1≤B+1) 2
      have here : 3≤C/Real.sqrt x := (le_div_iff₀ (Real.sqrt_pos.mpr xp)).mpr (by
        dsimp [C];nlinarith [total_pos,sr.trans sm])
      linarith
  have exponent := Real.rpow_le_rpow_of_exponent_le x1 (show -(1/2:ℝ)≤e-1/2 by linarith)
  rw [Real.rpow_neg xp.le,←Real.sqrt_eq_rpow] at exponent
  rw [div_eq_mul_inv] at floor
  linarith [mul_le_mul_of_nonneg_left exponent cn.le]

#print axioms PALRH.CubicFourth.rh_of_fourth_signs

private theorem extend_sweep {p N K : ℕ} (pp : 2≤p) (nk : N≤K) {f : ℝ → ℝ} (quiet : Before f)
    {x : ℝ} (inside : x≤(2:ℝ)^N) : sweep N p f x=sweep K p f x := by
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro i _ missing
  have index : N+1 ≤ i := by simpa using missing
  have pp1 : 1≤p := by omega
  have big : 2*2^N≤p^i := by
    rw [←pow_succ']
    exact (Nat.pow_le_pow_left pp _).trans (Nat.pow_le_pow_right (by omega) index)
  have mm : (2:ℝ)*2^N≤((p^i:ℕ):ℝ) := by exact_mod_cast big
  have jr : (1:ℝ)≤((p^i:ℕ):ℝ) := by exact_mod_cast (show 1≤p^i from pow_pos (show 0<p by omega) i)
  have sq : 0<((p^i:ℕ):ℝ)^2 := by positivity
  have far : x/((p^i:ℕ):ℝ)^2≤1/2 := (div_le_iff₀ sq).mpr (by
    nlinarith [mul_nonneg (sub_nonneg.mpr jr) (show 0≤((p^i:ℕ):ℝ) by positivity)])
  rw [shift,quiet _ far,zero_div]

theorem extend_pass {N K : ℕ} (nk : N≤K) {x : ℝ} (xp : 0≤x) (inside : x≤(2:ℝ)^N) :
    reading N 1 x=reading K 1 x := by
  have quiet : Before edge := fun _ hx => edge_before hx
  change sweep N 2 (sweep N 3 edge) x=sweep K 2 (sweep K 3 edge) x
  rw [←extend_sweep (by decide : 2≤2) nk (sweep_before K (by decide : 0<3) quiet) inside]
  apply Finset.sum_congr rfl
  intro i _
  have denom : (1:ℝ)≤((2^i:ℕ):ℝ)^2 := by exact_mod_cast (show 1≤(2^i)^2 from pow_pos (pow_pos (by decide : 0<(2:ℕ)) i) 2)
  rw [shift,shift,extend_sweep (by decide : 2≤3) nk quiet ((div_le_self xp denom).trans inside)]

def fourthValue (j : ℕ) : ℚ :=
  SquareSignRows.qReading (Nat.log 2 (j^4)+1) 1 ((j:ℚ)^4)

/-- A single rational number per root. All sufficiently late fourth powers of a
single pass must be nonnegative, with no externally supplied frame or rate. -/
theorem rh_of_first_pass_fourths (h : ∃ B : ℕ, ∀ j : ℕ, B≤j → 0≤fourthValue j) : RiemannHypothesis := by
  apply rh_of_fourth_signs
  obtain ⟨B,small⟩ := h
  refine ⟨B,?_⟩
  intro N j late jp inside
  let L:=Nat.log 2 (j^4)+1
  have enough : j^4≤2^L := (Nat.lt_pow_succ_log_self (by decide : 1<2) (j^4)).le
  have xr : 0<(j:ℝ)^4 := by positivity
  have xq : 0<(j:ℚ)^4 := by positivity
  have atN := SquareSignRows.reading_cast N 1 ((j:ℚ)^4) xq (by exact_mod_cast inside)
  have atL := SquareSignRows.reading_cast L 1 ((j:ℚ)^4) xq (by exact_mod_cast enough)
  push_cast at atN atL
  have r1 := extend_pass (le_max_left N L) xr.le (by exact_mod_cast inside)
  have r2 := extend_pass (le_max_right N L) xr.le (by exact_mod_cast enough)
  have eq : SquareSignRows.qReading N 1 ((j:ℚ)^4)=fourthValue j := by
    apply Rat.cast_injective (α:=ℝ)
    change ((SquareSignRows.qReading N 1 ((j:ℚ)^4):ℚ):ℝ)=((SquareSignRows.qReading L 1 ((j:ℚ)^4):ℚ):ℝ)
    exact atN.trans (r1.trans (r2.symm.trans atL.symm))
  rw [eq]
  exact small j late

#print axioms PALRH.CubicFourth.rh_of_first_pass_fourths

end PALRH.CubicFourth
