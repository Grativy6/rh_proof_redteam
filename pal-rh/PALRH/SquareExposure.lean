import PALRH.TrailingRows

open Finset
open scoped BigOperators Classical

noncomputable section
namespace PALRH.SquareExposure
open RunningMass TaperedNewton

def root (p : ℕ × ℕ) : ℕ := 2^p.1 * 3^p.2

def pairs (R : ℕ) := range (R+1) ×ˢ range (R+1)

def hits (p : ℕ × ℕ) (a b : ℕ) :=
  (Ioc (a/(root p)^2) (b/(root p)^2)).filter (fun d => d.Coprime 6)

private theorem root_pos (p : ℕ × ℕ) : 0<root p := by unfold root; positivity

private theorem bounds {p : ℕ × ℕ} {d a b : ℕ} (hd : d ∈ hits p a b) :
    a<(root p)^2*d ∧ (root p)^2*d≤b ∧ 0<d ∧ d.Coprime 6 := by
  obtain ⟨h,cop⟩:=Finset.mem_filter.mp hd
  obtain ⟨lo,hi⟩:=Finset.mem_Ioc.mp h
  have rp:=pow_pos (root_pos p) 2
  exact ⟨by simpa [Nat.mul_comm] using (Nat.div_lt_iff_lt_mul rp).mp lo,
    by simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le rp).mp hi,(Nat.zero_le _).trans_lt lo,cop⟩

private theorem factor_read (p : ℕ × ℕ) {d : ℕ} (dp : 0<d) (cop : d.Coprime 6) :
    ((root p)^2*d).factorization 2=2*p.1 ∧ ((root p)^2*d).factorization 3=2*p.2 := by
  have two : ¬2 ∣ d := Nat.prime_two.coprime_iff_not_dvd.mp
    (cop.of_dvd_right (by decide : 2∣6)).symm
  have three : ¬3 ∣ d := Nat.prime_three.coprime_iff_not_dvd.mp
    (cop.of_dvd_right (by decide : 3∣6)).symm
  have rp := (pow_pos (root_pos p) 2).ne'
  have a : (2:ℕ)^p.1 ≠ 0 := by positivity
  have b : (3:ℕ)^p.2 ≠ 0 := by positivity
  simp only [Nat.factorization_mul rp dp.ne',Nat.factorization_pow (root p) 2]
  unfold root
  simp [
    Nat.factorization_mul a b,Nat.prime_two.factorization_pow,Nat.prime_three.factorization_pow,
    Nat.factorization_eq_zero_of_not_dvd two,Nat.factorization_eq_zero_of_not_dvd three,
    two_mul]

private theorem same_label {p q : ℕ × ℕ} {d e a b : ℕ} (hd : d ∈ hits p a b)
    (he : e ∈ hits q a b) (eq : (root p)^2*d=(root q)^2*e) : p=q := by
  obtain ⟨_,_,dp,dc⟩:=bounds hd
  obtain ⟨_,_,ep,ec⟩:=bounds he
  obtain ⟨p2,p3⟩:=factor_read p dp dc
  obtain ⟨q2,q3⟩:=factor_read q ep ec
  rw [eq] at p2 p3
  exact Prod.ext (by omega) (by omega)

private theorem equal_multiples {a b L x y : ℕ} (xlo : a<x) (xhi : x≤b)
    (ylo : a<y) (yhi : y≤b) (width : b-a<L) (dx : L∣x) (dy : L∣y) : x=y := by
  rcases le_total x y with before|before
  · have z:=Nat.eq_zero_of_dvd_of_lt (Nat.dvd_sub dy dx) (show y-x<L by omega)
    omega
  · have z:=Nat.eq_zero_of_dvd_of_lt (Nat.dvd_sub dx dy) (show x-y<L by omega)
    omega

private theorem bucket_ordered {s a b : ℕ} (sp : 0<s) (short : b-a≤2^(6*s))
    {p q : ℕ × ℕ} (large_p : 2^(4*s)<root p) (large_q : 2^(4*s)<root q)
    (same : p.1/s=q.1/s) (order : p.1≤q.1) {d e : ℕ}
    (hd : d ∈ hits p a b) (he : e ∈ hits q a b) : p=q := by
  have partp:=Nat.mod_add_div p.1 s
  have partq:=Nat.mod_add_div q.1 s
  rw [←same] at partq
  have tail:=Nat.mod_lt q.1 sp
  have gap : q.1-p.1 ≤ s := by omega
  let g:=2^p.1*3^(min p.2 q.2)
  have divp : g∣root p := Nat.mul_dvd_mul (dvd_refl _) (pow_dvd_pow _ (min_le_left _ _))
  have divq : g∣root q := Nat.mul_dvd_mul (pow_dvd_pow _ order) (pow_dvd_pow _ (min_le_right _ _))
  have high : 2^(3*s)<g := by
    by_cases second : p.2≤q.2
    · have lo : (2:ℕ)^(3*s)≤2^(4*s) := Nat.pow_le_pow_right (by decide) (by omega)
      simpa [g,root,min_eq_left second] using lo.trans_lt large_p
    · have eq : root q = 2^(q.1-p.1)*g := by
        dsimp [g,root];rw [min_eq_right (by omega : q.2≤p.2),←Nat.mul_assoc,←pow_add,Nat.sub_add_cancel order]
      by_contra! neg
      have low:=Nat.mul_le_mul (Nat.pow_le_pow_right (by decide : 0<2) gap) neg
      rw [←pow_add,show s+3*s=4*s by omega,←eq] at low
      omega
  have square : 2^(6*s)<g^2 := by
    have lift:=Nat.pow_lt_pow_left high (by decide : 2≠0)
    simpa only [←pow_mul,show 3*s*2=6*s by omega] using lift
  obtain ⟨lo,hi,_⟩:=bounds hd
  obtain ⟨lo',hi',_⟩:=bounds he
  apply same_label hd he
  exact equal_multiples lo hi lo' hi' (short.trans_lt square)
    ((pow_dvd_pow_of_dvd divp 2).trans (dvd_mul_right _ _))
    ((pow_dvd_pow_of_dvd divq 2).trans (dvd_mul_right _ _))

def giants (R s a b : ℕ) := (pairs R).filter fun p => 2^(4*s)<root p ∧ (hits p a b).Nonempty

/-- Only seven bins of 2-adic exponents can contribute a large occupied row. -/
theorem giant_count {R s a b : ℕ} (sp : 0<s) (short : b-a≤2^(6*s))
    (cap : b≤(2^(6*s))^2) : (giants R s a b).card≤7 := by
  let bucket := fun p : ℕ × ℕ => p.1/s
  have belong (p : ℕ × ℕ) (hp : p∈giants R s a b) : bucket p∈range 7 := by
    obtain ⟨_,_,⟨d,hd⟩⟩:=mem_filter.mp hp
    obtain ⟨_,hi,dp,_⟩:=bounds hd
    have root_sq : (root p)^2≤(2^(6*s))^2 :=
      (Nat.le_mul_of_pos_right _ dp).trans (hi.trans cap)
    have vcap : root p≤2^(6*s) := by
      by_contra! h
      exact (Nat.not_lt_of_ge root_sq) (Nat.pow_lt_pow_left h (by decide : 2≠0))
    have power : 2^p.1≤root p := Nat.le_mul_of_pos_right _ (by positivity : 0<(3:ℕ)^p.2)
    have exp: p.1≤6*s := (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp (power.trans vcap)
    apply mem_range.mpr
    apply (Nat.div_lt_iff_lt_mul sp).mpr
    omega
  have inj : Set.InjOn bucket ↑(giants R s a b) := by
    intro p hp q hq same
    obtain ⟨_,big,⟨d,hd⟩⟩:=mem_filter.mp hp
    obtain ⟨_,big',⟨e,he⟩⟩:=mem_filter.mp hq
    rcases le_total p.1 q.1 with before|before
    · exact bucket_ordered sp short big big' same before hd he
    · exact (bucket_ordered sp short big' big same.symm before he hd).symm
  simpa using (Finset.card_le_card_of_injOn (t:=range 7) bucket belong inj)

private theorem local_sum (p : ℕ × ℕ) {a b : ℕ} (ab : a≤b) :
    (∑ d ∈ Icc 1 (b/(root p)^2), (marks d:ℝ))-
      (∑ d ∈ Icc 1 (a/(root p)^2), (marks d:ℝ))=∑ d ∈ hits p a b, (marks d:ℝ) := by
  let lo:=a/(root p)^2
  let hi:=b/(root p)^2
  have order : lo≤hi := Nat.div_le_div_right ab
  have non : 0≤lo := Nat.zero_le _
  have union : Icc 1 hi=Icc 1 lo ∪ Ioc lo hi := by
    ext d;simp only [mem_Icc,mem_union,mem_Ioc];omega
  have dis : Disjoint (Icc 1 lo) (Ioc lo hi) := Finset.disjoint_left.mpr (fun _ x y =>
    (not_lt_of_ge (mem_Icc.mp x).2) (mem_Ioc.mp y).1)
  change (∑ d ∈ Icc 1 hi, (marks d:ℝ))-(∑ d ∈ Icc 1 lo, (marks d:ℝ))=_
  rw [union,Finset.sum_union dis,add_sub_cancel_left]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro d hd out
  have no : ¬d.Coprime 6 := fun yes => out (mem_filter.mpr ⟨hd,yes⟩)
  have eq : marks d=0 := by
    change (ArithmeticFunction.moebius d:ℚ)*(if d.Coprime 6 then 1 else 0)=0
    simp [no]
  simp [eq]

private theorem mass_interval (R : ℕ) {a b : ℕ} (ab : a≤b) :
    |mass R b-mass R a| ≤ ∑ p ∈ pairs R, (root p:ℝ)*(hits p a b).card := by
  have eq (n : ℕ) : mass R n=∑ p ∈ pairs R,
      (root p:ℝ)*∑ d ∈ Icc 1 (n/(root p)^2), (marks d:ℝ) := by
    rw [pairs,Finset.sum_product];rfl
  rw [eq b,eq a,←Finset.sum_sub_distrib]
  simp_rw [←mul_sub,local_sum _ ab]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro p _
  rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg _)]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _d ∈ hits p a b, (1:ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      have rough := (mem_filter.mp hd).2
      have eqm : marks d=(ArithmeticFunction.moebius d:ℚ) := by
        change (ArithmeticFunction.moebius d:ℚ)*(if d.Coprime 6 then 1 else 0)=_
        rw [if_pos rough,mul_one]
      rw [eqm]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n:=d)
    _ = _ := by simp

private theorem cost_count (p : ℕ × ℕ) {a b : ℕ} (ab : a≤b) :
    (root p:ℝ)*(hits p a b).card ≤ ((b-a:ℕ):ℝ)/(root p)+(root p:ℝ) := by
  let v:=root p
  let D:=v^2
  have dp : 0<D := pow_pos (root_pos p) 2
  have ord : a/D≤b/D := Nat.div_le_div_right ab
  have hc : (hits p a b).card ≤ b/D-a/D :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Nat.card_Ioc _ _)
  have low:=Nat.lt_mul_div_succ a dp
  rw [Nat.mul_add,Nat.mul_one,Nat.mul_comm D (a/D)] at low
  have high:=Nat.div_mul_le_self b D
  have weight:=Nat.mul_le_mul_right D hc
  have cancel : (b/D-a/D)*D+(a/D)*D=(b/D)*D := by rw [←Nat.add_mul,Nat.sub_add_cancel ord]
  have total : (hits p a b).card*D ≤ (b-a)+D := by omega
  have vr : 0<(v:ℝ) := by exact_mod_cast root_pos p
  have cast : ((hits p a b).card:ℝ)*(v:ℝ)^2 ≤ ((b-a:ℕ):ℝ)+(v:ℝ)^2 := by exact_mod_cast total
  change (v:ℝ)*(hits p a b).card ≤ ((b-a:ℕ):ℝ)/v+v
  apply le_of_mul_le_mul_right (a:=(v:ℝ)) _ vr
  rw [add_mul,div_mul_cancel₀ _ vr.ne']
  nlinarith only [cast]

private theorem reciprocal_total (R : ℕ) :
    (∑ p ∈ pairs R, 1/Real.sqrt (root p:ℝ)) ≤ 12 := by
  have bound (p : ℕ × ℕ) : 1/Real.sqrt (root p:ℝ) ≤ (3/4:ℝ)^p.1*(2/3:ℝ)^p.2 := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    rw [div_pow,one_pow,Real.sq_sqrt (Nat.cast_nonneg _),mul_pow,
      show ((3/4:ℝ)^p.1)^2=((3/4)^2)^p.1 by rw [←pow_mul,←pow_mul,Nat.mul_comm],
      show ((2/3:ℝ)^p.2)^2=((2/3)^2)^p.2 by rw [←pow_mul,←pow_mul,Nat.mul_comm]]
    have inv : 1/(root p:ℝ)=(1/2:ℝ)^p.1*(1/3:ℝ)^p.2 := by
      simp [root,one_div,mul_inv_rev,mul_comm]
    rw [inv]
    exact mul_le_mul (pow_le_pow_left₀ (by norm_num) (by norm_num : (1/2:ℝ)≤(3/4)^2) _)
      (pow_le_pow_left₀ (by norm_num) (by norm_num : (1/3:ℝ)≤(2/3)^2) _) (by positivity) (by positivity)
  apply (Finset.sum_le_sum fun p _ => bound p).trans
  rw [pairs,Finset.sum_product]
  simp only [←Finset.mul_sum,←Finset.sum_mul]
  have a:=SquarePassBudget.finite_geometric (r:=(3/4:ℝ)) (by norm_num) (by norm_num) R
  have b:=SquarePassBudget.finite_geometric (r:=(2/3:ℝ)) (by norm_num) (by norm_num) R
  calc
    _ ≤ (1/(1-3/4:ℝ))*(1/(1-2/3:ℝ)) := mul_le_mul a b
      (Finset.sum_nonneg (fun _ _ => by positivity)) (by norm_num)
    _ = (12:ℝ) := by norm_num

/-- Uniform unsigned capacity of all rough labels in a square-root sized interval. -/
theorem offered_bound {R s a b : ℕ} (sp : 0<s) (ab : a≤b) (short : b-a≤2^(6*s))
    (cap : b≤(2^(6*s))^2) :
    (∑ p ∈ pairs R, (root p:ℝ)*(hits p a b).card) ≤ 31*((2^(6*s):ℕ):ℝ) := by
  let Y : ℕ:=2^(6*s)
  let G:=giants R s a b
  have yn : 0≤(Y:ℝ) := Nat.cast_nonneg _
  have each (p : ℕ × ℕ) (hp : p∈pairs R) :
      (root p:ℝ)*(hits p a b).card ≤ 2*(Y:ℝ)*(1/Real.sqrt (root p:ℝ)) +
        (if p∈G then (Y:ℝ) else 0) := by
    have vr : 0<(root p:ℝ) := by exact_mod_cast root_pos p
    have rootp:=Real.sqrt_pos_of_pos vr
    have extra : 0 ≤ (if p∈G then (Y:ℝ) else 0) := by split <;> positivity
    by_cases small : root p≤2^(4*s)
    · have cube : (root p)^3≤Y^2 := by
        have lim:=Nat.pow_le_pow_left small 3
        simpa only [Y,←pow_mul,show 4*s*3=6*s*2 by omega] using lim
      have size : (root p:ℝ)*Real.sqrt (root p:ℝ) ≤ (Y:ℝ) := by
        apply (sq_le_sq₀ (by positivity) yn).mp
        rw [mul_pow,Real.sq_sqrt vr.le]
        have val : (root p:ℝ)^3≤(Y:ℝ)^2 := by exact_mod_cast cube
        nlinarith only [val]
      have small2 := (le_div_iff₀ rootp).mpr size
      have one : (1:ℝ)≤root p := by exact_mod_cast root_pos p
      have sqrtle : Real.sqrt (root p:ℝ)≤root p := Real.sqrt_le_iff.mpr
        ⟨vr.le,by nlinarith only [one,mul_nonneg (sub_nonneg.mpr one) vr.le]⟩
      have small1 : ((b-a:ℕ):ℝ)/(root p:ℝ) ≤ (Y:ℝ)/Real.sqrt (root p:ℝ) := by
        apply (div_le_div_of_nonneg_right (by exact_mod_cast short : ((b-a:ℕ):ℝ)≤Y) vr.le).trans
        exact div_le_div_of_nonneg_left yn rootp sqrtle
      apply (cost_count p ab).trans
      rw [mul_one_div]
      linarith only [small1,small2,extra,show 2*(Y:ℝ)/Real.sqrt (root p:ℝ)=
        2*((Y:ℝ)/Real.sqrt (root p:ℝ)) by ring]
    · by_cases exists_hit : (hits p a b).Nonempty
      · have member : p∈G := mem_filter.mpr ⟨hp,by omega,exists_hit⟩
        rw [if_pos member]
        obtain ⟨d,hd⟩:=exists_hit
        obtain ⟨_,hi,dp,_⟩:=bounds hd
        have lim : (root p)^2≤Y^2 := (Nat.le_mul_of_pos_right _ dp).trans (hi.trans cap)
        have vcap : root p≤Y := by
          by_contra! no
          exact (Nat.not_lt_of_ge lim) (Nat.pow_lt_pow_left no (by decide : 2≠0))
        have more : Y<(root p)^2 := by
          have base : 2^(3*s)<root p := (Nat.pow_le_pow_right (by decide : 0<2)
            (show 3*s≤4*s by omega)).trans_lt (lt_of_not_ge small)
          simpa only [Y,←pow_mul,show 3*s*2=6*s by omega] using Nat.pow_lt_pow_left base (by decide : 2≠0)
        have just : (hits p a b).card≤1 := by
          apply Finset.card_le_one.mpr
          intro f hf g hg
          obtain ⟨l,u,_⟩:=bounds hf
          obtain ⟨l',u',_⟩:=bounds hg
          exact Nat.eq_of_mul_eq_mul_left (pow_pos (root_pos p) 2)
            (equal_multiples l u l' u' (short.trans_lt more) (dvd_mul_right _ _) (dvd_mul_right _ _))
        have inc := mul_le_mul_of_nonneg_left (by exact_mod_cast just : ((hits p a b).card:ℝ)≤1) vr.le
        apply (inc.trans (by simpa only [mul_one] using (show (root p:ℝ)≤Y by exact_mod_cast vcap))).trans
        linarith only [show 0≤2*(Y:ℝ)*(1/Real.sqrt (root p:ℝ)) by positivity]
      · rw [Finset.not_nonempty_iff_eq_empty.mp exists_hit]
        simp only [card_empty,Nat.cast_zero,mul_zero]
        positivity
  have s1:=Finset.sum_le_sum each
  have counts : (∑ p ∈ pairs R, if p∈G then (Y:ℝ) else 0)= (G.card:ℝ)*Y := by
    rw [←Finset.sum_filter]
    have same : (pairs R).filter (fun p => p∈G)=G := by ext p;simp [G,giants]
    rw [same,Finset.sum_const,nsmul_eq_mul]
  rw [Finset.sum_add_distrib,←Finset.mul_sum,counts] at s1
  have gr : (G.card:ℝ)≤7 := by exact_mod_cast (giant_count (R:=R) sp short cap)
  have sg:=mul_le_mul_of_nonneg_left (reciprocal_total R) (show 0≤2*(Y:ℝ) by positivity)
  change _ ≤ 31*(Y:ℝ)
  linarith only [s1,sg,mul_le_mul_of_nonneg_right gr yn]

/-- A square-sized jump is uniformly bounded on every interval between consecutive squares. -/
theorem square_variation {j n : ℕ} (jp : 0<j) (first : j^2≤n) (after : n<(j+1)^2) :
    |running n-running (j^2)|≤(31*256:ℝ)*j := by
  let u:=2*(j+1)
  let l:=Nat.log 2 u
  let s:=l/6+1
  let Y:ℕ:=2^(6*s)
  have sp : 0<s := by dsimp [s];omega
  have up : 0<u := by dsimp [u];positivity
  have eu : l+1≤6*s := by dsimp [s];omega
  have el : 6*s≤l+6 := by dsimp [s];omega
  have above : u≤Y := (Nat.lt_pow_succ_log_self (by decide : 1<2) u).le.trans
    (Nat.pow_le_pow_right (by decide : 0<2) eu)
  have below : Y≤64*u := by
    apply (Nat.pow_le_pow_right (by decide : 0<2) el).trans
    rw [pow_add]
    have z:=Nat.pow_log_le_self 2 up.ne'
    dsimp only [l]
    norm_num
    omega
  have jY : j+1≤Y := (by dsimp only [u] at above;omega)
  have cap : n≤Y^2 := after.le.trans (Nat.pow_le_pow_left jY 2)
  have width : n-j^2≤Y := by
    have w : n≤j^2+2*j := by nlinarith only [after]
    dsimp only [u] at above
    omega
  let R:=Nat.log 2 n+1
  have plenty : n≤2^R := (Nat.lt_pow_succ_log_self (by decide : 1<2) n).le
  have dif:=(mass_interval R first).trans (offered_bound (R:=R) sp first width cap)
  rw [canonical plenty,canonical (first.trans plenty)] at dif
  have cheap : Y≤256*j := by dsimp only [u] at below;omega
  have c' : (Y:ℝ)≤256*(j:ℝ) := by exact_mod_cast cheap
  change |running n-running (j^2)|≤31*(Y:ℝ) at dif
  exact dif.trans (by linarith only [c'])

/-- Any one ordinary head in each square interval can be selected after looking at that interval. -/
theorem rh_of_square_contacts {C : ℝ} (cn : 0≤C)
    (heads : ∀ j : ℕ, 0<j → ∃ k : ℕ, j^2≤k ∧ k<(j+1)^2 ∧ running k≤C*j) :
    RiemannHypothesis := by
  apply TerminalWindows.rh_of_running_upper (C:=C+2*(31*256)) (by positivity)
  intro n
  by_cases nz : n=0
  · simp [nz,running,mass]
  let j:=n.sqrt
  have jp : 0<j := Nat.sqrt_pos.mpr (Nat.pos_of_ne_zero nz)
  have first : j^2≤n := by simpa [j,pow_two] using Nat.sqrt_le n
  have after : n<(j+1)^2 := Nat.lt_succ_sqrt' n
  obtain ⟨k,fk,ak,price⟩:=heads j jp
  have up:=(abs_le.mp (square_variation jp first after)).2
  have down:=(abs_le.mp (square_variation jp fk ak)).1
  have jroot : (j:ℝ)≤Real.sqrt (n:ℝ) :=
    (Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)).mpr (by exact_mod_cast first)
  apply le_trans _ (mul_le_mul_of_nonneg_left jroot (show 0≤C+2*(31*256) by positivity))
  linarith only [up,down,price]

theorem rh_of_square_heads {C : ℝ} (cn : 0≤C)
    (heads : ∀ j : ℕ, 0<j → running (j^2)≤C*j) : RiemannHypothesis := by
  apply rh_of_square_contacts cn
  intro j jp
  exact ⟨j^2,le_rfl,Nat.pow_lt_pow_left (by omega) (by decide : 2≠0),heads j jp⟩

#print axioms PALRH.SquareExposure.giant_count
#print axioms PALRH.SquareExposure.offered_bound
#print axioms PALRH.SquareExposure.square_variation
#print axioms PALRH.SquareExposure.rh_of_square_contacts
#print axioms PALRH.SquareExposure.rh_of_square_heads
end PALRH.SquareExposure
