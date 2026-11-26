import PALRH.CubicFourth

open Finset Set
open scoped BigOperators Classical
noncomputable section
namespace PALRH.ClockRoutes
open RectangleBalance SquarePass SquarePassBudget CubicGaps SquareSignRows

def clock (N p : ℕ) := sweep N p edge
def sample (N p n : ℕ) : ℚ := qSweep N p (qEdge N) ((n:ℚ)/2)
def debt (N n : ℕ) : ℚ := max 0 (-max (sample N 2 n) (sample N 3 n))

theorem commute (N p q : ℕ) (f : ℝ → ℝ) (x : ℝ) : sweep N p (sweep N q f) x=sweep N q (sweep N p f) x := by
  simp only [sweep,shift,Finset.sum_div]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  rw [div_div,div_div x, mul_comm (((p^a:ℕ):ℝ)^2),div_div,div_div,mul_comm ((q^b:ℕ):ℝ)]

theorem routes (N : ℕ) {x : ℝ} (head : x≤(2:ℝ)^N) :
    reading N 1 x=clock N 3 x+reading N 1 (x/4)/2 ∧
    reading N 1 x=clock N 2 x+reading N 1 (x/9)/3 := by
  have quiet : Before edge := fun t h => edge_before h
  have a:=on_head (by decide : 2≤2) N (sweep_before N (by decide : 0<3) quiet) head
  have b:=on_head (by decide : 2≤3) N (sweep_before N (by decide : 0<2) quiet) head
  have swap : (sweep N 3 (sweep N 2 edge))=reading N 1 := funext (fun t => commute N 3 2 edge t)
  rw [swap] at b
  change clock N 3 x=reading N 1 x-shift 2 (reading N 1) x at a
  change clock N 2 x=reading N 1 x-shift 3 (reading N 1) x at b
  dsimp only [shift] at a b
  norm_num at a b
  constructor <;> linarith

def SampleBudget : Prop := ∀ e : ℝ, 0<e → e≤1/2 → ∃ C : ℝ, 0≤C ∧ ∀ N n : ℕ,
  0<n → n≤2^(N+1) → (debt N n:ℝ)≤C*(n:ℝ)^(e-1/2)

theorem real_route (budget : SampleBudget) {e : ℝ} (ep : 0<e) (small : e≤1/2) :
    ∃ A : ℝ, 0≤A ∧ ∀ N : ℕ, ∀ x ∈ Set.Ioc (0:ℝ) ((2:ℝ)^N),
      -(A*x^(e-1/2))≤clock N 2 x ∨ -(A*x^(e-1/2))≤clock N 3 x := by
  obtain ⟨C,cn,known⟩:=budget e ep small
  refine ⟨C+4,by linarith,?_⟩
  intro N x hx
  by_cases early : x≤1/2
  · left
    rw [clock,sweep_before N (by decide : 0<2) (fun _ h => edge_before h) x early]
    exact neg_nonpos.mpr (mul_nonneg (by linarith) (Real.rpow_nonneg hx.1.le _))
  let n:=⌊2*x⌋₊
  have lo : (n:ℝ)≤2*x := Nat.floor_le (by linarith [hx.1])
  have hi : 2*x<(n:ℝ)+1 := Nat.lt_floor_add_one (2*x)
  have np : 0<n := (Nat.one_le_floor_iff _).mpr (by linarith)
  have nr : (1:ℝ)≤n := by exact_mod_cast np
  have npos : 0<(n:ℝ) := by positivity
  have span : (n:ℝ)≤(2:ℝ)^(N+1) := by rw [pow_succ];linarith [hx.2]
  have cap : (n:ℚ)/2≤(2:ℚ)^N := by
    have h : (n:ℚ)≤(2:ℚ)^(N+1) := by exact_mod_cast span
    rw [pow_succ] at h;linarith
  have pos : 0<(n:ℚ)/2 := by positivity
  have sc (p : ℕ) (pp : 0<p) : (sample N p n:ℝ)=clock N p ((n:ℝ)/2) := by
    simpa [sample,clock] using single_cast N pp _ pos cap
  have q:=known N n np (by exact_mod_cast span)
  simp only [debt,Rat.cast_max,Rat.cast_neg,Rat.cast_zero,sc 2 (by decide),sc 3 (by decide)] at q
  have v : -max (clock N 2 ((n:ℝ)/2)) (clock N 3 ((n:ℝ)/2)) ≤ C*(n:ℝ)^(e-1/2) :=
    (le_max_right _ _).trans q
  have xsmall : x≤n := by linarith
  have shrink := Real.rpow_le_rpow_of_nonpos hx.1 xsmall (sub_nonpos.mpr small)
  have inv : 1/(n:ℝ)≤(n:ℝ)^(e-1/2) := by
    simpa [Real.rpow_neg_one,one_div] using
      Real.rpow_le_rpow_of_exponent_le nr (show (-1:ℝ)≤e-1/2 by linarith)
  have frac : (x-(n:ℝ)/2)/((n:ℝ)/2)≤1/n := by
    rw [show (x-(n:ℝ)/2)/((n:ℝ)/2)=(2*x-n)/n by ring]
    exact div_le_div_of_nonneg_right (by linarith) npos.le
  have pay (p : ℕ) (rel : Relative (clock N p) 4)
      (ok : -clock N p ((n:ℝ)/2)≤C*(n:ℝ)^(e-1/2)) : -((C+4)*x^(e-1/2))≤clock N p x := by
    have motion:=rel (by positivity : 0<(n:ℝ)/2) (by linarith : (n:ℝ)/2≤x)
    have reverse : - (clock N p x-clock N p ((n:ℝ)/2))≤_ := (neg_le_abs _).trans motion
    nlinarith [mul_le_mul_of_nonneg_left (frac.trans (inv.trans shrink)) (by norm_num : (0:ℝ)≤4),
      mul_le_mul_of_nonneg_left shrink cn]
  rcases le_total (clock N 2 ((n:ℝ)/2)) (clock N 3 ((n:ℝ)/2)) with h|h
  · right
    rw [max_eq_right h] at v
    apply pay 3 _ v
    intro y z yp yz
    have r : Relative (clock N 3) (2/(1-1/(3:ℝ))) := sweep_relative N (by decide : 1<3) (by norm_num) edge_relative
    have step:=r yp yz
    norm_num at step
    nlinarith [div_nonneg (sub_nonneg.mpr yz) yp.le]
  · left
    rw [max_eq_left h] at v
    apply pay 2 _ v
    intro y z yp yz
    have r : Relative (clock N 2) (2/(1-1/(2:ℝ))) := sweep_relative N (by decide : 1<2) (by norm_num) edge_relative
    convert r yp yz using 1; norm_num

theorem rh_of_choices (budget : SampleBudget) : RiemannHypothesis := by
  apply rh_of_first_pass_floors
  intro e ep small
  obtain ⟨A,an,route⟩:=real_route budget ep small
  let r:=1/(4:ℝ)^e
  have rp : 0≤r := by dsimp [r];positivity
  have less : r<1 := (div_lt_one (Real.rpow_pos_of_pos (by norm_num) _)).mpr
    (Real.one_lt_rpow (by norm_num) ep)
  let C:=max 3 (A/(1-r))
  have cn : 0≤C := (by norm_num : (0:ℝ)≤3).trans (le_max_left _ _)
  have room : A+C*r≤C := by
    have h: A/(1-r)≤C := le_max_right _ _
    have v:=(div_le_iff₀ (sub_pos.mpr less)).mp h
    nlinarith
  refine ⟨C,cn,?_⟩
  intro N
  refine ⟨N,le_rfl,?_⟩
  have extend (j : ℕ) : ∀ x : ℝ, 0<x → x≤(2:ℝ)^N → x≤(2:ℝ)^j →
      -(C*x^e)≤Real.sqrt x*reading N 1 x := by
    induction j with
    | zero =>
      intro x xp head low
      rw [pow_zero] at low
      have am : - (reading N 1 x)≤3 := (neg_le_abs _).trans (by simpa using amplitude N 1 x xp)
      have shrink:=Real.rpow_le_rpow_of_exponent_ge xp low small
      rw [←Real.sqrt_eq_rpow] at shrink
      have c3 : 3≤C := le_max_left _ _
      nlinarith [mul_le_mul_of_nonneg_left am (Real.sqrt_nonneg x),
        mul_le_mul_of_nonneg_left shrink cn,mul_le_mul_of_nonneg_right c3 (Real.sqrt_nonneg x)]
    | succ j ih =>
      intro x xp head low
      rw [pow_succ] at low
      obtain ⟨four,nine⟩:=routes N head
      have one_step (p : ℕ) (pp : 2≤p) (v : ℝ)
          (way : reading N 1 x=v+reading N 1 (x/(p:ℝ)^2)/p)
          (earned : -(A*x^(e-1/2))≤v) : -(C*x^e)≤Real.sqrt x*reading N 1 x := by
        have pr : 0<(p:ℝ) := by exact_mod_cast (show 0<p by omega)
        have sq : (4:ℝ)≤(p:ℝ)^2 := by nlinarith [show (2:ℝ)≤p by exact_mod_cast pp]
        have dp:=sq_pos_of_pos pr
        have before : x/(p:ℝ)^2≤(2:ℝ)^j := (div_le_iff₀ dp).mpr (by
          nlinarith [mul_le_mul_of_nonneg_left sq (by positivity : (0:ℝ)≤2^j)])
        have past:=ih _ (div_pos xp dp) ((div_le_self xp.le (by linarith : 1≤(p:ℝ)^2)).trans head) before
        have price : (x/(p:ℝ)^2)^e≤x^e*r := by
          rw [show x^e*r=(x/4)^e by dsimp [r];rw [Real.div_rpow xp.le (by norm_num)];ring]
          exact Real.rpow_le_rpow (div_pos xp dp).le (div_le_div_of_nonneg_left xp.le (by norm_num) sq) ep.le
        have unit : Real.sqrt x*x^(e-1/2)=x^e := by
          rw [Real.sqrt_eq_rpow,←Real.rpow_add xp];congr 1;ring
        rw [Real.sqrt_div xp.le,Real.sqrt_sq pr.le] at past
        have first:=mul_le_mul_of_nonneg_left earned (Real.sqrt_nonneg x)
        rw [show Real.sqrt x*(-(A*x^(e-1/2)))= -(A*x^e) by rw [←unit];ring] at first
        have second : -(C*(x^e*r))≤Real.sqrt x/p*reading N 1 (x/(p:ℝ)^2) :=
          (neg_le_neg (mul_le_mul_of_nonneg_left price cn)).trans past
        rw [way]
        calc
          -(C*x^e) ≤ -(A*x^e) + -(C*(x^e*r)) := by
            nlinarith only [mul_le_mul_of_nonneg_right room (Real.rpow_nonneg xp.le e)]
          _ ≤ _ := add_le_add first second
          _ = _ := by ring
      rcases route N x ⟨xp,head⟩ with two|three
      · exact one_step 3 (by decide) _ (by convert nine using 1; norm_num) two
      · exact one_step 2 (by decide) _ (by convert four using 1; norm_num) three
  intro y hy
  have h:=extend N y hy.1 hy.2 hy.2
  have yn:=Real.sqrt_pos.mpr hy.1
  have form : y^(e-1/2)=y^e/Real.sqrt y := by rw [Real.rpow_sub hy.1,Real.sqrt_eq_rpow]
  rw [form,←mul_div_assoc,←neg_div]
  exact (div_le_iff₀ yn).mpr (by linarith)

#print axioms PALRH.ClockRoutes.routes
#print axioms PALRH.ClockRoutes.real_route
#print axioms PALRH.ClockRoutes.rh_of_choices

/-- Each half-row may use its own clock. A failed direction incurs no cost when the
other direction pays. Both measurements in this test are finite rational sums. -/
def JointPowers : Prop := ∀ q : ℕ, 0<q → ∃ A : ℕ, 0<A ∧ ∀ N n : ℕ, 0<n → n≤2^(N+1) →
    (n:ℚ)^q*(debt N n)^(2*q)≤(A:ℚ)*n

theorem rh_of_joint_powers (h : JointPowers) : RiemannHypothesis := by
  apply rh_of_choices
  intro e ep _
  obtain ⟨r,hr⟩:=exists_nat_one_div_lt ep
  let q:=r+1
  have qp : 0<q := by dsimp [q];omega
  have qr : 0<(q:ℝ) := by exact_mod_cast qp
  have room : 1≤e*(2*q:ℕ) := by
    have small : 1/(q:ℝ)<e := by simpa [q] using hr
    have a:=(div_lt_iff₀ qr).mp small
    push_cast;nlinarith
  obtain ⟨A,ap,known⟩:=h q qp
  refine ⟨A,by positivity,?_⟩
  intro N n np head
  have nr : 0<(n:ℝ) := by exact_mod_cast np
  have nu : 1≤(n:ℝ) := by exact_mod_cast np
  have au : 1≤(A:ℝ) := by exact_mod_cast ap
  have given : (n:ℝ)^q*(debt N n:ℝ)^(2*q)≤(A:ℝ)*n := by exact_mod_cast known N n np head
  have amp : (A:ℝ)≤(A:ℝ)^(2*q) := by simpa using pow_le_pow_right₀ au (show 1≤2*q by omega)
  have pow : (n:ℝ)≤(n:ℝ)^(e*(2*q:ℕ)) := by simpa using Real.rpow_le_rpow_of_exponent_le nu room
  have bound:=given.trans (mul_le_mul amp pow nr.le (by positivity))
  have id : (n:ℝ)^q*((A:ℝ)*(n:ℝ)^(e-1/2))^(2*q)=(A:ℝ)^(2*q)*(n:ℝ)^(e*(2*q:ℕ)) := by
    rw [mul_comm ((n:ℝ)^q),mul_pow,mul_assoc,←Real.rpow_natCast ((n:ℝ)^(e-1/2)),←Real.rpow_mul nr.le,
      ←Real.rpow_natCast (n:ℝ) q,←Real.rpow_add nr]
    congr 2;push_cast;ring
  rw [←id] at bound
  have cmp:=le_of_mul_le_mul_left bound (pow_pos nr q)
  by_contra! wrong
  exact (not_lt_of_ge cmp) (pow_lt_pow_left₀ wrong (by positivity) (show 2*q≠0 by omega))

#print axioms PALRH.ClockRoutes.rh_of_joint_powers

/-- At a record of either orientation, the two individual readings are forced to pay together
at the exact same side. The earlier comparison is made after removing the prescribed power. -/
theorem same_record (N : ℕ) {x l : ℝ} (xp : 0<x) (head : x≤(2:ℝ)^N) (orientation : ℝ)
    (record : ∀ p ∈ ({2,3}:Finset ℕ),
      (orientation*Real.sqrt (x/(p:ℝ)^2)*reading N 1 (x/(p:ℝ)^2))/(x/(p:ℝ)^2)^l≤
      (orientation*Real.sqrt x*reading N 1 x)/x^l) :
    (1-1/(4:ℝ)^l)*(orientation*Real.sqrt x*reading N 1 x)≤orientation*Real.sqrt x*clock N 3 x ∧
    (1-1/(9:ℝ)^l)*(orientation*Real.sqrt x*reading N 1 x)≤orientation*Real.sqrt x*clock N 2 x := by
  obtain ⟨four,nine⟩:=routes N head
  have one (p : ℕ) (pp : 0<p) (site : p∈({2,3}:Finset ℕ)) (v : ℝ)
      (eq : reading N 1 x=v+reading N 1 (x/(p:ℝ)^2)/p) :
      (1-1/((p:ℝ)^2)^l)*(orientation*Real.sqrt x*reading N 1 x)≤orientation*Real.sqrt x*v := by
    have pr : 0<(p:ℝ) := by exact_mod_cast pp
    have d:=sq_pos_of_pos pr
    have a:=record p site
    have z:=Real.rpow_pos_of_pos xp l
    have r:=Real.rpow_pos_of_pos d l
    rw [Real.sqrt_div xp.le,Real.sqrt_sq pr.le,Real.div_rpow xp.le d.le] at a
    have relative : orientation*(Real.sqrt x/p)*reading N 1 (x/(p:ℝ)^2)≤
        (orientation*Real.sqrt x*reading N 1 x)/((p:ℝ)^2)^l := by
      apply (le_div_iff₀ r).mpr
      have h:=(div_le_div_iff₀ (div_pos z r) z).mp a
      let u:=orientation*(Real.sqrt x/p)*reading N 1 (x/(p:ℝ)^2)
      let f:=orientation*Real.sqrt x*reading N 1 x
      change u*x^l≤f*(x^l/((p:ℝ)^2)^l) at h
      have hh : u*x^l≤f*x^l/((p:ℝ)^2)^l := h.trans_eq (by ring)
      have q:=(le_div_iff₀ r).mp hh
      change u*((p:ℝ)^2)^l≤f
      apply le_of_mul_le_mul_right (a:=x^l) _ z
      calc
        _ = (u*x^l)*((p:ℝ)^2)^l := by ring
        _ ≤ _ := q
    have back : orientation*Real.sqrt x*reading N 1 x =
        orientation*Real.sqrt x*v+orientation*(Real.sqrt x/p)*reading N 1 (x/(p:ℝ)^2) := by rw [eq];ring
    rw [show (1-1/((p:ℝ)^2)^l)*(orientation*Real.sqrt x*reading N 1 x)=
      orientation*Real.sqrt x*reading N 1 x-(orientation*Real.sqrt x*reading N 1 x)/((p:ℝ)^2)^l by ring]
    linarith
  constructor
  · convert one 2 (by decide) (by simp) (clock N 3 x) (by convert four using 1;norm_num) using 1;norm_num
  · convert one 3 (by decide) (by simp) (clock N 2 x) (by convert nine using 1;norm_num) using 1;norm_num

#print axioms PALRH.ClockRoutes.same_record

end PALRH.ClockRoutes
