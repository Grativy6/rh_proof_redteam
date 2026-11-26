import PALRH.OneHead

open Finset Filter Set
open scoped BigOperators Classical
noncomputable section
namespace PALRH.OneHeadSamples
open SquarePass SquarePassBudget CubicFourth OneHead

private theorem coordinate {a z b : ℝ} (ap : 0<a) (az : a≤z) (zb : z≤b) (ab : a<b) :
    let t:=(1/a-1/z)/(1/a-1/b)
    0≤t ∧ t≤1 ∧ 1/z=(1-t)/a+t/b := by
  dsimp only
  have den : 0<1/a-1/b := sub_pos.mpr (one_div_lt_one_div_of_lt ap ab)
  have zp:=ap.trans_le az
  have h1:=one_div_le_one_div_of_le ap az
  have h2:=one_div_le_one_div_of_le zp zb
  have used:=div_mul_cancel₀ (1/a-1/z) den.ne'
  refine ⟨div_nonneg (by linarith) den.le,(div_le_one den).mpr (by linarith),?_⟩
  linear_combination used

/-- Restrict a known reciprocal-coordinate chord to any shorter interval with the same left end. -/
private theorem short_chord (N : ℕ) {r z b t : ℝ} (unit : 1≤r)
    (lo : r^4≤z) (hi : z≤b) (stop : b≤(r+1)^4)
    (tn : 0≤t) (tu : t≤1) (same : 1/z=(1-t)/r^4+t/b) :
    |defect (reading N 1) (r^4) z b t|≤2*totalPrice/r^2 := by
  let a:=r^4
  let endpt:=(r+1)^4
  let f:=reading N 1
  let h:=fun y : ℝ => (1/a-1/y)/(1/a-1/endpt)
  let L:=fun y : ℝ => (1-h y)*f a+h y*f endpt
  have rp : 0<r := by linarith
  have ap : 0<a := by dsimp [a];positivity
  have ab : a<endpt := pow_lt_pow_left₀ (by linarith : r<r+1) rp.le (by decide)
  have fit (y : ℝ) (yl : a≤y) (yr : y≤endpt) : |f y-L y|≤totalPrice/r^2 := by
    obtain ⟨low,upp,rep⟩:=coordinate ap yl yr ab
    exact pass_chord N unit yl yr low upp rep
  have la : L a=f a := by simp [L,h]
  have hm : h z=(1-t)*h a+t*h b := by
    dsimp [h]
    change 1/z=(1-t)/a+t/b at same
    rw [same];ring
  have lm : L z=(1-t)*L a+t*L b := by dsimp only [L];rw [hm];ring
  have eq : defect f a z b t=(f z-L z)-t*(f b-L b) := by
    dsimp only [defect]
    rw [lm,la];ring
  have one := fit z lo (hi.trans stop)
  have two := fit b (lo.trans hi) stop
  have small:=mul_le_mul_of_nonneg_right tu (abs_nonneg (f b-L b))
  change |defect f a z b t|≤_
  rw [eq]
  calc
    _ ≤ |f z-L z|+|t*(f b-L b)| := abs_sub _ _
    _ ≤ totalPrice/r^2+totalPrice/r^2 := by
      rw [abs_mul,abs_of_nonneg tn]
      exact add_le_add one ((by simpa using small : t*|f b-L b| ≤ |f b-L b|).trans two)
    _ = _ := by ring

private theorem scaled_chord (N : ℕ) {c j x t : ℝ} (c1 : 1≤c) (jp : 1≤j)
    (lo : j^4≤x) (hi : x≤(j+1)^4) (tn : 0≤t) (tu : t≤1)
    (same : 1/x=(1-t)/j^4+t/(j+1)^4) :
    |defect (fun y => reading N 1 (y/c)/c) (j^4) x ((j+1)^4) t| ≤
      (2*totalPrice+6)/(j^2*Real.sqrt c) := by
  have cp : 0<c := by linarith
  have jr : 0<j := by linarith
  have xp : 0<x := (pow_pos jr 4).trans_le lo
  have sp:=Real.sqrt_pos.mpr cp
  let v:=Real.sqrt (Real.sqrt c)
  have vp : 0<v := Real.sqrt_pos.mpr sp
  have vu : 1≤v := Real.one_le_sqrt.mpr (Real.one_le_sqrt.mpr c1)
  have sq : v^2=Real.sqrt c := Real.sq_sqrt sp.le
  have four : v^4=c := by rw [show (4:ℕ)=2*2 by decide,pow_mul,sq,Real.sq_sqrt cp.le]
  have root : (j/v)^4=j^4/c := by rw [div_pow,four]
  have eq : defect (fun y => reading N 1 (y/c)/c) (j^4) x ((j+1)^4) t=
      defect (reading N 1) (j^4/c) (x/c) ((j+1)^4/c) t / c := by dsimp [defect];ring
  rw [eq,abs_div,abs_of_pos cp]
  by_cases inside : c≤j^4
  · have vj : v≤j := by
      by_contra! lt
      have pow:=pow_lt_pow_left₀ lt jr.le (by decide : 4≠0)
      linarith only [pow,four,inside]
    have r1 : 1≤j/v := (one_le_div vp).mpr vj
    have stop : (j+1)^4/c≤(j/v+1)^4 := by
      rw [←four,←div_pow]
      apply pow_le_pow_left₀ (by positivity)
      rw [add_div]
      linarith [(div_le_one vp).mpr vu]
    have rep : 1/(x/c)=(1-t)/(j^4/c)+t/((j+1)^4/c) := by
      have shift_rule (u d : ℝ) : u/(d/c)=c*(u/d) := by
        simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
        ring
      simp only [shift_rule,←mul_add,same]
    have raw := short_chord N r1 (root.trans_le (div_le_div_of_nonneg_right lo cp.le))
      (div_le_div_of_nonneg_right hi cp.le) stop tn tu (by simpa only [root] using rep)
    rw [root] at raw
    apply (div_le_div_of_nonneg_right raw cp.le).trans
    have pull : 2*totalPrice/(j/v)^2/c = 2*totalPrice/(j^2*Real.sqrt c) := by
      rw [div_pow,sq]
      field_simp [jr.ne',sp.ne',cp.ne']
      rw [Real.sq_sqrt cp.le]
    rw [pull]
    apply div_le_div_of_nonneg_right (by linarith) (by positivity)
  · have sc : j^2≤Real.sqrt c := (Real.le_sqrt (sq_nonneg j) cp.le).mpr (by nlinarith only [le_of_not_ge inside])
    have amp (y : ℝ) (yp : 0<y) : |reading N 1 (y/c)|≤3 := by simpa using amplitude N 1 _ (div_pos yp cp)
    have a:=abs_le.mp (amp (j^4) (pow_pos jr _))
    have b:=abs_le.mp (amp ((j+1)^4) (by positivity))
    have u:=abs_le.mp (amp x xp)
    have raw : |defect (reading N 1) (j^4/c) (x/c) ((j+1)^4/c) t|≤6 := by
      unfold defect
      rw [abs_le]
      constructor <;> nlinarith [mul_le_mul_of_nonneg_left a.1 (sub_nonneg.mpr tu),
        mul_le_mul_of_nonneg_left a.2 (sub_nonneg.mpr tu),mul_le_mul_of_nonneg_left b.1 tn,
        mul_le_mul_of_nonneg_left b.2 tn,u.1,u.2]
    apply (div_le_div_of_nonneg_right raw cp.le).trans
    have den : j^2*Real.sqrt c≤c := by
      have m:=mul_le_mul_of_nonneg_right sc sp.le
      nlinarith only [m,Real.sq_sqrt cp.le]
    exact (div_le_div_of_nonneg_left (by norm_num : (0:ℝ)≤6) (by positivity) den).trans
      (div_le_div_of_nonneg_right (by linarith [total_pos]) (by positivity))

theorem bank_sum (N : ℕ) (f : ℝ → ℝ) (x : ℝ) :
    bank N f x = ∑ i ∈ Finset.range (N+1), f (x/(2:ℝ)^i)/(2:ℝ)^i := by
  induction N generalizing x with
  | zero => simp [bank]
  | succ n ih =>
    change f x+bank n f (x/2)/2=_
    rw [ih,Finset.sum_div,Finset.sum_range_succ' (f:=fun i => f (x/(2:ℝ)^i)/(2:ℝ)^i)]
    simp only [pow_zero,div_one]
    rw [add_comm]
    apply congrArg (fun y : ℝ => y+f x)
    apply Finset.sum_congr rfl
    intro i _
    rw [pow_succ,show x/2/2^i=x/(2^i*2) by ring]
    ring

def price := 4*(2*totalPrice+6)

theorem price_pos : 0<price := by unfold price; positivity [total_pos]

theorem bank_chord (N : ℕ) {j x t : ℝ} (jp : 1≤j)
    (lo : j^4≤x) (hi : x≤(j+1)^4) (tn : 0≤t) (tu : t≤1)
    (same : 1/x=(1-t)/j^4+t/(j+1)^4) :
    |defect (bank N (reading N 1)) (j^4) x ((j+1)^4) t|≤price/j^2 := by
  let I:=Finset.range (N+1)
  let term:=fun i : ℕ => fun y : ℝ => reading N 1 (y/(2:ℝ)^i)/2^i
  have eq : defect (bank N (reading N 1)) (j^4) x ((j+1)^4) t=
      ∑ i ∈ I,defect (term i) (j^4) x ((j+1)^4) t := by
    rw [defect,bank_sum,bank_sum,bank_sum]
    simp only [Finset.mul_sum,←Finset.sum_add_distrib,←Finset.sum_sub_distrib]
    rfl
  rw [eq]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  have bound (i : ℕ) : |defect (term i) (j^4) x ((j+1)^4) t| ≤
      ((2*totalPrice+6)/j^2)*(1/Real.sqrt 2)^i := by
    apply (scaled_chord N (one_le_pow₀ (by norm_num : (1:ℝ)≤2)) jp lo hi tn tu same).trans_eq
    have sqrt_pow (n : ℕ) : Real.sqrt ((2:ℝ)^n)=(Real.sqrt 2)^n := by
      induction n with
      | zero => simp
      | succ n ih => rw [pow_succ,Real.sqrt_mul (by positivity),ih,pow_succ]
    rw [sqrt_pow]
    ring
  apply (Finset.sum_le_sum (fun i _ => bound i)).trans
  rw [←Finset.mul_sum]
  have sp:=Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)
  have coef : 1/Real.sqrt 2≤3/4 := (div_le_iff₀ sp).mpr (by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2)])
  have geo:=finite_geometric (by positivity : 0≤1/Real.sqrt 2) (by linarith : 1/Real.sqrt 2<1) N
  have bound4 : 1/(1-1/Real.sqrt 2)≤4 := (div_le_iff₀ (by linarith)).mpr (by linarith)
  have mul:=mul_le_mul_of_nonneg_left (geo.trans bound4) (by positivity [total_pos] : 0≤(2*totalPrice+6)/j^2)
  exact mul.trans_eq (by dsimp [price];ring)

theorem bank_cap (N M : ℕ) {x : ℝ} (xp : 0<x) : |bank M (reading N 1) x|≤6 := by
  induction M generalizing x with
  | zero =>
    change |reading N 1 x|≤6
    exact (amplitude N 1 x xp).trans (by norm_num)
  | succ n ih =>
    change |reading N 1 x+bank n (reading N 1) (x/2)/2|≤6
    apply (abs_add_le _ _).trans
    rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
    have a : |reading N 1 x|≤3 := by simpa using amplitude N 1 x xp
    linarith only [a,ih (x:=x/2) (by positivity)]

theorem rh_of_bank_fourths {A : ℝ} (an : 0≤A) (checks : ∃ B : ℕ, ∀ N j : ℕ, B≤j → 0<j →
    j^4≤2^N → -(A/(j:ℝ)^2)≤bank N (reading N 1) ((j:ℝ)^4)) : RiemannHypothesis := by
  obtain ⟨B,sign⟩ := checks
  apply OneHead.rh_of_bank_floors
  intro e ep small
  let C:=4*(price+A)+6*((B:ℝ)+1)^2+6
  have cn : 0<C := by dsimp [C];positivity [price_pos]
  have c3 : 6≤C := by dsimp [C];nlinarith [price_pos,sq_nonneg ((B:ℝ)+1)]
  have cost : 4*(price+A)≤C := by dsimp [C];nlinarith [sq_nonneg ((B:ℝ)+1)]
  refine ⟨C,cn.le,?_⟩
  intro N
  let K:=N+4
  refine ⟨K,by dsimp [K];omega,?_⟩
  intro x hx
  have xp:=hx.1
  have amplitude' := (neg_le_abs (bank K (reading K 1) x)).trans (bank_cap K K xp)
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
  have floor : -(C/Real.sqrt x)≤bank K (reading K 1) x := by
    by_cases active : B≤j
    · have lasted : ((j:ℝ)+1)^4≤(2:ℝ)^K := calc
        _ ≤ (2*(j:ℝ))^4 := pow_le_pow_left₀ (by positivity) (by linarith) _
        _ = (j:ℝ)^4*16 := by ring
        _ ≤ (2:ℝ)^N*16 := mul_le_mul_of_nonneg_right (lo.trans hx.2) (by norm_num)
        _ = _ := by simp [K,pow_add];ring
      have at_root (i : ℕ) (above : B ≤ i) (ip : 0 < i) (within : (i:ℝ)^4≤(2:ℝ)^K) :
          -(A/(i:ℝ)^2)≤bank K (reading K 1) ((i:ℝ)^4) :=
        sign K i above ip (by exact_mod_cast within)
      have first:=at_root j active jp (lo.trans (hi.le.trans lasted))
      have last:=at_root (j+1) (by omega) (by omega) (by simpa using lasted)
      push_cast at last
      let t:=(1/(j:ℝ)^4-1/x)/(1/(j:ℝ)^4-1/((j:ℝ)+1)^4)
      obtain ⟨tn,tu,same⟩:=coordinate (by positivity : 0<(j:ℝ)^4) lo hi.le (lo.trans_lt hi)
      have bend:=bank_chord K jr lo hi.le tn tu same
      have lower:=neg_le_abs (defect (bank K (reading K 1)) ((j:ℝ)^4) x ((j+1:ℝ)^4) t) |>.trans bend
      dsimp only [defect] at lower
      have cmp : A/((j:ℝ)+1)^2≤A/(j:ℝ)^2 := div_le_div_of_nonneg_left an (sq_pos_of_pos jpos)
        (pow_le_pow_left₀ jpos.le (by linarith) 2)
      have last' : -(A/(j:ℝ)^2)≤bank K (reading K 1) (((j:ℝ)+1)^4) := by linarith
      have ratio : (price+A)/(j:ℝ)^2≤C/Real.sqrt x := by
        apply (div_le_div_iff₀ (sq_pos_of_pos jpos) (Real.sqrt_pos.mpr xp)).mpr
        nlinarith [mul_le_mul_of_nonneg_left four (add_nonneg price_pos.le an),
          mul_le_mul_of_nonneg_right cost (sq_nonneg (j:ℝ))]
      rw [add_div] at ratio
      nlinarith [mul_le_mul_of_nonneg_left first (sub_nonneg.mpr tu),
        mul_le_mul_of_nonneg_left last' tn]
    · have before : (j:ℝ)≤B := by exact_mod_cast (le_of_not_ge active)
      have sm := pow_le_pow_left₀ (show 0≤(j:ℝ)+1 by positivity)
        (by linarith : (j:ℝ)+1≤B+1) 2
      have here : 6≤C/Real.sqrt x := (le_div_iff₀ (Real.sqrt_pos.mpr xp)).mpr (by
        dsimp [C];nlinarith [price_pos,sr.trans sm])
      linarith
  have exponent := Real.rpow_le_rpow_of_exponent_le x1 (show -(1/2:ℝ)≤e-1/2 by linarith)
  rw [Real.rpow_neg xp.le,←Real.sqrt_eq_rpow] at exponent
  rw [div_eq_mul_inv] at floor
  linarith [mul_le_mul_of_nonneg_left exponent cn.le]

#print axioms PALRH.OneHeadSamples.rh_of_bank_fourths
end PALRH.OneHeadSamples
