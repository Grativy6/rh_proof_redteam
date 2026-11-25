import PALRH.SourceAllowance
import Mathlib.NumberTheory.Harmonic.Bounds

open Set Finset Filter MeasureTheory
open scoped Topology BigOperators
noncomputable section
namespace PALRH.FourthAccounts
open RectangleBalance PositiveArea TaperedNewton SourceAllowance

def peak (o : Bool) (j : ℕ) : ℚ := max (direction o*slope (j^4) marks) 0
def tally (o : Bool) (J : ℕ) : ℚ := ∑ j ∈ Finset.Icc 1 J, (j:ℚ)*peak o j

variable (o : Bool)

theorem mark_cap (d : ℕ) : |(marks d:ℝ)|≤1 := by
  have q : |marks d|≤1 := by
    change |(ArithmeticFunction.moebius d:ℚ)*(if d.Coprime 6 then 1 else 0)|≤1
    split
    · rw [mul_one];exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n:=d)
    · simp
  exact_mod_cast q

theorem taper_lip (x y : ℝ) : |taper x-taper y|≤|x-y| := by
  unfold taper
  simp only [max_def,min_def]
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith [le_abs_self (x-y),neg_abs_le (x-y)]

/-- Reading a real side through its preceding integer costs at most four divided by that integer. -/
theorem fractional {h : ℕ} (hp : 0<h) {x : ℝ} (lo : h≤x) (hi : x≤h+1) :
    |edge x-(slope h marks:ℝ)|≤4/(h:ℝ) := by
  have hr : 0<(h:ℝ) := by positivity
  have xp := hr.trans_le lo
  rw [←same_edge hp,edge_pad_positive xp hi,edge_pad_positive hr (le_add_of_nonneg_right zero_le_one),
    ←Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  let D := Finset.Icc 1 ⌊2*((h:ℝ)+1)⌋₊
  have diff (d : ℕ) (hd : d∈D) :
      |(marks d:ℝ)/d*taper (d/x)-(marks d:ℝ)/d*taper (d/h)|≤1/((h:ℝ)*h) := by
    have dp : 0<(d:ℝ) := by exact_mod_cast (show 0<d from (Finset.mem_Icc.mp hd).1)
    have gap := taper_lip ((d:ℝ)/x) ((d:ℝ)/h)
    rw [abs_of_nonpos (sub_nonpos.mpr (div_le_div_of_nonneg_left dp.le hr lo))] at gap
    rw [←mul_sub,abs_mul,abs_div,abs_of_pos dp]
    have pay := mul_le_mul (div_le_div_of_nonneg_right (mark_cap d) dp.le) gap (abs_nonneg _) (by positivity)
    apply pay.trans
    have eq : (1/(d:ℝ))*(-((d:ℝ)/x-(d:ℝ)/h))=(x-h)/(x*h) := by field_simp;ring
    rw [eq]
    apply (div_le_div_iff₀ (mul_pos xp hr) (mul_pos hr hr)).mpr
    have first := mul_le_mul_of_nonneg_right (show x-(h:ℝ)≤1 by linarith) (mul_nonneg hr.le hr.le)
    have second := mul_le_mul_of_nonneg_right lo hr.le
    nlinarith
  have eq : ⌊2*((h:ℝ)+1)⌋₊=2*(h+1) := by
    rw [show 2*((h:ℝ)+1)=((2*(h+1):ℕ):ℝ) by push_cast;rfl,Nat.floor_natCast]
  have card : D.card=2*(h+1) := by simp [D,eq,Nat.card_Icc]
  apply (Finset.sum_le_sum diff).trans
  rw [Finset.sum_const,card,nsmul_eq_mul]
  push_cast
  have one : (1:ℝ)≤h := by exact_mod_cast hp
  field_simp
  nlinarith

private theorem integer_cell {j k : ℕ} (jp : 0<j) (inside : k≤(j+1)^4-j^4) :
    (direction o:ℝ)*((slope (j^4+k) marks:ℚ):ℝ)≤(peak o j:ℝ)+(peak o (j+1):ℝ)+2700/(j:ℝ)^2 := by
  let H:=j^4
  let L:=(j+1)^4-j^4
  have hp : H≤(j+1)^4 := Nat.pow_le_pow_left (by omega) _
  have lp : 0<L := Nat.sub_pos_of_lt (Nat.pow_lt_pow_left (by omega) (by decide))
  have c := CarriedEdge.fourth_chord jp inside
  change |slope (H+k) marks-slope H marks-(k/L:ℚ)*(slope (H+L) marks-slope H marks)|≤2700/(j:ℚ)^2 at c
  have equal : H+L=(j+1)^4 := by dsimp only [L,H];omega
  rw [equal] at c
  have frac : 0≤(k:ℚ)/L := by positivity
  have cap : (k:ℚ)/L≤1 := (div_le_one (by positivity)).mpr (by exact_mod_cast inside)
  have old : direction o*slope H marks≤peak o j := le_max_left _ _
  have nxt : direction o*slope ((j+1)^4) marks≤peak o (j+1) := le_max_left _ _
  have opos : 0≤peak o j := le_max_right _ _
  have npos : 0≤peak o (j+1) := le_max_right _ _
  have a := mul_le_mul_of_nonneg_left old (sub_nonneg.mpr cap)
  have b := mul_le_mul_of_nonneg_left nxt frac
  have a' := mul_le_mul_of_nonneg_right (show 1-(k:ℚ)/L≤1 by linarith) opos
  have b' := mul_le_mul_of_nonneg_right cap npos
  have price : direction o*(slope (H+k) marks-slope H marks-(k/L:ℚ)*(slope ((j+1)^4) marks-slope H marks))≤2700/(j:ℚ)^2 := by
    apply (le_abs_self _).trans
    rwa [abs_mul,direction_abs,one_mul]
  have q : direction o*slope (H+k) marks≤peak o j+peak o (j+1)+2700/(j:ℚ)^2 := by nlinarith
  have moved := (Rat.cast_le (K:=ℝ)).mpr q
  simpa only [H,Rat.cast_mul,Rat.cast_add,Rat.cast_div,Rat.cast_pow,Rat.cast_natCast,Rat.cast_ofNat] using moved

theorem real_cell {j : ℕ} (jp : 0<j) {x : ℝ} (lo : (j:ℝ)^4≤x) (hi : x≤((j:ℝ)+1)^4) :
    max ((direction o:ℝ)*edge x) 0 ≤ (peak o j:ℝ)+(peak o (j+1):ℝ)+2704/(j:ℝ)^2 := by
  let h:=⌊x⌋₊
  have hp : j^4≤h := Nat.le_floor (by exact_mod_cast lo)
  have past : (0:ℝ)<(j:ℝ)^4 := by positivity
  have up : h≤(j+1)^4 := by
    exact_mod_cast (show (h:ℝ)≤(((j+1)^4:ℕ):ℝ) by push_cast; exact (Nat.floor_le (past.trans_le lo).le).trans hi)
  have hpos : 0<h := (by positivity : 0<j^4).trans_le hp
  have near := fractional hpos (Nat.floor_le (past.trans_le lo).le) (Nat.lt_floor_add_one x).le
  have cs := integer_cell o (k:=h-j^4) jp (by omega)
  rw [show j^4+(h-j^4)=h by omega] at cs
  have vpos : 0<(j:ℝ)^2 := by positivity
  have n2 : j^2≤j^4 := Nat.pow_le_pow_right jp (by decide)
  have wide : (j:ℝ)^2≤h := by exact_mod_cast n2.trans hp
  have lower : 4/(h:ℝ)≤4/(j:ℝ)^2 := div_le_div_of_nonneg_left (by norm_num) vpos wide
  have non (n : ℕ) : 0≤(peak o n:ℝ) := by exact_mod_cast (le_max_right (direction o*slope (n^4) marks) 0)
  have split : 2704/(j:ℝ)^2=2700/(j:ℝ)^2+4/(j:ℝ)^2 := by ring
  have signedNear : (direction o:ℝ)*(edge x-(slope h marks:ℝ))≤4/(h:ℝ) := by
    apply (le_abs_self _).trans
    have unit : |(direction o:ℝ)|=1 := by exact_mod_cast direction_abs o
    rwa [abs_mul,unit,one_mul]
  have v := non j
  have v' := non (j+1)
  apply max_le
  · rw [split];nlinarith [signedNear,cs,lower]
  · positivity

#print axioms PALRH.FourthAccounts.fractional
#print axioms PALRH.FourthAccounts.real_cell

private theorem peak_nonnegative (j : ℕ) : 0≤(peak o j:ℝ) := by
  exact_mod_cast (le_max_right (direction o*slope (j^4) marks) 0)

private theorem tally_step (j : ℕ) : tally o (j+1)=tally o j+((j+1:ℕ):ℚ)*peak o (j+1) := by
  unfold tally
  rw [Finset.sum_Icc_succ_top (by omega)]

private theorem strip_cost {j : ℕ} (jp : 0<j) :
    amount o (((j:ℝ)+1)^4)≤amount o ((j:ℝ)^4)+15*(j:ℝ)*(peak o j:ℝ)+
      15*((j:ℝ)+1)*(peak o (j+1):ℝ)+40560/(j:ℝ) := by
  let H := (j:ℝ)^4
  let K := ((j:ℝ)+1)^4
  have jr : 0<(j:ℝ) := by positivity
  have hpos : 0<H := by dsimp [H];positivity
  have hk : H≤K := pow_le_pow_left₀ jr.le (by linarith) _
  have d : K-H≤15*(j:ℝ)^3 := by
    have gap := CarriedEdge.fourth_gap jp
    have a : (j+1)^4≤15*j^3+j^4 := by omega
    have b : ((j:ℝ)+1)^4≤15*(j:ℝ)^3+(j:ℝ)^4 := by exact_mod_cast a
    dsimp [K,H];linarith
  let c := ((peak o j:ℝ)+(peak o (j+1):ℝ)+2704/(j:ℝ)^2)/(j:ℝ)^2
  have cn : 0≤c := by dsimp [c];positivity [peak_nonnegative o j,peak_nonnegative o (j+1)]
  let f := fun x : ℝ => max ((direction o:ℝ)*edge x) 0/Real.sqrt x
  have each (x : ℝ) (hx : x∈Set.Ioc H K) : f x≤c := by
    have root : (j:ℝ)^2≤Real.sqrt x := by
      have p := Real.sqrt_le_sqrt hx.1.le
      rwa [show H=((j:ℝ)^2)^2 by dsimp [H];ring,Real.sqrt_sq (sq_nonneg _)] at p
    have hr := real_cell o jp hx.1.le hx.2
    exact (div_le_div_of_nonneg_right hr (Real.sqrt_nonneg x)).trans
      (div_le_div_of_nonneg_left (by positivity [peak_nonnegative o j,peak_nonnegative o (j+1)]) (by positivity) root)
  have incl : Set.Ioc H K⊆Set.Ioc 0 K := fun _ h => ⟨hpos.trans h.1,h.2⟩
  have cint : IntegrableOn (fun _ : ℝ => c) (Set.Ioc H K) :=
    (continuousOn_const.integrableOn_Icc (μ:=volume)).mono_set Set.Ioc_subset_Icc_self
  have cost := setIntegral_mono_on ((amount_int o K).mono_set incl) cint measurableSet_Ioc each
  rw [setIntegral_const,Measure.real,Real.volume_Ioc,ENNReal.toReal_ofReal (sub_nonneg.mpr hk),smul_eq_mul] at cost
  have join := setIntegral_union (f:=f) (μ:=volume)
    (Set.disjoint_left.mpr (fun x (hx : x∈Set.Ioc 0 H) (hy : x∈Set.Ioc H K) => (not_lt_of_ge hx.2) hy.1))
    measurableSet_Ioc (amount_int o H) ((amount_int o K).mono_set incl)
  rw [Set.Ioc_union_Ioc_eq_Ioc hpos.le hk] at join
  change amount o K=amount o H+_ at join
  change amount o K≤amount o H+15*(j:ℝ)*(peak o j:ℝ)+15*((j:ℝ)+1)*(peak o (j+1):ℝ)+40560/(j:ℝ)
  have cap := cost.trans (mul_le_mul_of_nonneg_right d cn)
  have algebra : 15*(j:ℝ)^3*c=15*(j:ℝ)*(peak o j:ℝ)+15*(j:ℝ)*(peak o (j+1):ℝ)+40560/(j:ℝ) := by
    dsimp only [c];field_simp;ring
  rw [algebra] at cap
  linarith [peak_nonnegative o (j+1)]

theorem fourths_pay {J : ℕ} (jp : 0<J) :
    amount o ((J:ℝ)^4)≤amount o 1+30*(tally o J:ℝ)+81120*(harmonic J:ℝ) := by
  have stronger (j : ℕ) (pos : 0<j) : amount o ((j:ℝ)^4)+15*(j:ℝ)*(peak o j:ℝ)≤
      amount o 1+30*(tally o j:ℝ)+81120*(harmonic j:ℝ) := by
    induction j with
    | zero => omega
    | succ j old =>
      by_cases atone : j=0
      · subst j
        norm_num [tally,harmonic];linarith [peak_nonnegative o 1]
      have jp : 0<j := Nat.pos_of_ne_zero atone
      have jr : 0<(j:ℝ) := by positivity
      have j1 : (1:ℝ)≤j := by exact_mod_cast jp
      have pay : 40560/(j:ℝ)≤81120/((j:ℝ)+1) := by
        apply (div_le_div_iff₀ jr (by positivity)).mpr
        linarith
      rw [tally_step o,harmonic_succ]
      push_cast
      have step := strip_cost o jp
      specialize old jp
      simp only [div_eq_mul_inv] at pay step
      linarith
  have keep := stronger J jp
  linarith [mul_nonneg (show 0≤15*(J:ℝ) by positivity) (peak_nonnegative o J)]


/-- A checkpoint reads one of two nonnegative rational accounts; its sign may change between cuts. -/
def Checkpoints : Prop := ∀ k : ℕ, 0<k → ∀ B : ℕ, ∃ J : ℕ, B≤J ∧
  ∃ o : Bool, (tally o J)^k≤(J:ℚ)

private theorem subpower (checks : Checkpoints) {e : ℝ} (ep : 0<e) (B : ℕ) :
    ∃ J : ℕ, max B 1≤J ∧ ∃ o : Bool, (tally o J:ℝ)≤(J:ℝ)^e := by
  obtain ⟨k,hk⟩ := exists_nat_one_div_lt ep
  have positive : 0<((k+1:ℕ):ℝ) := by positivity
  have exp : 1≤e*((k+1:ℕ):ℝ) := by
    have h : 1/((k+1:ℕ):ℝ)<e := by simpa using hk
    exact ((div_lt_iff₀ positive).mp h).le
  obtain ⟨J,late,way,budget⟩ := checks (k+1) (by omega) (max B 1)
  have one : (1:ℝ)≤J := by exact_mod_cast (show 1≤J by omega)
  have positiveJ : 0<(J:ℝ) := by linarith
  refine ⟨J,late,way,?_⟩
  have actual : (tally way J:ℝ)^(k+1)≤(J:ℝ) := by exact_mod_cast budget
  have allow : (J:ℝ)≤((J:ℝ)^e)^(k+1) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul positiveJ.le]
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le one exp
  by_contra! bad
  exact (not_lt_of_ge (actual.trans allow)) (pow_lt_pow_left₀ bad (Real.rpow_nonneg positiveJ.le _) (by omega))

theorem rh_of_checkpoints (checks : Checkpoints) : RiemannHypothesis := by
  apply rh_of_sparse_choice
  intro e ep B
  let K := |amount true 1|+|amount false 1|
  let D : ℝ := K+81120+30+81120/e
  have big := ((tendsto_rpow_atTop ep).comp tendsto_natCast_atTop_atTop).eventually_gt_atTop (D+2)
  obtain ⟨N,hN⟩ := eventually_atTop.mp big
  obtain ⟨J,late,way,funded⟩ := subpower checks ep (max B N)
  have jp : 0<J := by omega
  have jr : 0<(J:ℝ) := by positivity
  let p := (J:ℝ)^e
  have one : 1≤p := Real.one_le_rpow (by exact_mod_cast jp) ep.le
  have high : D+2<p := by simpa only [Function.comp_apply,p] using hN J (show N≤J by omega)
  have powup : J≤J^4 := by simpa using (Nat.pow_le_pow_right jp (by decide : 1≤4))
  refine ⟨J^4,by omega,way,?_⟩
  have log := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos jr e)
  rw [Real.log_rpow jr] at log
  have l : Real.log J ≤p/e := (le_div_iff₀ ep).mpr (by dsimp [p];linarith)
  have core := fourths_pay way jp
  have harm := harmonic_le_one_add_log J
  have baseBound : amount way 1≤K := by
    dsimp [K]; cases way <;> linarith [le_abs_self (amount true 1),le_abs_self (amount false 1),
      abs_nonneg (amount true 1),abs_nonneg (amount false 1)]
  have const : amount way 1+30*(tally way J:ℝ)+81120*(harmonic J:ℝ)≤D*p := by
    have base : 0≤K+81120 := by dsimp [K];positivity
    have scale := mul_le_mul_of_nonneg_left one base
    dsimp only [D]
    change (tally way J:ℝ)≤p at funded
    have rule : 81120*(p/e)=(81120/e)*p := by ring
    linarith
  have step : D*p≤p^2 := by nlinarith [mul_le_mul_of_nonneg_right (show D≤p by linarith) (show 0≤p by linarith)]
  have more : p^2≤p^4 := pow_le_pow_right₀ one (by decide)
  push_cast
  rw [←Real.rpow_natCast_mul jr.le]
  have eq : (J:ℝ)^((4:ℕ)*e)=p^4 := by
    dsimp only [p]
    rw [←Real.rpow_natCast,←Real.rpow_mul jr.le,mul_comm]
  exact (core.trans (const.trans (step.trans more))).trans_eq eq.symm

#print axioms PALRH.FourthAccounts.fourths_pay
#print axioms PALRH.FourthAccounts.rh_of_checkpoints
end PALRH.FourthAccounts
