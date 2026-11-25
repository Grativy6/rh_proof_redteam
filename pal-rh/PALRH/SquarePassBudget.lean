import PALRH.SquarePass

open Set Finset Filter MeasureTheory
open scoped Topology BigOperators
noncomputable section
namespace PALRH.SquarePassBudget
open SquarePass RectangleBalance
open TaperedNewton (oldSlope marks old_slope_cap)

/-- The actual continuous edge is a convexly weighted sum of sharp reciprocal readings. -/
theorem seed_cap {x : ℝ} (pos : 0<x) : |edge x|≤1 := by
  let U:=fun n : ℕ => (oldSlope n:ℝ)
  let w:=fun n : ℕ => taper (n/x)
  have bounds (n : ℕ) : |U n|≤1 := by
    rcases n.eq_zero_or_pos with z|p
    · simp [z,U,oldSlope]
    · dsimp only [U];exact_mod_cast old_slope_cap p
  have increment (n : ℕ) : U (n+1)=U n+(marks (n+1):ℝ)/(n+1:ℕ) := by
    have h : oldSlope (n+1)=oldSlope n+marks (n+1)/(n+1:ℕ) := by
      unfold oldSlope;rw [Finset.sum_Icc_succ_top (by omega)]
    dsimp only [U];rw [h,Rat.cast_add,Rat.cast_div,Rat.cast_natCast]
  have anti : Antitone taper := fun a b le => max_le_max_left _ (min_le_min_left _ (by linarith))
  have falls (n : ℕ) : w (n+1)≤w n := anti
    (div_le_div_of_nonneg_right (by exact_mod_cast n.le_succ : (n:ℝ)≤(n+1:ℕ)) pos.le)
  have non (n : ℕ) : 0≤w n := le_max_left _ _
  have form (M : ℕ) : (∑ n ∈ Finset.Icc 1 M, (marks n:ℝ)/n*w n)=
      w (M+1)*U M+∑ n ∈ Finset.Icc 1 M, (w n-w (n+1))*U n := by
    induction M with
    | zero => simp [U,oldSlope]
    | succ M old =>
      rw [Finset.sum_Icc_succ_top (by omega),Finset.sum_Icc_succ_top (f:=fun n => (w n-w (n+1))*U n) (by omega),old,increment]
      ring
  have widths (M : ℕ) : w (M+1)+(∑ n ∈ Finset.Icc 1 M, (w n-w (n+1)))=w 1 := by
    induction M with
    | zero => simp
    | succ M old => rw [Finset.sum_Icc_succ_top (by omega)];linarith
  let M:=⌊2*x⌋₊
  change |∑ n ∈ Finset.Icc 1 M, (marks n:ℝ)/n*w n|≤1
  rw [form]
  apply (abs_add_le _ _).trans
  have a : |w (M+1)*U M|≤w (M+1) := by
    rw [abs_mul,abs_of_nonneg (non _)]
    exact (mul_le_mul_of_nonneg_left (bounds M) (non _)).trans_eq (mul_one _)
  have b (n : ℕ) : |(w n-w (n+1))*U n|≤w n-w (n+1) := by
    have h := sub_nonneg.mpr (falls n)
    rw [abs_mul,abs_of_nonneg h]
    exact (mul_le_mul_of_nonneg_left (bounds n) h).trans_eq (mul_one _)
  have total := (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (s:=Finset.Icc 1 M) (fun n _ => b n))
  exact (add_le_add a total).trans ((widths M).le.trans (max_le zero_le_one (min_le_left _ _)))

private theorem base_int {f : ℝ → ℝ} (reg : Regular f) (quiet : Before f) (X : ℝ) :
    IntegrableOn (fun x : ℝ => f x/Real.sqrt x) (Set.Ioc 0 X) := by
  let den := fun y : ℝ => Real.sqrt (max y (1/4))
  have cd : Continuous den := Real.continuous_sqrt.comp (continuous_id.max continuous_const)
  have dn (y : ℝ) : den y≠0 := (Real.sqrt_pos.mpr
    (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/4) (le_max_right y _))).ne'
  have h := ((reg X).mono (fun _ (hx : _∈Set.Icc 0 X) => hx.2)).div cd.continuousOn (fun _ _ => dn _)
  apply (integrableOn_congr_fun (g:=fun y : ℝ => f y/den y) ?_ measurableSet_Ioc).mpr
    (h.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
  intro y _
  by_cases hi : 1/4≤y
  · simp only [den,max_eq_left hi]
  · simp only [quiet y (by linarith : y≤1/2),zero_div]

private theorem gain_meas : Measurable gain := by
  have h := (measurable_of_countable harmonics).comp (Nat.measurable_floor (R:=ℝ))
  unfold gain
  have nn : Measurable (fun x : ℝ => (⌊x⌋₊:ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n:ℝ))).comp Nat.measurable_floor
  exact (nn.div Real.continuous_sqrt.measurable).sub (h.div_const _)

theorem balance_int {f : ℝ → ℝ} (reg : Regular f) (quiet : Before f) (X : ℝ) :
    IntegrableOn (fun y : ℝ => f y*(gain (X/y)/Real.sqrt y)) (Set.Ioc 0 X) := by
  have h := (base_int reg quiet X).mul_bdd ((gain_meas.comp (measurable_const.div measurable_id)).aestronglyMeasurable)
    (c:=1) (Filter.Eventually.of_forall (fun y => (show ‖gain (X/y)‖≤1 from by
      by_cases big : 1≤X/y
      · rw [Real.norm_eq_abs,abs_of_nonneg (by linarith [uniform_floor big])]
        exact ceiling big
      · simp [gain,Nat.floor_eq_zero.mpr (lt_of_not_ge big),harmonics])))
  apply (integrableOn_congr_fun (g:=fun y : ℝ => (f y/Real.sqrt y)*gain (X/y)) ?_ measurableSet_Ioc).mpr h
  intro y _;dsimp;ring

theorem size_int {f : ℝ → ℝ} (reg : Regular f) (quiet : Before f) (X : ℝ) :
    IntegrableOn (fun y : ℝ => |f y| *(1/Real.sqrt y)) (Set.Ioc 0 X) := by
  simpa only [one_div,div_eq_mul_inv,one_mul] using base_int (f:=fun x => |f x|)
    (fun R => (reg R).abs) (fun t ht => by simp [quiet t ht]) X

theorem size_mono {f : ℝ → ℝ} (reg : Regular f) (quiet : Before f) {X Y : ℝ} (le : X≤Y) : size f X≤size f Y := by
  exact setIntegral_mono_set (size_int reg quiet Y) (Filter.Eventually.of_forall (fun _ => by positivity))
    (Filter.Eventually.of_forall (fun _ hx => ⟨hx.1,hx.2.trans le⟩))

theorem size_shift {p : ℕ} (pos : 0<p) (f : ℝ → ℝ) {X : ℝ} (xp : 0<X) :
    size (shift p f) X=size f (X/(p:ℝ)^2) := by
  have eq : (fun x : ℝ => |shift p f x|)=shift p (fun y => |f y|) := by
    funext x;rw [shift,abs_div,abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) p)];rfl
  rw [size,eq,window_shift _ _ pos xp,size]

theorem undo_size (N : ℕ) {p : ℕ} (pp : 2≤p) {f : ℝ → ℝ} (reg : Regular f) (quiet : Before f)
    {X : ℝ} (xp : 0<X) (inside : X≤(2:ℝ)^N) :
    size f X≤2*size (sweep N p f) X := by
  let g:=sweep N p f
  have pn : 0<p := by omega
  have gr := sweep_regular N pn reg
  have gq := sweep_before N pn quiet
  have ir := size_int gr gq X
  have is := size_int (shift_regular pn gr) (shift_before pn gq) X
  have each (t : ℝ) (ht : t∈Set.Ioc 0 X) :
      |f t| *(1/Real.sqrt t)≤|g t| *(1/Real.sqrt t)+|shift p g t| *(1/Real.sqrt t) := by
    rw [←add_mul,on_head pp N quiet (ht.2.trans inside)]
    exact mul_le_mul_of_nonneg_right (abs_sub (g t) (shift p g t)) (by positivity)
  have total := setIntegral_mono_on (size_int reg quiet X) (ir.add is) measurableSet_Ioc each
  change size f X≤∫ t in Set.Ioc 0 X, |g t| *(1/Real.sqrt t)+|shift p g t| *(1/Real.sqrt t) at total
  rw [integral_add ir is] at total
  change size f X≤size g X+size (shift p g) X at total
  rw [size_shift pn g xp] at total
  have p1 : (1:ℝ)≤p := by exact_mod_cast (show 1≤p by omega)
  have smaller : size g (X/(p:ℝ)^2)≤size g X := size_mono gr gq (div_le_self xp.le (one_le_pow₀ p1))
  change size f X≤2*size g X
  linarith

theorem recovered_size (N k : ℕ) {X : ℝ} (xp : 0<X) (inside : X≤(2:ℝ)^N) :
    size edge X≤4^k*size (reading N k) X := by
  induction k with
  | zero => simp [reading]
  | succ k old =>
    have good := reading_good N k
    have a := undo_size N (by decide : 2≤3) good.1 good.2 xp inside
    have b := undo_size N (by decide : 2≤2) (sweep_regular N (by decide : 0<3) good.1)
      (sweep_before N (by decide : 0<3) good.2) xp inside
    change size (sweep N 3 (reading N k)) X≤2*size (reading N (k+1)) X at b
    have both : size (reading N k) X≤4*size (reading N (k+1)) X := by linarith
    exact old.trans ((mul_le_mul_of_nonneg_left both (by positivity)).trans_eq (by rw [pow_succ];ring))

#print axioms PALRH.SquarePassBudget.seed_cap
#print axioms PALRH.SquarePassBudget.recovered_size

private theorem finite_geometric {r : ℝ} (non : 0≤r) (less : r<1) (N : ℕ) :
    (∑ j ∈ Finset.range (N+1), r^j)≤1/(1-r) := by
  have eq (n : ℕ) : (∑ j ∈ Finset.range n, r^j)*(1-r)=1-r^n := by
    induction n with
    | zero => simp
    | succ n old => rw [Finset.sum_range_succ,pow_succ,add_mul,old];ring
  apply (le_div_iff₀ (sub_pos.mpr less)).mpr
  rw [eq]
  linarith [pow_nonneg non (N+1)]

private theorem sup_add (p N : ℕ) (pp : 1<p) {f : ℝ → ℝ} {C : ℝ} (non : 0≤C)
    (known : ∀ x : ℝ, 0<x → |f x|≤C) {x : ℝ} (xp : 0<x) :
    |sweep N p f x|≤C*(1/(1-1/(p:ℝ))) := by
  have pr : (1:ℝ)<p := by exact_mod_cast pp
  let r:=1/(p:ℝ)
  have rg : r<1 := (div_lt_one (by linarith)).mpr pr
  have rn : 0≤r := by dsimp [r];positivity
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  have single (j : ℕ) : |shift (p^j) f x|≤C*r^j := by
    dsimp [shift,r]
    rw [abs_div,abs_of_nonneg (by positivity : 0≤((p^j:ℕ):ℝ)),Nat.cast_pow,one_div,inv_pow,←div_eq_mul_inv]
    exact div_le_div_of_nonneg_right (known _ (by positivity)) (by positivity)
  have sum := Finset.sum_le_sum (s:=Finset.range (N+1)) (fun j _ => single j)
  rw [←Finset.mul_sum] at sum
  exact sum.trans (mul_le_mul_of_nonneg_left (finite_geometric rn rg N) non)

theorem amplitude (N k : ℕ) : ∀ x : ℝ, 0<x → |reading N k x|≤3^k := by
  induction k with
  | zero => intro x xp;simpa [reading] using seed_cap xp
  | succ k old =>
    have a := fun x (xp : 0<x) => sup_add 3 N (by decide) (by positivity : 0≤(3:ℝ)^k) old xp
    intro x xp
    have b := sup_add 2 N (by decide) (by positivity : 0≤(3:ℝ)^k*(1/(1-1/(3:ℝ)))) a xp
    change |sweep N 2 (sweep N 3 (reading N k)) x|≤_
    exact b.trans_eq (by rw [pow_succ];norm_num;ring)

def ratio (p : ℕ) (e : ℝ) := ((p:ℝ)^(2*e))⁻¹
def price (p : ℕ) (e : ℝ) := 1/(1-ratio p e)
def pairPrice (e : ℝ) := price 3 e*price 2 e

private theorem ratio_lt {p : ℕ} (pp : 1<p) {e : ℝ} (ep : 0<e) : ratio p e<1 := by
  have pr : (1:ℝ)<p := by exact_mod_cast pp
  exact inv_lt_one_of_one_lt₀ (Real.one_lt_rpow pr (by linarith))

theorem price_pos {p : ℕ} (pp : 1<p) {e : ℝ} (ep : 0<e) : 0<price p e :=
  div_pos zero_lt_one (sub_pos.mpr (ratio_lt pp ep))

theorem pair_price_pos {e : ℝ} (ep : 0<e) : 0<pairPrice e :=
  mul_pos (price_pos (by decide : 1<3) ep) (price_pos (by decide : 1<2) ep)

private theorem transport_power {p : ℕ} (pp : 1<p) (i : ℕ) (e : ℝ) {x : ℝ} (xp : 0<x) :
    (2*(x/((p^i:ℕ):ℝ)^2))^e=(2*x)^e*(ratio p e)^i := by
  have pr : 0<(p:ℝ) := by exact_mod_cast (show 0<p by omega)
  have base : ((((p:ℝ)^i)^2)^e)=((p:ℝ)^(2*e))^i := by
    rw [←Real.rpow_natCast_mul (pow_nonneg pr.le i),←Real.rpow_natCast_mul pr.le,
      ←Real.rpow_mul_natCast pr.le]
    congr 1
    push_cast;ring
  rw [Nat.cast_pow,mul_div_assoc',Real.div_rpow (by positivity) (by positivity),base,ratio,inv_pow,div_eq_mul_inv]

private theorem balance_sweep (N : ℕ) {p : ℕ} (pp : 1<p) {f : ℝ → ℝ} (reg : Regular f) (quiet : Before f)
    {e C : ℝ} (ep : 0<e) (non : 0≤C) (funded : ∀ x : ℝ, 0<x → balanceOf f x≤C*(2*x)^e)
    {X : ℝ} (xp : 0<X) : balanceOf (sweep N p f) X≤(C*price p e)*(2*X)^e := by
  let I:=Finset.range (N+1)
  have collect : balanceOf (sweep N p f) X=∑ i ∈ I, balanceOf f (X/((p^i:ℕ):ℝ)^2) := by
    have eq (y : ℝ) : sweep N p f y*(gain (X/y)/Real.sqrt y)=
        ∑ i ∈ I, shift (p^i) f y*(gain (X/y)/Real.sqrt y) := by rw [sweep,Finset.sum_mul]
    rw [balanceOf,window,setIntegral_congr_fun measurableSet_Ioc (fun y _ => eq y),
      integral_finsetSum _ (fun i _ => balance_int (shift_regular (pow_pos (by omega : 0<p) i) reg)
        (shift_before (pow_pos (by omega : 0<p) i) quiet) X)]
    exact Finset.sum_congr rfl (fun i _ => window_shift _ _ (pow_pos (by omega) i) xp)
  rw [collect]
  have each (i : ℕ) : balanceOf f (X/((p^i:ℕ):ℝ)^2)≤(C*(2*X)^e)*(ratio p e)^i := by
    have pos : 0<((p^i:ℕ):ℝ) := by exact_mod_cast pow_pos (show 0<p by omega) i
    have a := funded _ (div_pos xp (sq_pos_of_pos pos))
    rw [transport_power pp i e xp] at a
    simpa only [mul_assoc] using a
  have sum := Finset.sum_le_sum (s:=I) (fun i _ => each i)
  rw [←Finset.mul_sum] at sum
  have rn : 0≤ratio p e := by dsimp [ratio];positivity
  have total := sum.trans (mul_le_mul_of_nonneg_left (finite_geometric rn (ratio_lt pp ep) N) (by positivity))
  exact total.trans_eq (by unfold price;ring)

theorem balance_bound (N k : ℕ) {e : ℝ} (ep : 0<e) : ∀ X : ℝ, 0<X →
    balanceOf (reading N k) X≤(16*pairPrice e^k)*(2*X)^e := by
  induction k with
  | zero =>
    intro X xp
    simp only [pow_zero,mul_one,reading]
    by_cases small : X≤1/2
    · have z : balanceOf edge X=0 := setIntegral_eq_zero_of_forall_eq_zero (fun y (hy : y∈Set.Ioc 0 X) => by
        change edge y*_=0;rw [edge_before (hy.2.trans small),zero_mul])
      rw [z];positivity
    · have bound := SourceAllowance.balance_ceiling xp
      change balanceOf edge X≤16 at bound
      have one := Real.one_le_rpow (show 1≤2*X by linarith) ep.le
      linarith
  | succ k old =>
    intro X xp
    have nn : 0≤16*pairPrice e^k := mul_nonneg (by norm_num) (pow_nonneg (pair_price_pos ep).le k)
    have good := reading_good N k
    have first := fun x (h : 0<x) => balance_sweep N (by decide : 1<3) good.1 good.2 ep nn old h
    have sec := balance_sweep N (by decide : 1<2) (sweep_regular N (by decide : 0<3) good.1)
      (sweep_before N (by decide : 0<3) good.2) ep (mul_nonneg nn (price_pos (by decide : 1<3) ep).le) first xp
    exact sec.trans_eq (by unfold pairPrice;rw [pow_succ];ring)

#print axioms PALRH.SquarePassBudget.amplitude
#print axioms PALRH.SquarePassBudget.balance_bound


theorem positive_area {f : ℝ → ℝ} (reg : Regular f) (quiet : Before f) {X : ℝ}
    (positive : ∀ y ∈ Set.Ioc 0 X, 0≤f y) : size f X≤5*balanceOf f X := by
  rw [size,balanceOf,window,window,←integral_const_mul]
  apply setIntegral_mono_on (size_int reg quiet X) ((balance_int reg quiet X).const_mul (5:ℝ)) measurableSet_Ioc
  intro y hy
  have low := uniform_floor ((one_le_div hy.1).mpr hy.2)
  have factor : f y≤5*f y*gain (X/y) := by nlinarith [mul_le_mul_of_nonneg_left low (positive y hy)]
  change |f y| *(1/Real.sqrt y)≤5*(f y*(gain (X/y)/Real.sqrt y))
  rw [abs_of_nonneg (positive y hy),mul_one_div,show 5*(f y*(gain (X/y)/Real.sqrt y))=
    (5*f y*gain (X/y))/Real.sqrt y by ring]
  exact div_le_div_of_nonneg_right factor (Real.sqrt_nonneg y)

def RealPasses : Prop := ∀ q : ℕ, 0<q → ∀ B : ℕ, ∃ N : ℕ, B≤N ∧ ∃ k : ℕ, 0<k ∧ q*k≤N ∧
  ∀ x ∈ Set.Ioc (0:ℝ) ((2:ℝ)^N), 0≤reading N k x

theorem rh_of_real_passes (funded : RealPasses) : RiemannHypothesis := by
  apply PositiveArea.rh_of_sparse_up
  intro a ap B
  let e:=a/3
  have ep : 0<e := by dsimp [e];linarith
  let t:=(2:ℝ)^e
  have more : 1<t := Real.one_lt_rpow (by norm_num) ep
  let C:=4*pairPrice e
  have cn : 0≤C := mul_nonneg (by norm_num) (pair_price_pos ep).le
  have tends : Tendsto (fun n : ℕ => t^n) atTop atTop := tendsto_pow_atTop_atTop_of_one_lt more
  obtain ⟨r,largeR⟩ := eventually_atTop.mp (tends.eventually_gt_atTop C)
  obtain ⟨m,largeM⟩ := eventually_atTop.mp (tends.eventually_gt_atTop (80*t))
  obtain ⟨N,late,k,_kp,cost,pos⟩ := funded (r+1) (by omega) (max B m)
  let H := (2:ℝ)^N
  have hp : 0<H := by dsimp [H];positivity
  have id : H^e=t^N := by
    dsimp only [H,t];rw [←Real.rpow_natCast_mul (by norm_num : (0:ℝ)≤2),←Real.rpow_mul_natCast (by norm_num : (0:ℝ)≤2),mul_comm]
  have budget : C^k≤H^e := calc
    C^k ≤ (t^(r+1))^k := pow_le_pow_left₀ cn (largeR _ (by omega)).le _
    _ = t^((r+1)*k) := (pow_mul _ _ _).symm
    _ ≤ t^N := pow_le_pow_right₀ more.le cost
    _ = _ := id.symm
  have room : 80*t≤H^e := (largeM _ (show m≤N by omega)).le.trans_eq id.symm
  have base : PositiveArea.up H≤size edge H := by
    apply setIntegral_mono_on (PositiveArea.up_integrable H)
      (size_int edge_continuousOn (fun _ hy => edge_before hy) H) measurableSet_Ioc
    intro y _
    change max (edge y) 0/Real.sqrt y≤|edge y| *(1/Real.sqrt y)
    rw [mul_one_div]
    exact div_le_div_of_nonneg_right (max_le (le_abs_self _) (abs_nonneg _)) (Real.sqrt_nonneg _)
  have pay := positive_area (reading_good N k).1 (reading_good N k).2 pos
  have price := balance_bound N k ep H hp
  have costed : PositiveArea.up H≤80*t*(H^e)*C^k := calc
    _ ≤ 4^k*size (reading N k) H := base.trans (recovered_size N k hp le_rfl)
    _ ≤ 4^k*(5*((16*pairPrice e^k)*(2*H)^e)) :=
      mul_le_mul_of_nonneg_left (pay.trans (mul_le_mul_of_nonneg_left price (by norm_num))) (by positivity)
    _ = _ := by dsimp only [C,t];rw [Real.mul_rpow (by norm_num) hp.le,mul_pow];ring
  have goal : PositiveArea.up H≤(H^e)^3 := by
    apply costed.trans
    have n : 0≤H^e := Real.rpow_nonneg hp.le _
    have p := mul_le_mul (mul_le_mul_of_nonneg_right room n) budget (pow_nonneg cn _) (mul_nonneg n n)
    nlinarith
  have exact_power : (H^e)^3=H^a := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hp.le];congr 1;dsimp [e];norm_num
  refine ⟨2^N,(show B≤N by omega).trans Nat.lt_two_pow_self.le,?_⟩
  push_cast
  exact goal.trans_eq exact_power

#print axioms PALRH.SquarePassBudget.rh_of_real_passes

end PALRH.SquarePassBudget
