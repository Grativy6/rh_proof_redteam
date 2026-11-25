import PALRH.HeadGrowth
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

open Finset
open scoped BigOperators
noncomputable section
namespace PALRH.Balanced
open OneTick

def headSet (H : ℕ) := Finset.Icc 1 H

def floorSum (ν : ℕ → ℚ) (H k : ℕ) : ℚ :=
  ∑ d ∈ headSet H, ν d*((k/d:ℕ):ℚ)

def slope (ν : ℕ → ℚ) (H : ℕ) : ℚ := ∑ d ∈ headSet H, ν d/d
def mass (ν : ℕ → ℚ) (H : ℕ) (t : ℚ) : ℚ := 2*t+∑ d ∈ headSet H, ν d
def upperRate (ν : ℕ → ℚ) (H : ℕ) (t : ℚ) : ℚ :=
  (mass ν H t-((5*(H:ℚ)+1)/2)*slope ν H)/H
def lowerRate (ν : ℕ → ℚ) (H : ℕ) (t : ℚ) : ℚ := slope ν H-upperRate ν H t

/-- A linear block of rational coefficients lying strictly beyond the specified octave. -/
def ramp (H j : ℕ) (a : ℚ) : ℕ → ℚ :=
  ∑ i ∈ Finset.range H, (a*((j*H+i+1:ℕ):ℚ)/H) • turn (j*H+i+1)

def profile (ν : ℕ → ℚ) (H : ℕ) (t : ℚ) : ℕ → ℚ :=
  -(∑ d ∈ headSet H, ν d • turn d) +
    ramp H 2 (lowerRate ν H t) + ramp H 3 (upperRate ν H t)

private theorem any_turn (d : ℕ) (pos : 0<d) : turn d∈fits := by
  by_cases one : d=1
  · have zero : turn d=0 := by funext k; simp [turn,one,Nat.mod_one]
    rw [zero]; exact fits.zero_mem
  · exact turn_mem (by omega)

private theorem ramp_mem (H j : ℕ) (a : ℚ) : ramp H j a∈fits := by
  apply Submodule.sum_mem
  intro i _
  exact fits.smul_mem _ (any_turn _ (by omega))

theorem profile_mem (ν : ℕ → ℚ) (H : ℕ) (t : ℚ) : profile ν H t∈fits := by
  unfold profile
  apply fits.add_mem _ (ramp_mem _ _ _)
  apply fits.add_mem _ (ramp_mem _ _ _)
  apply fits.neg_mem
  apply Submodule.sum_mem
  intro d hd
  exact fits.smul_mem _ (any_turn _ (Finset.mem_Icc.mp hd).1)

private lemma turn_floor {d : ℕ} (hd : 0<d) (k : ℕ) :
    turn d k=(k:ℚ)/d-(k/d:ℕ) := by
  have sum : (d:ℚ)*((k/d:ℕ):ℚ)+(k%d:ℕ)=(k:ℚ) := by exact_mod_cast Nat.div_add_mod k d
  unfold turn
  field_simp
  linarith

private lemma ramp_early {H j k : ℕ} (hH : 0<H) (early : k≤j*H) (a : ℚ) :
    ramp H j a k = a*(k:ℚ) := by
  simp only [ramp, Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  have eq (i : ℕ) : a*((j*H+i+1:ℕ):ℚ)/H*turn (j*H+i+1) k=a*(k:ℚ)/H := by
    rw [turn,Nat.mod_eq_of_lt (by omega)]
    have h : ((j*H+i+1:ℕ):ℚ)≠0 := by positivity
    field_simp
  simp only [eq,Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  field_simp

/-- All rows through 2H see the unmodified truncated arithmetic count. -/
theorem before_exits (ν : ℕ → ℚ) {H k : ℕ} (hH : 0<H) (early : k≤2*H) (t : ℚ) :
    profile ν H t k=floorSum ν H k := by
  simp only [profile,Pi.add_apply,Pi.neg_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  rw [ramp_early hH early,ramp_early hH (by omega : k≤3*H)]
  have old : ∑ d ∈ headSet H, ν d*turn d k =
      slope ν H*(k:ℚ)-floorSum ν H k := by
    unfold slope floorSum
    rw [Finset.sum_mul,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    rw [turn_floor (Finset.mem_Icc.mp hd).1]
    ring
  rw [old,lowerRate]
  ring

def octaveCoefficientSum (H j : ℕ) (a : ℚ) : ℚ :=
  ∑ i ∈ Finset.range H, a*((j*H+i+1:ℕ):ℚ)/H

private lemma first_indices (H : ℕ) :
    2*(∑ i ∈ Finset.range H, (i:ℚ))=(H:ℚ)*((H:ℚ)-1) := by
  induction H with
  | zero => norm_num
  | succ H ih => rw [Finset.sum_range_succ]; push_cast; linarith

theorem octave_mass {H : ℕ} (hH : 0<H) (j : ℕ) (a : ℚ) :
    octaveCoefficientSum H j a=a*(2*(j:ℚ)*H+H+1)/2 := by
  have grain (i : ℕ) : a*((j*H+i+1:ℕ):ℚ)/H = (a/H)*((j:ℚ)*H+1)+(a/H)*(i:ℚ) := by
    push_cast; ring
  simp only [octaveCoefficientSum,grain,Finset.sum_add_distrib,Finset.sum_const,
    Finset.card_range,nsmul_eq_mul,←Finset.mul_sum]
  have sum := first_indices H
  field_simp
  linear_combination a*sum

/-- The same two block rates also set the coefficient mass, hence the full-period mean. -/
theorem mass_balance (ν : ℕ → ℚ) {H : ℕ} (hH : 0<H) (t : ℚ) :
    -(∑ d ∈ headSet H, ν d) + octaveCoefficientSum H 2 (lowerRate ν H t) +
      octaveCoefficientSum H 3 (upperRate ν H t) = 2*t := by
  rw [octave_mass hH,octave_mass hH]
  unfold lowerRate upperRate mass
  push_cast
  field_simp
  ring

private lemma floor_step (ν : ℕ → ℚ) {H k : ℕ} (inside : k+1≤H) :
    floorSum ν H (k+1)-floorSum ν H k=∑ d ∈ (k+1).divisors, ν d := by
  unfold floorSum
  rw [←Finset.sum_sub_distrib]
  have term (d : ℕ) (hd : d ∈ headSet H) : ν d*((((k+1)/d:ℕ):ℚ))-ν d*((k/d:ℕ):ℚ) =
      if d ∣ k+1 then ν d else 0 := by
    by_cases h : d ∣ k+1
    · rw [Nat.succ_div_of_dvd h,if_pos h]
      push_cast
      ring
    · simp [Nat.succ_div_of_not_dvd h,h]
  have eq : (headSet H).filter (fun d => d ∣ k+1)=(k+1).divisors := by
    ext d
    simp only [headSet,Finset.mem_filter,Finset.mem_Icc,Nat.mem_divisors]
    constructor
    · intro h; exact ⟨h.2,by omega⟩
    · rintro ⟨dv,pos⟩
      have a := Nat.pos_of_dvd_of_pos dv (show 0<k+1 by omega)
      exact ⟨⟨a,(Nat.le_of_dvd (by omega) dv).trans inside⟩,dv⟩
  rw [Finset.sum_congr rfl term,←Finset.sum_filter,eq]

/-- The exact arithmetic input read off from the target's physical first differences. -/
def impulse (T : ℕ → ℚ) (d : ℕ) : ℚ :=
  ∑ ab ∈ d.divisorsAntidiagonal, (ArithmeticFunction.moebius ab.1:ℚ)*(T ab.2-T (ab.2-1))

theorem floor_recovers (T : ℕ → ℚ) (zero : T 0=0) (H : ℕ) (k : ℕ) (inside : k≤H) :
    floorSum (impulse T) H k=T k := by
  have inv : ∀ n>0, (∑ d ∈ n.divisors, impulse T d)=T n-T (n-1) :=
    ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mpr (fun _ _ => rfl)
  induction k with
  | zero => simp [floorSum,zero]
  | succ k prev =>
    have old := prev (by omega)
    have step := floor_step (impulse T) inside
    rw [inv (k+1) (by omega),Nat.add_one_sub_one] at step
    linarith

theorem profile_hits (T : ℕ → ℚ) (zero : T 0=0) {H : ℕ} (hH : 0<H) (t : ℚ)
    (k : ℕ) (inside : k≤H) : profile (impulse T) H t k=T k := by
  rw [before_exits _ hH (by omega) t,floor_recovers T zero H k inside]


def mu (d : ℕ) : ℚ := ArithmeticFunction.moebius d

private lemma mu_sum (n : ℕ) :
    (∑ d ∈ n.divisors, mu d)=if n=1 then 1 else 0 := by
  have h := DFunLike.congr_fun ArithmeticFunction.moebius_mul_coe_zeta n
  rw [ArithmeticFunction.coe_mul_zeta_apply,ArithmeticFunction.one_apply] at h
  by_cases one : n=1 <;> simp only [mu,one,if_true,if_false] at h ⊢ <;> exact_mod_cast h

def doubleMu (d : ℕ) : ℚ := if 2 ∣ d then mu (d/2) else 0

private lemma double_sum {n : ℕ} (hn : 0<n) :
    (∑ d ∈ n.divisors, doubleMu d)=if n=2 then 1 else 0 := by
  by_cases even : 2 ∣ n
  · obtain ⟨m,rfl⟩ := even
    have hm : 0<m := by omega
    unfold doubleMu
    rw [←Finset.sum_filter]
    have bridge : (∑ d ∈ (2*m).divisors.filter (fun e => 2 ∣ e), mu (d/2))=
        ∑ e ∈ m.divisors, mu e := by
      apply Finset.sum_bij' (fun d _ => d/2) (fun e _ => 2*e)
      · intro d hd; exact Nat.mul_div_cancel' (Finset.mem_filter.mp hd).2
      · intro e _; simp
      · intro d _; rfl
      · intro d hd
        obtain ⟨divn,two⟩ := Finset.mem_filter.mp hd
        obtain ⟨e,he⟩ := two
        rw [he,Nat.mul_div_cancel_left _ (by decide)]
        exact Nat.mem_divisors.mpr ⟨Nat.dvd_of_mul_dvd_mul_left (by decide : 0<2)
          (by simpa only [he] using Nat.dvd_of_mem_divisors divn),hm.ne'⟩
      · intro e he
        exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr
          ⟨Nat.mul_dvd_mul_left _ (Nat.dvd_of_mem_divisors he),hn.ne'⟩,dvd_mul_right _ _⟩
    rw [bridge,mu_sum]
    by_cases one : m=1 <;> simp [one]
  · rw [if_neg (by rintro rfl; exact even (dvd_refl 2))]
    apply Finset.sum_eq_zero
    intro d hd
    rw [doubleMu,if_neg (fun h : 2 ∣ d => even (h.trans (Nat.dvd_of_mem_divisors hd)))]

theorem occupied_impulse {n : ℕ} (hn : 0<n) : impulse occupied n=mu n := by
  have sums : ∀ m>0, (∑ d ∈ m.divisors, mu d)=occupied m-occupied (m-1) := by
    intro m hm
    rw [mu_sum]
    by_cases one : m=1 <;> simp [occupied,one,hm.ne',show m-1=0 ↔ m=1 by omega]
  exact ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mp sums n hn

theorem tick_impulse {n : ℕ} (hn : 0<n) : impulse tick n=mu n-doubleMu n := by
  have sums : ∀ m>0, (∑ d ∈ m.divisors, (mu d-doubleMu d))=tick m-tick (m-1) := by
    intro m hm
    rw [Finset.sum_sub_distrib,mu_sum,double_sum hm]
    simp only [tick,show m-1=1 ↔ m=2 by omega]
  exact ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mp sums n hn

theorem next_octave (T : ℕ → ℚ) (zero : T 0=0) {H k : ℕ} (hH : 0<H)
    (lo : H≤k) (hi : k≤2*H) (t : ℚ) :
    T k-profile (impulse T) H t k = ∑ d ∈ Finset.Ioc H k, impulse T d := by
  rw [before_exits _ hH hi t,←floor_recovers T zero k k le_rfl]
  unfold floorSum
  have split : headSet k = headSet H ∪ Finset.Ioc H k := by
    ext d
    simp only [headSet,Finset.mem_Icc,Finset.mem_union,Finset.mem_Ioc]
    omega
  have dis : Disjoint (headSet H) (Finset.Ioc H k) := by
    apply Finset.disjoint_left.mpr
    intro d a b
    have := (Finset.mem_Icc.mp a).2
    have := (Finset.mem_Ioc.mp b).1
    omega
  rw [split,Finset.sum_union dis,add_sub_cancel_left]
  apply Finset.sum_congr rfl
  intro d hd
  obtain ⟨dh,dk⟩ := Finset.mem_Ioc.mp hd
  have low : 1≤k/d := (Nat.le_div_iff_mul_le (by omega : 0<d)).mpr (by omega)
  have high : k/d<2 := (Nat.div_lt_iff_lt_mul (by omega : 0<d)).mpr (by omega)
  simp [show k/d=1 by omega]

#print axioms PALRH.Balanced.next_octave
#print axioms PALRH.Balanced.tick_impulse


private lemma cap_turn {d : ℕ} (hd : 0<d) (k : ℕ) : |turn d k|≤1 := by
  rw [turn,abs_of_nonneg (by positivity),div_le_one (by positivity)]
  exact_mod_cast (Nat.mod_lt k hd).le

private lemma cap_sum (ν : ℕ → ℚ) (H : ℕ) (v : ℕ → ℚ)
    (cap : ∀ d ∈ headSet H, |ν d|≤2) (unit : ∀ d ∈ headSet H, |v d|≤1) :
    |∑ d ∈ headSet H, ν d*v d|≤2*H := by
  calc
    _ ≤ ∑ d ∈ headSet H, |ν d*v d| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ headSet H, (2:ℚ) := by
      apply Finset.sum_le_sum
      intro d hd
      rw [abs_mul]
      exact (mul_le_of_le_one_right (abs_nonneg _) (unit d hd)).trans (cap d hd)
    _ = _ := by simp [headSet,Nat.card_Icc,mul_comm]

private lemma cap_ramp {H j : ℕ} (hH : 0<H) (a : ℚ) (k : ℕ) :
    |ramp H j a k| ≤ H*(|a| *((j:ℚ)+1)) := by
  simp only [ramp,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  calc
    _ ≤ ∑ i ∈ Finset.range H, |a*((j*H+i+1:ℕ):ℚ)/H*turn (j*H+i+1) k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range H, |a| *((j:ℚ)+1) := by
      apply Finset.sum_le_sum
      intro i hi
      have h := Finset.mem_range.mp hi
      have frac : ((j*H+i+1:ℕ):ℚ)/H ≤ (j:ℚ)+1 := by
        apply (div_le_iff₀ (by positivity)).mpr
        exact_mod_cast (show j*H+i+1 ≤ (j+1)*H by rw [Nat.add_mul,one_mul]; omega)
      rw [abs_mul]
      apply (mul_le_of_le_one_right (abs_nonneg _) (cap_turn (by omega) k)).trans
      rw [abs_div,abs_mul,abs_of_nonneg (by positivity : 0≤((j*H+i+1:ℕ):ℚ)),
        abs_of_nonneg (by positivity : 0≤(H:ℚ)),mul_div_assoc]
      exact mul_le_mul_of_nonneg_left frac (abs_nonneg _)
    _ = _ := by simp [nsmul_eq_mul]

/-- Uniform amplitude bound for the entire explicit profile. Each input is an
ordinary arithmetic bound on the signed impulses or the supplied target. -/
theorem profile_bound (ν : ℕ → ℚ) {H : ℕ} (hH : 0<H) (t : ℚ) (ht : |t|≤1)
    (small : ∀ d ∈ headSet H, |ν d|≤2) (value : |floorSum ν H H|≤1) (k : ℕ) :
    |profile ν H t k| ≤ 102*H := by
  have hq : (1:ℚ)≤H := by exact_mod_cast hH
  have base (k : ℕ) := cap_sum ν H (fun d => turn d k) small (fun d hd => cap_turn (Finset.mem_Icc.mp hd).1 k)
  have total : |∑ d ∈ headSet H, ν d|≤2*H := by simpa using cap_sum ν H (fun _ => 1) small (by simp)
  have massb : |mass ν H t| ≤ 4*H := by
    have h := abs_add_le (2*t) (∑ d ∈ headSet H, ν d)
    rw [abs_mul,abs_of_nonneg (by norm_num : (0:ℚ)≤2)] at h
    dsimp [mass]; linarith
  have relation : (H:ℚ)*slope ν H = floorSum ν H H+∑ d ∈ headSet H, ν d*turn d H := by
    unfold slope floorSum
    rw [Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    rw [turn_floor (Finset.mem_Icc.mp hd).1]; ring
  have slopeb : |slope ν H|≤3 := by
    have h := abs_add_le (floorSum ν H H) (∑ d ∈ headSet H, ν d*turn d H)
    rw [←relation,abs_mul,abs_of_nonneg (by positivity : 0≤(H:ℚ))] at h
    have bound := base H
    exact (le_of_mul_le_mul_left (show (H:ℚ)*|slope ν H|≤H*3 by linarith) (by positivity : 0<(H:ℚ)))
  have rateb : |upperRate ν H t|≤13 := by
    rw [upperRate,abs_div,abs_of_nonneg (by positivity : 0≤(H:ℚ))]
    apply (div_le_iff₀ (by positivity)).mpr
    have tri := abs_sub (mass ν H t) (((5*(H:ℚ)+1)/2)*slope ν H)
    rw [abs_mul,abs_of_nonneg (by positivity : (0:ℚ)≤(5*H+1)/2)] at tri
    have h := mul_le_mul_of_nonneg_left slopeb (by positivity : (0:ℚ)≤(5*H+1)/2)
    linarith
  have ratea : |lowerRate ν H t|≤16 := (abs_sub _ _).trans (by linarith)
  have hb := base k
  have ha := cap_ramp (j:=2) hH (lowerRate ν H t) k
  have hc := cap_ramp (j:=3) hH (upperRate ν H t) k
  change |(-(∑ d ∈ headSet H, ν d • turn d)+ramp H 2 (lowerRate ν H t)+ramp H 3 (upperRate ν H t)) k|≤_
  simp only [Pi.add_apply,Pi.neg_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  apply (abs_add_le _ _).trans
  have mid := abs_add_le (-(∑ d ∈ headSet H, ν d*turn d k)) (ramp H 2 (lowerRate ν H t) k)
  rw [abs_neg] at mid
  norm_num only [Nat.cast_ofNat] at ha hc
  nlinarith [mul_le_mul_of_nonneg_left ratea (show (0:ℚ)≤H by positivity),
    mul_le_mul_of_nonneg_left rateb (show (0:ℚ)≤H by positivity)]

#print axioms PALRH.Balanced.profile_bound

end PALRH.Balanced
