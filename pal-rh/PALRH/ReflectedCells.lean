import PALRH.CubicFourth

open Finset Set
open scoped BigOperators Classical
noncomputable section
namespace PALRH.ReflectedCells
open CubicQuadrature RectangleBalance TaperedNewton

/-- A monotone cubic whose derivative vanishes at the two ends of its transition. -/
def weight (T n : ℕ) : ℝ := (max 0 (1-(n:ℝ)/T))^2*(1+2*(n:ℝ)/T)
def ramp (T d : ℕ) : ℝ := if d≤T then ((T:ℝ)-d)/(2*d) else 0
def numerator (T d r : ℝ) := T*r*(d-r)*(d-2*r)-r^2*(d-r)^2
def residue (T d : ℕ) : ℝ :=
  if d≤T then numerator T d (T%d:ℕ)/(2*(d:ℝ)*T^3) else 0

theorem flip (T d r : ℝ) : numerator T d r+numerator T d (d-r)= -2*r^2*(d-r)^2 := by
  unfold numerator;ring

/-- A telescoping polynomial identity keeps the remainder of the last division. -/
theorem cubic_sum (T d : ℝ) (N : ℕ) :
    2*d*(∑ i ∈ Finset.Icc 1 N,(T-i*d)^2*(T+2*i*d))=
      T^3*(T-d)-numerator T d (T-(N:ℝ)*d) := by
  induction N with
  | zero => simp [numerator];ring
  | succ N old =>
    rw [Finset.sum_Icc_succ_top (by omega),mul_add,old]
    unfold numerator
    push_cast
    ring

theorem weight_stop {T : ℕ} (tp : 0<T) (n : ℕ) (after : T≤n) : weight T n=0 := by
  have tr : 0<(T:ℝ) := by exact_mod_cast tp
  have u := (one_le_div tr).mpr (by exact_mod_cast after : (T:ℝ)≤n)
  simp [weight,max_eq_left (sub_nonpos.mpr u)]

theorem cell_identity {T d : ℕ} (tp : 0<T) (dp : 0<d) :
    ramp T d-profile T (weight T) d=residue T d := by
  have tr : 0<(T:ℝ) := by exact_mod_cast tp
  have dr : 0<(d:ℝ) := by exact_mod_cast dp
  by_cases inframe : d≤T
  · let N:=T/d
    let I:=Finset.Icc 1 N
    have trim : profile T (weight T) d=∑ j ∈ I, weight T (j*d) := by
      symm
      apply Finset.sum_subset (fun j hj => Finset.mem_Icc.mpr
        ⟨(Finset.mem_Icc.mp hj).1,((Finset.mem_Icc.mp hj).2).trans (Nat.div_le_self _ _)⟩)
      intro j hj missing
      have outside : T/d<j := by
        by_contra! good;exact missing (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hj).1,good⟩)
      exact weight_stop tp _ ((Nat.div_lt_iff_lt_mul dp).mp outside).le
    have expand (j : ℕ) (hj : j∈I) : weight T (j*d)=
        (((T:ℝ)-j*d)^2*(T+2*j*d))/T^3 := by
      have low := (Nat.le_div_iff_mul_le dp).mp (Finset.mem_Icc.mp hj).2
      have yes : (j:ℝ)*d/T≤1 := (div_le_one tr).mpr (by exact_mod_cast low)
      rw [weight,Nat.cast_mul,max_eq_right (sub_nonneg.mpr yes)]
      field_simp
    have rr : (T:ℝ)-(N:ℝ)*d=(T%d:ℕ) := by
      have h := Nat.mod_add_div T d
      have cast : ((T%d:ℕ):ℝ)+(d:ℝ)*(N:ℝ)=T := by exact_mod_cast h
      linarith
    have eq := cubic_sum (T:ℝ) (d:ℝ) N
    rw [rr] at eq
    rw [ramp,if_pos inframe,trim,Finset.sum_congr rfl expand,←Finset.sum_div,residue,if_pos inframe]
    field_simp
    dsimp only [I]
    simp only [mul_comm,mul_left_comm,mul_assoc] at eq ⊢
    linarith
  · have vanish : profile T (weight T) d=0 := Finset.sum_eq_zero (fun j hj =>
      weight_stop tp _ ((le_of_not_ge inframe).trans (Nat.le_mul_of_pos_left _ (Finset.mem_Icc.mp hj).1)))
    simp [ramp,residue,inframe,vanish]

theorem residue_cap {T d : ℕ} (tp : 0<T) (dp : 0<d) :
    |residue T d|≤((d:ℝ)/T)^2 := by
  by_cases inside : d≤T
  · let q:=(T%d:ℕ)/(d:ℝ)
    let v:=(d:ℝ)/T
    have dr : 0<(d:ℝ) := by exact_mod_cast dp
    have tr : 0<(T:ℝ) := by exact_mod_cast tp
    have qn : 0≤q := by dsimp [q];positivity
    have qu : q≤1 := (div_le_one dr).mpr (by exact_mod_cast (Nat.mod_lt T dp).le)
    have vn : 0≤v := by dsimp [v];positivity
    have vu : v≤1 := (div_le_one tr).mpr (by exact_mod_cast inside)
    have prod : 0≤q*(1-q) := mul_nonneg qn (sub_nonneg.mpr qu)
    have unit : q*(1-q)≤1 := by nlinarith [sq_nonneg q]
    have ff : |1-2*q|≤1 := abs_le.mpr ⟨by linarith,by linarith⟩
    have odd : |q*(1-q)*(1-2*q)|≤1 := by
      rw [abs_mul,abs_of_nonneg prod]
      exact (mul_le_mul unit ff (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
    have even : (q*(1-q))^2≤1 := by simpa using pow_le_pow_left₀ prod unit 2
    have high : v^3≤v^2 := by simpa [pow_succ] using mul_le_mul_of_nonneg_left vu (sq_nonneg v)
    have form : residue T d=v^2/2*(q*(1-q)*(1-2*q))-v^3/2*(q*(1-q))^2 := by
      rw [residue,if_pos inside,numerator]
      dsimp only [q,v]
      field_simp
    rw [form]
    apply (abs_sub _ _).trans
    rw [abs_mul (v^2/2) _,abs_mul (v^3/2) _,abs_of_nonneg (by positivity : 0≤v^2/2),abs_of_nonneg (by positivity : 0≤v^3/2),
      abs_of_nonneg (sq_nonneg (q*(1-q)))]
    change _≤v^2
    nlinarith [mul_le_mul_of_nonneg_left odd (show 0≤v^2/2 by positivity),
      mul_le_mul_of_nonneg_left even (show 0≤v^3/2 by positivity)]
  · rw [residue,if_neg inside,abs_zero];positivity

theorem ramp_difference {H d : ℕ} (hp : 0<H) (dp : 0<d) :
    ramp (2*H) d-ramp (2*H) (2*d)=(H:ℝ)/(2*d)*taper ((d:ℝ)/H) := by
  have hr : 0<(H:ℝ) := by exact_mod_cast hp
  have dr : 0<(d:ℝ) := by exact_mod_cast dp
  by_cases small : d≤H
  · have one := (div_le_one hr).mpr (by exact_mod_cast small : (d:ℝ)≤H)
    rw [ramp,if_pos (by omega),ramp,if_pos (by omega),taper,min_eq_left (by linarith),max_eq_right zero_le_one]
    push_cast;field_simp;ring
  by_cases before : d≤2*H
  · have u := (one_le_div hr).mpr (by exact_mod_cast (le_of_not_ge small) : (H:ℝ)≤d)
    have v := (div_le_iff₀ hr).mpr (by exact_mod_cast before : (d:ℝ)≤2*H)
    rw [ramp,if_pos before,ramp,if_neg (by omega),taper,min_eq_right (by linarith),max_eq_right (by linarith)]
    push_cast;field_simp;ring
  · have late := (le_div_iff₀ hr).mpr (by exact_mod_cast (le_of_not_ge before) : 2*(H:ℝ)≤d)
    rw [ramp,if_neg before,ramp,if_neg (by omega),taper,min_eq_right (by linarith),max_eq_left (by linarith)];ring

#print axioms PALRH.ReflectedCells.flip
#print axioms PALRH.ReflectedCells.cell_identity
#print axioms PALRH.ReflectedCells.residue_cap
#print axioms PALRH.ReflectedCells.ramp_difference
end PALRH.ReflectedCells
