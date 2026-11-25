import PALRH.AlternatingRead

open Finset Set Filter MeasureTheory Complex
open scoped Topology BigOperators
noncomputable section
namespace PALRH.CensusTransfer
open RectangleBalance

def insertAt (p : ℕ) (f : ℕ → ℝ) (n : ℕ) : ℝ := if p∣n then f (n/p) else 0

private theorem collect_multiples {R : Type*} [AddCommMonoid R] (N p : ℕ) (hp : 0<p) (f : ℕ → R) :
    (∑ n ∈ Finset.Icc 1 N, if p∣n then f (n/p) else 0)=
      ∑ d ∈ Finset.Icc 1 (N/p), f d := by
  let src := Finset.Icc 1 (N/p)
  have eq : (Finset.Icc 1 N).filter (fun n => p∣n)=src.image (fun d => d*p) := by
    ext n
    constructor
    · intro hn
      obtain ⟨h,hit⟩ := Finset.mem_filter.mp hn
      have dn := Nat.div_mul_cancel hit
      refine Finset.mem_image.mpr ⟨n/p,Finset.mem_Icc.mpr ⟨?_,Nat.div_le_div_right (Finset.mem_Icc.mp h).2⟩,dn⟩
      exact Nat.div_pos (Nat.le_of_dvd (Finset.mem_Icc.mp h).1 hit) hp
    · intro h
      obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp h
      obtain ⟨low,top⟩ := Finset.mem_Icc.mp hd
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.mul_pos low hp,(Nat.le_div_iff_mul_le hp).mp top⟩,
        dvd_mul_left p d⟩
  rw [←Finset.sum_filter,eq,Finset.sum_image (fun _ _ _ _ h => Nat.eq_of_mul_eq_mul_right hp h)]
  exact Finset.sum_congr rfl (fun _ _ => congrArg f (Nat.mul_div_cancel _ hp))

theorem observe_insert {p : ℕ} (hp : 0<p) (f : ℕ → ℝ) (x : ℝ) :
    observe (insertAt p f) x=observe f (x/p)/p := by
  let term := fun d : ℕ => (f d/((d*p:ℕ):ℝ))*edge (x/(d*p:ℕ))
  have point (n : ℕ) (_ : n∈Finset.Icc 1 ⌊2*x⌋₊) :
      insertAt p f n/n*edge (x/n)=(if p∣n then term (n/p) else 0) := by
    by_cases hit : p∣n
    · simp only [insertAt,hit,if_true,term,Nat.div_mul_cancel hit]
    · simp [insertAt,hit]
  rw [observe,Finset.sum_congr rfl point,collect_multiples _ _ hp,observe,
    show 2*(x/p)=2*x/p by ring,Nat.floor_div_natCast,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d _
  dsimp only [term]
  rw [Nat.cast_mul,show x/((d:ℝ)*p)=(x/p)/d by ring]
  rw [div_mul_eq_div_div]
  ring

private theorem observe_linear (f g : ℕ → ℝ) (a : ℝ) (x : ℝ) :
    observe (fun n => f n-a*g n) x=observe f x-a*observe g x := by
  unfold observe
  rw [Finset.mul_sum,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  ring

def plain (n : ℕ) : ℝ := if 2∣n then -1 else 1
def rough (n : ℕ) : ℝ := TaperedNewton.allowed n
def signed (n : ℕ) : ℝ := rough n-2*insertAt 2 rough n

theorem actual_pulse {x : ℝ} (xp : 0<x) : observe signed x=AlternatingRead.pulse x := by
  unfold signed
  rw [observe_linear,observe_insert (by decide : 0<2)]
  change observe (fun n => (TaperedNewton.allowed n:ℝ)) x-
    2*(observe (fun n => (TaperedNewton.allowed n:ℝ)) (x/2)/2)=_
  rw [rough_dilation xp,rough_dilation (by positivity)]
  have eq : 1/(x/2)=2/x := by ring
  rw [eq,AlternatingRead.pulse]
  ring

theorem mask (n : ℕ) : signed n=plain n-insertAt 2 plain n-insertAt 3 plain n+insertAt 6 plain n := by
  have gate (d : ℕ) : rough d=if 2∣d ∨ 3∣d then 0 else 1 := by
    have c : d.Coprime 6 ↔ d.Coprime 2 ∧ d.Coprime 3 := by
      change d.Coprime (2*3) ↔ _
      exact Nat.coprime_mul_iff_right
    have a : d.Coprime 2 ↔ ¬2∣d := Nat.coprime_comm.trans Nat.prime_two.coprime_iff_not_dvd
    have b : d.Coprime 3 ↔ ¬3∣d := Nat.coprime_comm.trans Nat.prime_three.coprime_iff_not_dvd
    change ((TaperedNewton.allowed d:ℚ):ℝ)=_
    rw [show TaperedNewton.allowed d=(if d.Coprime 6 then (1:ℚ) else 0) by rfl]
    by_cases two : 2∣d <;> by_cases three : 3∣d <;> simp [c,a,b,two,three]
  simp only [signed,gate,insertAt,plain]
  split_ifs <;> norm_num <;> omega

def read (f : ℕ → ℝ) (s : ℂ) (v : ℝ) : ℂ :=
  (v:ℂ)^s*∑ n ∈ Finset.Icc 1 ⌊v⌋₊, (n:ℂ)^(-s)*(f n:ℂ)

theorem read_insert {p : ℕ} (hp : 0<p) (f : ℕ → ℝ) (s : ℂ) {v : ℝ} (vp : 0<v) :
    read (insertAt p f) s v=read f s (v/p) := by
  let term := fun d : ℕ => ((d*p:ℕ):ℂ)^(-s)*(f d:ℂ)
  have point (n : ℕ) (_ : n∈Finset.Icc 1 ⌊v⌋₊) :
      (n:ℂ)^(-s)*(insertAt p f n:ℂ)=if p∣n then term (n/p) else 0 := by
    by_cases hit : p∣n
    · simp only [insertAt,hit,if_true,term,Nat.div_mul_cancel hit]
    · simp [insertAt,hit]
  rw [read,Finset.sum_congr rfl point,collect_multiples _ _ hp,read,Nat.floor_div_natCast]
  have pv : 0<(p:ℝ) := by exact_mod_cast hp
  rw [Complex.ofReal_div,Complex.div_cpow_ofReal_nonneg vp.le pv.le,Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  dsimp only [term]
  rw [show ((d*p:ℕ):ℂ)=(((d:ℝ)*(p:ℝ):ℝ):ℂ) by push_cast;rfl,Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (by positivity : (0:ℝ)≤d) pv.le]
  simp only [Complex.ofReal_natCast,Complex.cpow_neg (p:ℂ) s]
  ring

private theorem read_plain (s : ℂ) (v : ℝ) : read plain s v=AlternatingRead.response s v := by
  unfold read AlternatingRead.response AlternatingRead.alternating
  congr 1
  have strip : Finset.Icc 0 ⌊v⌋₊=insert 0 (Finset.Icc 1 ⌊v⌋₊) := by
    ext n;simp only [Finset.mem_insert,Finset.mem_Icc];omega
  rw [strip,Finset.sum_insert (by simp)]
  simp only [AlternatingRead.jump,AlternatingRead.digit,Nat.zero_sub,Nat.zero_mod,Nat.cast_zero,
    sub_self,mul_zero,zero_add]
  apply Finset.sum_congr rfl
  intro n hn
  have pos := (Finset.mem_Icc.mp hn).1
  by_cases yes : 2∣n
  · simp [plain,yes,show n%2=0 by omega,show (n-1)%2=1 by omega]
  · simp [plain,yes,show n%2=1 by omega,show (n-1)%2=0 by omega]

theorem signed_bound {s : ℂ} (sp : 0<s.re) (except : s≠1) (zero : riemannZeta s=0)
    {v : ℝ} (vp : 0<v) : ‖read signed s v‖≤4*(1+‖s‖/s.re) := by
  have unit (y : ℝ) : ‖read plain s y‖≤1+‖s‖/s.re := by
    by_cases large : 1≤y
    · rw [read_plain]
      exact AlternatingRead.bounded_at_zero sp except zero large
    · simp [read,Nat.floor_eq_zero.mpr (lt_of_not_ge large)]
      positivity
  have expand : read signed s v=read plain s v-read (insertAt 2 plain) s v-
        read (insertAt 3 plain) s v+read (insertAt 6 plain) s v := by
    unfold read
    simp only [mask,Complex.ofReal_add,Complex.ofReal_sub,mul_add,mul_sub,
      Finset.sum_add_distrib,Finset.sum_sub_distrib]
  rw [expand,read_insert (by decide : 0<2) _ _ vp,read_insert (by decide : 0<3) _ _ vp,
    read_insert (by decide : 0<6) _ _ vp]
  have t := norm_add_le (read plain s v-read plain s (v/2)-read plain s (v/3)) (read plain s (v/6))
  have u := norm_sub_le (read plain s v-read plain s (v/2)) (read plain s (v/3))
  have w := norm_sub_le (read plain s v) (read plain s (v/2))
  linarith [unit v,unit (v/2),unit (v/3),unit (v/6)]

#print axioms PALRH.CensusTransfer.actual_pulse
#print axioms PALRH.CensusTransfer.signed_bound
end PALRH.CensusTransfer
