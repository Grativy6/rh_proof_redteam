import PALRH.PrimeDivisorPrimitive
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

open Finset MeasureTheory
open scoped BigOperators Interval

noncomputable section
namespace PALRH.LogPrimitive
open PrimeDivisorPrimitive PositivePrimitive

/-- Density of the contribution of one prime-power label to the logarithmic primitive. -/
def single (d : ℕ) (t : ℝ) := max 0 (t-d)/(max (d:ℝ) t)^2

def halfstep : ℝ → ℝ := (Set.Ici (1:ℝ)).indicator (fun _ => 1/2)
def density (t : ℝ) : ℝ := value t/t
def primitive (x : ℝ) : ℝ := ∫ t in (0:ℝ)..x, density t

private theorem single_cont {d : ℕ} (dp : 0<d) : Continuous (single d) := by
  unfold single
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro t
  exact pow_ne_zero _ (ne_of_gt (lt_of_lt_of_le (by exact_mod_cast dp) (le_max_left _ t)))

private theorem step_mono : Monotone halfstep := by
  intro a b ab
  by_cases h : 1≤a
  · simp [halfstep,Set.mem_Ici,h,h.trans ab]
  · by_cases hb : 1≤b <;> simp [halfstep,Set.mem_Ici,h,hb]

private theorem density_finite {t X : ℝ} (tn : 0≤t) (small : t≤X) :
    density t=(∑ d ∈ Icc 1 ⌊X⌋₊,ArithmeticFunction.vonMangoldt d*single d t)-halfstep t := by
  have same : (∑ d ∈ Icc 1 ⌊t⌋₊,ArithmeticFunction.vonMangoldt d*(1-d/t))/t =
      ∑ d ∈ Icc 1 ⌊X⌋₊,ArithmeticFunction.vonMangoldt d*single d t := by
    rw [Finset.sum_div]
    calc
      _ = ∑ d ∈ Icc 1 ⌊t⌋₊,ArithmeticFunction.vonMangoldt d*single d t := by
        apply Finset.sum_congr rfl
        intro d hd
        have dr : (d:ℝ)≤t := (Nat.le_floor_iff tn).mp (mem_Icc.mp hd).2
        have dp : 0<(d:ℝ) := by exact_mod_cast (mem_Icc.mp hd).1
        have pos:=dp.trans_le dr
        rw [single,max_eq_right (sub_nonneg.mpr dr),max_eq_right dr]
        field_simp
      _ = _ := by
        apply Finset.sum_subset (fun i hi => mem_Icc.mpr ⟨(mem_Icc.mp hi).1,(mem_Icc.mp hi).2.trans (Nat.floor_mono small)⟩)
        intro d hd out
        have late : t<(d:ℝ) := (Nat.floor_lt tn).mp (lt_of_not_ge (fun h => out (mem_Icc.mpr ⟨(mem_Icc.mp hd).1,h⟩)))
        simp [single,max_eq_left (sub_nonpos.mpr late.le)]
  unfold density value
  rw [sub_div,same]
  by_cases hi : 1≤t
  · have tp : t≠0 := by linarith
    simp [halfstep,Set.mem_Ici,hi]
    field_simp
  · simp [halfstep,Set.mem_Ici,hi]

theorem density_int {a b : ℝ} (an : 0≤a) (ab : a≤b) : IntervalIntegrable density volume a b := by
  have each (i : ℕ) (hi : i∈Icc 1 ⌊b⌋₊) :
      IntervalIntegrable (fun t => ArithmeticFunction.vonMangoldt i*single i t) volume a b :=
    ((single_cont (mem_Icc.mp hi).1).intervalIntegrable a b).const_mul _
  have summed:=IntervalIntegrable.sum _ each
  have both:=summed.sub (step_mono.intervalIntegrable (a:=a) (b:=b))
  apply IntervalIntegrable.congr _ both
  intro t ht
  rw [Set.uIoc_of_le ab] at ht
  simpa [Pi.sub_apply,Finset.sum_apply] using (density_finite (an.trans ht.1.le) ht.2).symm

private theorem single_zero {d : ℕ} {t : ℝ} (hd : t≤d) : single d t=0 := by
  simp [single,max_eq_left (sub_nonpos.mpr hd)]

private theorem single_integral {d : ℕ} (dp : 0<d) {x : ℝ} (xp : 0≤x) :
    (∫ t in (0:ℝ)..x,single d t)=if (d:ℝ)≤x then Real.log (x/d)-1+d/x else 0 := by
  have dr : 0<(d:ℝ) := by exact_mod_cast dp
  have cont:=single_cont dp
  have zero {y : ℝ} (yn : 0≤y) (yd : y≤d) : (∫ t in (0:ℝ)..y,single d t)=0 := by
    calc
      _ = ∫ _ in (0:ℝ)..y,(0:ℝ) := intervalIntegral.integral_congr (fun t ht => by
        rw [Set.uIcc_of_le yn] at ht;exact single_zero (ht.2.trans yd))
      _ = _ := by simp
  by_cases inside : (d:ℝ)≤x
  · rw [if_pos inside,←intervalIntegral.integral_add_adjacent_intervals (cont.intervalIntegrable 0 d)
      (cont.intervalIntegrable (d:ℝ) x),zero dr.le le_rfl,zero_add]
    have der : ∀ t ∈ Set.uIcc (d:ℝ) x,
        HasDerivAt (fun t : ℝ => Real.log t+(d:ℝ)/t) (single d t) t := by
      intro t ht
      rw [Set.uIcc_of_le inside] at ht
      have tp:=dr.trans_le ht.1
      have h:=(Real.hasDerivAt_log tp.ne').add ((hasDerivAt_const t (d:ℝ)).div (hasDerivAt_id t) tp.ne')
      have same : single d t=t⁻¹+(0*t-(d:ℝ)*1)/t^2 := by
        rw [single,max_eq_right (sub_nonneg.mpr ht.1),max_eq_right ht.1]
        field_simp
        ring
      rw [same]
      exact h
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt der (cont.intervalIntegrable _ _),
      Real.log_div (dr.trans_le inside).ne' dr.ne',div_self dr.ne']
    ring
  · rw [if_neg inside,zero xp (le_of_not_ge inside)]

private theorem step_integral {x : ℝ} (large : 1≤x) : (∫ t in (0:ℝ)..x,halfstep t)=(x-1)/2 := by
  rw [intervalIntegral.integral_of_le (zero_le_one.trans large),halfstep,
    MeasureTheory.integral_indicator measurableSet_Ici,Measure.restrict_restrict measurableSet_Ici]
  have eq : Set.Ici (1:ℝ)∩Set.Ioc 0 x=Set.Icc 1 x := by
    ext z
    simp only [Set.mem_inter_iff,Set.mem_Ici,Set.mem_Ioc,Set.mem_Icc]
    constructor <;> rintro h <;> exact ⟨h.1,by first | exact h.2.2 | exact ⟨by linarith only [h.1],h.2⟩⟩
  rw [eq,MeasureTheory.integral_const]
  simp [Measure.real,Real.volume_Icc,ENNReal.toReal_ofReal (sub_nonneg.mpr large),smul_eq_mul]
  ring

theorem exact_value {x : ℝ} (large : 1≤x) :
    primitive x=(∑ d ∈ Icc 1 ⌊x⌋₊,ArithmeticFunction.vonMangoldt d*(Real.log (x/d)-1+d/x))-(x-1)/2 := by
  have xp:=zero_le_one.trans large
  let S:=Icc 1 ⌊x⌋₊
  have ci d (hd : d∈S) : IntervalIntegrable (fun t => ArithmeticFunction.vonMangoldt d*single d t) volume 0 x := ((single_cont (mem_Icc.mp hd).1).intervalIntegrable 0 x).const_mul
    (ArithmeticFunction.vonMangoldt d)
  unfold primitive
  calc
    _ = ∫ t in (0:ℝ)..x, (∑ d ∈ S,ArithmeticFunction.vonMangoldt d*single d t)-halfstep t := by
      apply intervalIntegral.integral_congr
      intro t ht;rw [Set.uIcc_of_le xp] at ht
      exact density_finite ht.1 ht.2
    _ = _ := by
      have isum:=IntervalIntegrable.sum S ci
      have point : (∑ d ∈ S,fun t : ℝ => ArithmeticFunction.vonMangoldt d*single d t)=
          (fun t => ∑ d ∈ S,ArithmeticFunction.vonMangoldt d*single d t) := by
        funext t;simp
      rw [point] at isum
      rw [intervalIntegral.integral_sub isum (step_mono.intervalIntegrable (a:=0) (b:=x)),
        intervalIntegral.integral_finsetSum ci,step_integral large]
      congr 1
      apply Finset.sum_congr rfl
      intro d hd
      rw [intervalIntegral.integral_const_mul,single_integral (mem_Icc.mp hd).1 xp,
        if_pos ((Nat.le_floor_iff xp).mp (mem_Icc.mp hd).2)]

end PALRH.LogPrimitive
