import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

open Finset
open scoped BigOperators

namespace PALRH.PhaseBound

/-- Summation by parts for a carried phase. No distribution hypothesis enters this identity. -/
theorem transfer (a z ratio : ℕ → ℂ) (step : ∀ i, z (i+1)=ratio i*z i) (N : ℕ) :
    (∑ i ∈ range N,a i*(ratio i-1)*z i)=
      a N*z N-a 0*z 0+∑ i ∈ range N,(a i-a (i+1))*z (i+1) := by
  induction N with
  | zero => simp
  | succ N ih => rw [sum_range_succ,sum_range_succ,ih,step N];ring

/-- A varying weight off resonance prices an ordinary sum of the original phases. -/
theorem off_resonance (a z ratio : ℕ → ℂ) (step : ∀ i, z (i+1)=ratio i*z i)
    (unit : ∀ i, ‖z i‖=1) (N : ℕ) (normal : ∀ i<N, a i*(ratio i-1)=1) :
    ‖∑ i ∈ range N,z i‖≤‖a N‖+‖a 0‖+∑ i ∈ range N,‖a i-a (i+1)‖ := by
  have id:=transfer a z ratio step N
  have same : (∑ i ∈ range N,a i*(ratio i-1)*z i)=∑ i ∈ range N,z i := by
    apply sum_congr rfl;intro i hi;rw [normal i (mem_range.mp hi),one_mul]
  rw [same] at id
  rw [id]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · simpa only [norm_mul,unit,mul_one] using norm_sub_le (a N*z N) (a 0*z 0)
  · simpa only [norm_mul,unit,mul_one] using
      (norm_sum_le (range N) (fun i => (a i-a (i+1))*z (i+1)))

/-- If the observed arc leaves a gap wider than any real step, a trajectory from zero
cannot change its integer lift while staying in the observed arc. -/
theorem arc_lift {M : ℕ} {period radius : ℤ} {z : ℕ → ℤ} (rp : 0≤radius)
    (pp : 0<period) (origin : z 0=0)
    (speed : ∀ i<M, |z (i+1)-z i|+2*radius<period)
    (arc : ∀ i≤M, ∃ k : ℤ, |z i-k*period|≤radius) : ∀ i≤M, |z i|≤radius := by
  intro i
  induction i with
  | zero => intro _;simpa only [origin,abs_zero] using rp
  | succ i ih =>
    intro seen
    have old:=ih (by omega)
    obtain ⟨k,near⟩:=arc (i+1) seen
    have change:=speed i (by omega)
    by_cases reset : k=0
    · simpa only [reset,zero_mul,sub_zero] using near
    have nz : 1≤|k| := by
      rcases le_total 0 k with p|p
      · rw [abs_of_nonneg p];omega
      · rw [abs_of_nonpos p];omega
    have multiple : period≤|k*period| := by
      rw [abs_mul,abs_of_pos pp];simpa using mul_le_mul_of_nonneg_right nz pp.le
    have dist : |k*period|≤|z (i+1)-k*period|+|z (i+1)-z i|+|z i| := by
      calc
        _ = |(k*period-z (i+1))+(z (i+1)-z i)+z i| := by ring_nf
        _ ≤ |(k*period-z (i+1))+(z (i+1)-z i)|+|z i| := abs_add_le _ _
        _ ≤ _ := by rw [abs_sub_comm (z (i+1)) (k*period)];exact add_le_add_left (abs_add_le (k*period-z (i+1)) (z (i+1)-z i)) |z i|
    omega

theorem modular_witness {z period radius : ℤ} (pp : 0<period)
    (near : z%period≤radius ∨ period-radius≤z%period) :
    ∃ k : ℤ, |z-k*period|≤radius := by
  have eq:=Int.emod_add_mul_ediv z period
  have lo:=Int.emod_nonneg z pp.ne'
  have hi:=Int.emod_lt_of_pos z pp
  rcases near with left|right
  · refine ⟨z/period,?_⟩
    rw [show z-(z/period)*period=z%period by nlinarith only [eq],abs_of_nonneg lo];exact left
  · refine ⟨z/period+1,?_⟩
    rw [show z-(z/period+1)*period=z%period-period by nlinarith only [eq],abs_of_nonpos (by omega : z%period-period≤0)]
    omega

#print axioms PALRH.PhaseBound.transfer
#print axioms PALRH.PhaseBound.off_resonance
#print axioms PALRH.PhaseBound.arc_lift
end PALRH.PhaseBound
