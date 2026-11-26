import PALRH.DysonOctave

open Complex Finset
open scoped BigOperators Interval

noncomputable section
namespace PALRH.DysonObservation
open DysonOctave

def boxResponse (z : ℂ) : ℂ :=
  ∫ t in (0:ℝ)..Real.log 2, Complex.exp (z*t)

def transform (z : ℂ) : ℂ := boxResponse z*boxResponse (-z)

private theorem box_value {z : ℂ} (nz : z≠0) : boxResponse z=(octave z-1)/z := by
  rw [boxResponse,integral_exp_mul_complex nz]
  simp only [Complex.ofReal_zero,mul_zero,Complex.exp_zero]
  rw [octave,mul_comm z]

theorem transform_price {z : ℂ} (nz : z≠0) : transform z=kernel z := by
  rw [transform,box_value nz,box_value (neg_ne_zero.mpr nz)]
  have back : octave (-z)=(octave z)⁻¹ := by simp only [octave,mul_neg,Complex.exp_neg]
  rw [back,kernel]
  have en : octave z≠0 := Complex.exp_ne_zero _
  field_simp
  ring

theorem transform_origin : transform 0=((Real.log 2)^2:ℝ) := by
  simp [transform,boxResponse,pow_two]

theorem right_kept {z : ℂ} (right : 0<z.re) : transform z≠0 := by
  have nz : z≠0 := by intro zero;simp [zero] at right
  rw [transform_price nz]
  exact kernel_ne_zero right

theorem critical_energy (g : ℝ) :
    transform ((g:ℂ)*I)=(‖boxResponse ((g:ℂ)*I)‖^2:ℝ) := by
  let z:ℂ:=(g:ℂ)*I
  change transform z=_
  by_cases zero : z=0
  · change transform z=((‖boxResponse z‖^2:ℝ):ℂ)
    rw [zero,transform_origin]
    have bz : boxResponse 0=((Real.log (2:ℝ):ℝ):ℂ) := by simp [boxResponse]
    rw [bz,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.log_pos (by norm_num : (1:ℝ)<2))]
  have conjz : star z= -z := by simp [z]
  have other : boxResponse (-z)=star (boxResponse z) := by
    rw [box_value (neg_ne_zero.mpr zero),box_value zero]
    have e : star (octave z)=octave (-z) := by
      unfold octave
      change (starRingEnd ℂ) (Complex.exp ((Real.log 2:ℝ)*z))=_
      rw [←Complex.exp_conj,map_mul,Complex.conj_ofReal]
      change Complex.exp ((Real.log 2:ℝ)*star z)=_
      rw [conjz]
    simp [e,conjz]
  rw [transform,other]
  change boxResponse z*star (boxResponse z)=((‖boxResponse z‖^2:ℝ):ℂ)
  simpa [Complex.sq_norm] using Complex.mul_conj (boxResponse z)

theorem reference_value : kernel (1/2)=(referenceSlope:ℂ) := by
  let L:=Real.log 2
  have sqr : (Real.exp (L/2))^2=2 := by
    rw [sq,←Real.exp_add,show L/2+L/2=L by ring,Real.exp_log (by norm_num : (0:ℝ)<2)]
  have er : Real.exp (L/2)=Real.sqrt 2 := by
    calc
      _ = Real.sqrt ((Real.exp (L/2))^2) := (Real.sqrt_sq (Real.exp_pos _).le).symm
      _ = _ := congrArg Real.sqrt sqr
  have obs : octave (1/2)=(Real.sqrt 2:ℝ) := by
    unfold octave
    rw [←er,Complex.ofReal_exp]
    congr 1
    dsimp [L]
    push_cast;ring
  rw [kernel,obs]
  unfold referenceSlope
  push_cast
  have rt : ((Real.sqrt 2:ℝ):ℂ)≠0 := by exact_mod_cast (Real.sqrt_pos_of_pos (by norm_num : (0:ℝ)<2)).ne'
  field_simp
  ring

/-- The omission of repeated powers at the first square is exactly the contribution of four. -/
theorem first_square_price : fullReading 2-primeReading 2=(Real.log 2)^2/2 := by
  let w := fun n : ℕ => 1/Real.sqrt n * max 0 (Real.log 2-|Real.log ((n:ℝ)/4)|)
  have split : fullReading 2-primeReading 2 =
      ∑ n ∈ Icc 1 8, if n.Prime then 0 else ArithmeticFunction.vonMangoldt n*w n := by
    unfold fullReading primeReading
    norm_num only [Nat.reducePow,Nat.reduceMul,Nat.cast_ofNat,OfNat.ofNat]
    rw [←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases p : n.Prime
    · rw [if_pos p,if_pos p,ArithmeticFunction.vonMangoldt_apply_prime p,sub_self]
    · rw [if_neg p,if_neg p,sub_zero]
      dsimp [w]
      ring
  rw [split]
  have four : ArithmeticFunction.vonMangoldt 4=Real.log 2 := by
    rw [show (4:ℕ)=2^2 by decide,ArithmeticFunction.vonMangoldt_apply_pow (by decide),ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    norm_num
  have six : ArithmeticFunction.vonMangoldt 6=0 := ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr (by decide)
  have w4 : w 4=Real.log 2/2 := by
    dsimp [w]
    norm_num [max_eq_right (Real.log_pos (by norm_num : (1:ℝ)<2)).le]
    ring
  have w8 : w 8=0 := by
    dsimp [w]
    norm_num [abs_of_pos (Real.log_pos (by norm_num : (1:ℝ)<2))]
  have eqset : Icc (1:ℕ) 8={1,2,3,4,5,6,7,8} := by decide
  rw [eqset]
  norm_num [four,six,w4,w8,ArithmeticFunction.vonMangoldt_apply_one]
  ring

#print axioms PALRH.DysonObservation.transform_price
#print axioms PALRH.DysonObservation.right_kept
#print axioms PALRH.DysonObservation.critical_energy
#print axioms PALRH.DysonObservation.reference_value
#print axioms PALRH.DysonObservation.first_square_price
end PALRH.DysonObservation
