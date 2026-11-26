import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Log.Basic

noncomputable section
namespace PALRH.CentralMirror
open Complex

def phi : ℝ := (1+Real.sqrt 5)/2

def side (s : ℂ) := Complex.exp ((s-1/2)*(Real.log 5:ℝ))
def completion (t s : ℂ) := (side s+(side s)⁻¹+t)*completedRiemannZeta s

theorem same_mirror (t s : ℂ) : completion t (1-s)=completion t s := by
  have change : side (1-s)=(side s)⁻¹ := by
    unfold side
    rw [show (1-s-1/2)*(Real.log 5:ℝ)= -((s-1/2)*(Real.log 5:ℝ)) by ring,Complex.exp_neg]
  rw [completion,completion,change,inv_inv,completedRiemannZeta_one_sub];ring

def outsidePoint : ℂ := ((1/2+Real.log phi/Real.log 5 : ℝ):ℂ)+
  ((Real.pi/Real.log 5:ℝ):ℂ)*I

theorem displaced : 1/2<outsidePoint.re ∧ outsidePoint.re<1 := by
  have root := Real.sq_sqrt (by norm_num : (0:ℝ)≤5)
  have p1 : 1<phi := by dsimp [phi];nlinarith [Real.sqrt_nonneg 5]
  have psmall : phi<Real.sqrt 5 := by dsimp [phi];nlinarith [Real.sqrt_nonneg 5]
  have ll:=Real.log_lt_log (zero_lt_one.trans p1) psmall
  rw [Real.log_sqrt (by norm_num)] at ll
  have denom:=Real.log_pos (by norm_num : (1:ℝ)<5)
  have shift : Real.log phi/Real.log 5<1/2 := (div_lt_iff₀ denom).mpr (by linarith)
  have center : outsidePoint.re=1/2+Real.log phi/Real.log 5 := by
    simp only [outsidePoint,Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero]
  rw [center];constructor <;> linarith [div_pos (Real.log_pos p1) denom]

theorem factor_vanishes : side outsidePoint+(side outsidePoint)⁻¹+(Real.sqrt 5:ℂ)=0 := by
  have rp : 0<phi := by dsimp [phi];positivity
  have ln : (Real.log 5:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.log_pos (by norm_num)).ne'
  have eq : (outsidePoint-1/2)*(Real.log 5:ℝ)=(Real.log phi:ℝ)+(Real.pi:ℝ)*I := by
    dsimp [outsidePoint];push_cast;field_simp;ring
  have sp : side outsidePoint = -(phi:ℂ) := by
    rw [side,eq,Complex.exp_add,Complex.exp_pi_mul_I,←Complex.ofReal_exp,Real.exp_log rp];ring
  have gold : phi^2-(Real.sqrt 5)*phi+1=0 := by
    dsimp [phi];nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤5)]
  have cast : (phi:ℂ)^2-(Real.sqrt 5:ℂ)*phi+1=0 := by exact_mod_cast gold
  rw [sp]
  field_simp [Complex.ofReal_ne_zero.mpr rp.ne']
  linear_combination -cast

theorem off_center_zero : completion (Real.sqrt 5:ℂ) outsidePoint=0 := by
  rw [completion,factor_vanishes,zero_mul]

/-- The unnormalized integer transfer multiplies this quadratic form by five. -/
def length (a x y : ℝ) := x^2-a*x*y+5*y^2

theorem transfer (a x y : ℝ) : length a (-5*y) (x-a*y)=5*length a x y := by
  dsimp [length];ring

theorem four_length (x y : ℝ) : length 4 x y=(x-2*y)^2+y^2 := by
  dsimp [length];ring

theorem five_witness : length 5 2 1= -1 := by norm_num [length]

#print axioms PALRH.CentralMirror.same_mirror
#print axioms PALRH.CentralMirror.off_center_zero
#print axioms PALRH.CentralMirror.displaced
#print axioms PALRH.CentralMirror.transfer
end PALRH.CentralMirror
