import Formalism.LocalToGlobal.LatticeGeometry.Inhabited
import Formalism.SharpRestriction.Divisibility.HeightShare
import Formalism.DegreeFormula.PointDegree.FlagDeg
import Formalism.LocalToGlobal.LatticeGeometry.PluckerHadamard.WeylPolynomialAlgebra

/-!
Counterexamples and a comparison theorem at the unmodified 20 November release types.
Tested with Lean 4.33.1 and the dependency revisions pinned by that release.
-/
noncomputable section
namespace RHRedteam.FlagGrowth

open Formalism.DegreeFormula Formalism.L2.Geo Formalism.MainNotions.HeightShare

abbrev model := geoDegenerate ℚ (Fin 2)

def weight (a b : ℤ) (copy i : Fin 2) : ℤ :=
  if i = 0 then (if copy = 0 then a else b) else 0

private theorem dimension : dimFl (Fin 2) 2 = 2 := by norm_num [dimFl]

private theorem self_degree (a b : ℤ) :
    ((model.inter 2 (fun _ => weight a b) : ℤ) : ℝ) = 2 * (a : ℝ) * (b : ℝ) := by
  rw [geoFl_inter, flagDegFormula_statement]
  norm_num [dimension, weylProd, weight, Fin.prod_univ_two]
  ring

/-- The second divisor drops out in the supplied two-dimensional operation. -/
theorem first_slot (a b c d : ℤ) :
    ((model.inter 2 (fun i => if i.val = 0 then weight a b else weight c d) : ℤ) : ℝ) =
      2 * (a : ℝ) * (b : ℝ) := by
  have h : 0 < dimFl (Fin 2) 2 := by rw [dimension]; decide
  have heq : model.inter 2 (fun i => if i.val = 0 then weight a b else weight c d) =
      model.inter 2 (fun _ => weight a b) := by
    simp [h]
  rw [heq, self_degree]

/-- The weight of bidegree (1,0) has square zero and the model declares it big. -/
theorem nonzero_ruling_breaks_nef_criterion : ¬ GloballyGeneratedNef model := by
  intro h
  have hpos := (h.2.1 2 (weight 1 0) (by trivial)).mp (by trivial)
  have hz : model.inter 2 (fun _ => weight 1 0) = 0 := by
    exact_mod_cast (show ((model.inter 2 (fun _ => weight 1 0) : ℤ) : ℝ) = 0 by
      rw [self_degree]; norm_num)
  rw [hz] at hpos
  exact (lt_irrefl (0 : ℤ)) hpos

/-- The space of sections stays one-dimensional as the (1,1) weight is scaled. -/
theorem positive_weight_breaks_section_growth : ¬ AsymptoticRiemannRoch model := by
  intro h
  have hd : model.dim 2 = 2 := dimension
  obtain ⟨C, bound⟩ := h 2 (weight 1 1) (by rw [hd]; decide) (by trivial)
  obtain ⟨t, ht⟩ := exists_nat_gt (|C| + 2)
  have ht2 : (2 : ℝ) < t := by linarith [abs_nonneg C]
  have ht1 : 1 ≤ t := by exact_mod_cast (show (1 : ℝ) ≤ t by linarith)
  have rank_one : Module.finrank ℚ (model.H0 2 (t • weight 1 1)) = 1 := by
    change Module.finrank ℚ (⊤ : Submodule ℚ ℚ) = 1
    simp
  have hdeg : ((model.inter 2 (fun _ => weight 1 1) : ℤ) : ℝ) = 2 := by
    rw [self_degree]; norm_num
  have err := bound t ht1
  rw [rank_one, hdeg, hd] at err
  norm_num [Nat.factorial] at err
  have below := (abs_le.mp err).1
  have gap : (1 : ℝ) < (t : ℝ) - C := by linarith [le_abs_self C]
  have product := mul_lt_mul_of_pos_right gap (show (0 : ℝ) < t by linarith)
  nlinarith

theorem fails_height_share_admissibility : ¬ AdmG model := by
  rintro ⟨_, _, _, _, _, growth, _⟩
  exact positive_weight_breaks_section_growth growth

open Formalism.L2.Geo.WeylPolynomialAlgebra

private def regularWeight (_ : Fin 1) (i : Fin 3) : ℝ := 2 - (i.val : ℝ)

/-- The mixed coefficient used by the positivity branch of the released proof. -/
theorem polarized_flag_degree (ν : Fin 1 → Fin 3 → ℝ) :
    degFlL (Fin 1) 3 (a0Mu (Ψ := Fin 1) (N := 3) 1 ^ 2 * linRoot ν) = ν 0 1 - ν 0 2 := by
  have hs : idxS (Fin 1) 3 1 = {((0, 1, 2) : Fin 1 × Fin 3 × Fin 3)} := by
    ext ⟨t, i, j⟩
    fin_cases t
    fin_cases i <;> fin_cases j <;> norm_num [idxS] <;> decide
  have hc : idxC (Fin 1) 3 1 = {((0, 0, 1) : Fin 1 × Fin 3 × Fin 3), (0, 0, 2)} := by
    ext ⟨t, i, j⟩
    fin_cases t
    fin_cases i <;> fin_cases j <;> norm_num [idxC] <;> decide
  have mix := weyl_coeff 1 ν 2 1 (by norm_num [dimFl]) (by simp [hs])
  rw [hs, hc] at mix
  norm_num [dimFl, Nat.factorial, Nat.choose] at mix
  linarith

theorem mixed_example :
    degFlL (Fin 1) 3 (a0Mu (Ψ := Fin 1) (N := 3) 1 ^ 2 * linRoot regularWeight) = 1 := by
  rw [polarized_flag_degree]
  norm_num [regularWeight]

#print axioms polarized_flag_degree
#print axioms mixed_example
#print axioms fails_height_share_admissibility
#print axioms first_slot
#print axioms nonzero_ruling_breaks_nef_criterion
#print axioms positive_weight_breaks_section_growth
end RHRedteam.FlagGrowth
