import Formalism.LocalToGlobal.LatticeGeometry.Inhabited
import Formalism.SharpRestriction.Divisibility.HeightShare
import Formalism.DegreeFormula.PointDegree.FlagDeg

/-! The section-growth obstruction on any nonempty finite product of rank-two flags. -/
noncomputable section
namespace RHRedteam.GeneralFlagGrowth

open Formalism.DegreeFormula Formalism.L2.Geo Formalism.MainNotions.HeightShare

theorem no_asymptotic_riemann_roch (K ι : Type) [Field K] [NumberField K] [StarRing K]
    [Fintype ι] [Nonempty ι] : ¬ AsymptoticRiemannRoch (geoDegenerate K ι) := by
  classical
  let m := Fintype.card ι
  let G := geoDegenerate K ι
  let L : ι → Fin 2 → ℤ := fun _ i => if i = 0 then 1 else 0
  have hm : 0 < m := Fintype.card_pos
  have hd : G.dim 2 = m := by
    change dimFl ι 2 = m
    norm_num [dimFl, m]
  have deg : ((G.inter 2 (fun _ => L) : ℤ) : ℝ) = m.factorial := by
    rw [geoFl_inter, flagDegFormula_statement]
    norm_num [weylProd, Fin.prod_univ_two, L, dimFl, m]
  intro h
  obtain ⟨C, bounds⟩ := h 2 L (by change 1 ≤ G.dim 2; rw [hd]; omega) (by trivial)
  obtain ⟨t, ht⟩ := exists_nat_gt (|C| + 2)
  have ht2 : (2 : ℝ) < t := by linarith [abs_nonneg C]
  have ht1 : 1 ≤ t := by exact_mod_cast (show (1 : ℝ) ≤ t by linarith)
  have rank_one : Module.finrank K (G.H0 2 (t • L)) = 1 := by
    change Module.finrank K (⊤ : Submodule K K) = 1
    simp
  have err := bounds t ht1
  change |(Module.finrank K (G.H0 2 (t • L)) : ℝ) -
    (G.inter 2 (fun _ => L) : ℝ) * (t : ℝ) ^ G.dim 2 / ((G.dim 2).factorial : ℝ)| ≤
    C * (t : ℝ) ^ (G.dim 2 - 1) at err
  rw [rank_one, deg, hd] at err
  have hf : (m.factorial : ℝ) ≠ 0 := by positivity
  have cancel : (m.factorial : ℝ) * (t : ℝ) ^ m / (m.factorial : ℝ) = (t : ℝ) ^ m := by field_simp
  rw [cancel, Nat.cast_one] at err
  have split_pow : (t : ℝ) ^ m = (t : ℝ) ^ (m - 1) * t := by
    calc
      (t : ℝ) ^ m = (t : ℝ) ^ ((m - 1) + 1) := congrArg (fun n : ℕ => (t : ℝ) ^ n) (by omega)
      _ = _ := pow_succ _ _
  have lower := (abs_le.mp err).1
  rw [split_pow] at lower
  have mass : (1 : ℝ) ≤ (t : ℝ) ^ (m - 1) := one_le_pow₀ (by exact_mod_cast ht1)
  have gap : (1 : ℝ) < (t : ℝ) - C := by linarith [le_abs_self C]
  have unpaid := mul_lt_mul_of_pos_right gap (lt_of_lt_of_le zero_lt_one mass)
  nlinarith

theorem no_height_share_admissibility (K ι : Type) [Field K] [NumberField K] [StarRing K]
    [Fintype ι] [Nonempty ι] : ¬ AdmG (geoDegenerate K ι) := by
  rintro ⟨_, _, _, _, _, h, _⟩
  exact no_asymptotic_riemann_roch K ι h

open Formalism.BasicNotions

/-- The builder selects such a geometry for every stage, including its own index type. -/
theorem builder_fails_growth_and_admissibility (D : D7)
    (jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)) (X₀ : DivX D) :
    ¬ AsymptoticRiemannRoch (divXFl D jC X₀).geo ∧ ¬ AdmG (divXFl D jC X₀).geo := by
  let _ : Nonempty D.what₂.Tau := ⟨D.eTau.symm 1⟩
  exact ⟨no_asymptotic_riemann_roch D.what₂.LL D.what₂.Tau,
    no_height_share_admissibility D.what₂.LL D.what₂.Tau⟩

#print axioms builder_fails_growth_and_admissibility
#print axioms no_asymptotic_riemann_roch
#print axioms no_height_share_admissibility
end RHRedteam.GeneralFlagGrowth
