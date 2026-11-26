import PALRH.OneHeadPhysical

open Finset
open scoped BigOperators

/-- Sum the ordinary arithmetic marks against the one-sided linear ramp at 2*j^4. -/
def fixedPrimitive (j : ℕ) : ℚ :=
  let T:=2*j^4
  let L:=Nat.log 2 (j^4)+1
  ∑ i ∈ Finset.range (L+1), ∑ k ∈ Finset.range (L+1),
    let v : ℕ:=2^i*3^k
    ∑ d ∈ Finset.Icc 1 T, if d.Coprime 6 then
      (ArithmeticFunction.moebius d:ℚ)*v*max 0 ((T:ℚ)/((d:ℚ)*v^2)-1)
      else 0

private theorem ordinary_value (j : ℕ) :
    fixedPrimitive j=PALRH.OneHeadPhysical.primitive j := by
  unfold fixedPrimitive PALRH.OneHeadPhysical.primitive
  apply Finset.sum_congr rfl;intro i _
  apply Finset.sum_congr rfl;intro k _
  apply Finset.sum_congr rfl;intro d hd
  let v : ℕ:=2^i*3^k
  have dp : 0<d := (Finset.mem_Icc.mp hd).1
  have dr : 0<(d:ℚ) := by exact_mod_cast dp
  have vp : 0<v := by dsimp [v];positivity
  have vr : 0<(v:ℚ) := by exact_mod_cast vp
  by_cases rough : d.Coprime 6
  · have mark : PALRH.TaperedNewton.marks d=(ArithmeticFunction.moebius d:ℚ) := by
      change (ArithmeticFunction.moebius d:ℚ)*(if d.Coprime 6 then 1 else 0)=_
      simp [rough]
    rw [if_pos rough,mark]
    let T : ℚ:=((2*j^4:ℕ):ℚ)
    have same : 2*((j^4:ℕ):ℚ)=T := by simp [T]
    change (ArithmeticFunction.moebius d:ℚ)*(v:ℚ)*max 0 (T/((d:ℚ)*v^2)-1)=
      (ArithmeticFunction.moebius d:ℚ)/(d*(v:ℚ))*max 0 (2*((j^4:ℕ):ℚ)-((d*v^2:ℕ):ℚ))
    rw [same,show ((d*v^2:ℕ):ℚ)=(d:ℚ)*(v:ℚ)^2 by push_cast; rfl]
    have denom : 0<(d:ℚ)*v^2 := by positivity
    have eq : ((d:ℚ)*v^2)*max 0 (T/((d:ℚ)*v^2)-1) = max 0 (T-(d:ℚ)*v^2) := by
      rw [mul_max_of_nonneg _ _ denom.le,mul_zero]
      congr 1
      field_simp
    rw [←eq]
    let t:=max 0 (T/((d:ℚ)*v^2)-1)
    change (ArithmeticFunction.moebius d:ℚ)*v*t=(ArithmeticFunction.moebius d:ℚ)/(d*(v:ℚ))*((d:ℚ)*v^2*t)
    field_simp
  · have mark : PALRH.TaperedNewton.marks d=0 := by
      change (ArithmeticFunction.moebius d:ℚ)*(if d.Coprime 6 then 1 else 0)=0
      simp [rough]
    rw [if_neg rough,mark];ring

theorem primitiveFourthReduction (signs : ∃ B : ℕ, ∀ j : ℕ, B≤j → 0≤fixedPrimitive j) :
    RiemannHypothesis := by
  apply PALRH.OneHeadPhysical.rh_of_primitive_sign
  simpa only [ordinary_value] using signs

#print axioms primitiveFourthReduction
