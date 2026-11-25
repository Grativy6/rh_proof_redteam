import PALRH.CubicFourth

open Finset
open scoped BigOperators

/-- At the physical fourth power, take the ordinary Mobius marks coprime to six,
multiply their indices by the two squares and taper them on the same head. -/
def fixedFourthSignValue (j : ℕ) : ℚ :=
  let H:=j^4
  let L:=Nat.log 2 H+1
  ∑ a ∈ Finset.range (L+1), ∑ b ∈ Finset.range (L+1),
    ∑ d ∈ Finset.Icc 1 (2*H), if d.Coprime 6 then
      (ArithmeticFunction.moebius d:ℚ)/(d*(2^a*3^b:ℕ))*
        max 0 (min 1 (2-((d*(2^a*3^b)^2:ℕ):ℚ)/H)) else 0

private theorem actual (j : ℕ) (jp : 0<j) :
    fixedFourthSignValue j=PALRH.CubicFourth.fourthValue j := by
  let H:=j^4
  let L:=Nat.log 2 H+1
  have hp : 0<H := pow_pos jp 4
  have hq : 0<(H:ℚ) := by exact_mod_cast hp
  have enough : H≤2^L := (Nat.lt_pow_succ_log_self (by decide : 1<2) H).le
  let I:=Finset.Icc 1 (2*H)
  let J:=Finset.Icc 1 (2^(L+1))
  let K:=Finset.range (L+1)
  unfold fixedFourthSignValue PALRH.CubicFourth.fourthValue
  change (∑ a ∈ K, ∑ b ∈ K, ∑ d ∈ I, _) =
    PALRH.SquareSignRows.qSweep L 2 (PALRH.SquareSignRows.qSweep L 3 (PALRH.SquareSignRows.qEdge L)) ((j:ℚ)^4)
  rw [PALRH.SquareSignRows.qSweep]
  apply Finset.sum_congr rfl
  intro a _
  rw [PALRH.SquareSignRows.qSweep,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro b _
  let p:=2^a*3^b
  have pa : 0<((2^a:ℕ):ℚ) := by positivity
  have pb : 0<((3^b:ℕ):ℚ) := by positivity
  have pu : (1:ℚ)≤(p:ℚ)^2 := by exact_mod_cast (show 1≤p^2 from pow_pos (Nat.mul_pos (pow_pos (by decide) a) (pow_pos (by decide) b)) 2)
  have cap : I⊆J := fun d hd => Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1,
    ((Finset.mem_Icc.mp hd).2).trans (by rw [pow_succ'];exact Nat.mul_le_mul_left 2 enough)⟩
  let coefficient:=fun d : ℕ => if d.Coprime 6 then
    (ArithmeticFunction.moebius d:ℚ)/(d*p)*max 0 (min 1 (2-((d*p^2:ℕ):ℚ)/H)) else 0
  have trim : (∑ d ∈ I, coefficient d)=∑ d ∈ J, coefficient d := by
    apply Finset.sum_subset cap
    intro d hd out
    have large : 2*H<d := by
      by_contra! h;exact out (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1,h⟩)
    have dr : 2*(H:ℚ)<d := by exact_mod_cast large
    have rise : (2:ℚ)≤((d*p^2:ℕ):ℚ)/H := (le_div_iff₀ hq).mpr (by
      push_cast;nlinarith [mul_le_mul_of_nonneg_left pu (Nat.cast_nonneg (α:=ℚ) d)])
    simp only [coefficient,min_eq_right (show 2-((d*p^2:ℕ):ℚ)/H≤1 by linarith),
      max_eq_left (show 2-((d*p^2:ℕ):ℚ)/H≤0 by linarith),mul_zero,ite_self]
  change (∑ d ∈ I, coefficient d)=_
  rw [trim,PALRH.SquareSignRows.qEdge,Finset.sum_div,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d hd
  have dr : 0<(d:ℚ) := by exact_mod_cast (show 0<d from (Finset.mem_Icc.mp hd).1)
  have scale : ((d*p^2:ℕ):ℚ)/H=(d:ℚ)/(((j:ℚ)^4/((2^a:ℕ):ℚ)^2)/((3^b:ℕ):ℚ)^2) := by
    dsimp [p,H];push_cast;field_simp
  change coefficient d=((ArithmeticFunction.moebius d:ℚ)*(if d.Coprime 6 then 1 else 0)/d*
    max 0 (min 1 (2-(d:ℚ)/(((j:ℚ)^4/((2^a:ℕ):ℚ)^2)/((3^b:ℕ):ℚ)^2))))/(3^b:ℕ)/(2^a:ℕ)
  dsimp only [coefficient]
  rw [scale]
  by_cases cp : d.Coprime 6
  · simp only [if_pos cp,mul_one]
    dsimp only [p]
    push_cast
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  · simp [cp]

theorem firstPassFourthReduction (signs : ∃ B : ℕ, ∀ j : ℕ, B≤j → 0≤fixedFourthSignValue j) :
    RiemannHypothesis := by
  apply PALRH.CubicFourth.rh_of_first_pass_fourths
  obtain ⟨B,ok⟩ := signs
  refine ⟨max B 1,?_⟩
  intro j large
  rw [←actual j (by omega)]
  exact ok j (by omega)

#print axioms firstPassFourthReduction
