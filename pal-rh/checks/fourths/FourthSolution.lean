import PALRH.FourthAccounts

open Finset
open scoped BigOperators

/-- The price is specified directly by an ordinary Möbius sum on the first 2H indices. -/
def fixedAreaPrice (H : ℕ) : ℚ :=
  ∑ n ∈ Finset.Icc 1 (2*H), if n.Coprime 6 then
    (ArithmeticFunction.moebius n:ℚ)/n*
      (if n≤H then 1 else ((2*H-n:ℕ):ℚ)/H) else 0

def fixedAreaCount (positive : Bool) (J : ℕ) : ℚ :=
  ∑ j ∈ Finset.Icc 1 J, (j:ℚ)*max (if positive then fixedAreaPrice (j^4) else -fixedAreaPrice (j^4)) 0


private theorem correct_price (H : ℕ) : fixedAreaPrice H =
    PALRH.TaperedNewton.slope H PALRH.TaperedNewton.marks := by
  apply Finset.sum_congr rfl
  intro n hn
  have top := (Finset.mem_Icc.mp hn).2
  change (if n.Coprime 6 then _ else _) = PALRH.TaperedNewton.weight H n*
    ((ArithmeticFunction.moebius n:ℚ)*(if n.Coprime 6 then 1 else 0))/n
  unfold PALRH.TaperedNewton.weight
  split_ifs <;> first | omega | ring


private theorem correct_count (o : Bool) (J : ℕ) :
    fixedAreaCount o J=PALRH.FourthAccounts.tally o J := by
  apply Finset.sum_congr rfl
  intro j _
  cases o <;> simp [PALRH.FourthAccounts.peak,PALRH.SourceAllowance.direction,correct_price]

theorem fourthPowerAreaReduction
    (small : ∀ k : ℕ, 0<k → ∀ B : ℕ, ∃ J : ℕ, B≤J ∧
      ∃ positive : Bool, (fixedAreaCount positive J)^k≤(J:ℚ)) : RiemannHypothesis := by
  apply PALRH.FourthAccounts.rh_of_checkpoints
  intro k pos B
  obtain ⟨J,late,o,hit⟩ := small k pos B
  exact ⟨J,late,o,correct_count o J ▸ hit⟩

#print axioms fourthPowerAreaReduction
