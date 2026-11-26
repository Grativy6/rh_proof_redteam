import PALRH.EvenRemainders

open Finset
open scoped BigOperators

def fixedEvenEnergy (endLabel d : ℕ) : ℚ :=
  if d≤endLabel then
    ((endLabel%d:ℕ):ℚ)^2*((d:ℚ)-(endLabel%d:ℕ))^2/(4*d*(endLabel:ℚ)^2)
  else 0

def fixedEvenSource (T N : ℕ) : ℚ :=
  (T:ℚ)*∑ a ∈ Finset.range (N+1), ∑ b ∈ Finset.range (N+1),
    let p : ℕ:=2^a*3^b
    (p:ℚ)*∑ n ∈ Finset.Icc 1 T,
      if n=3^(Nat.log 3 n) then (max 0 (1-((n*p^2:ℕ):ℚ)/T))^3 else 0

/-- Squared circular remainders on one physical interval near a fourth power. -/
def fixedEvenWindow (j : ℕ) : ℚ :=
  let H:=j^4
  let S:=2*H
  let T:=2*(H+j^2)
  let N:=Nat.log 2 (H+j^2)+1
  fixedEvenSource T N-fixedEvenSource S N+
    ∑ a ∈ Finset.range (N+1), ∑ b ∈ Finset.range (N+1),
      let p : ℕ:=2^a*3^b
      (p:ℚ)*∑ d ∈ Finset.Icc 1 T,
        let k:=d*p^2
        if j^10<k^3 ∧ d.Coprime 6 then (ArithmeticFunction.moebius d:ℚ)*
          ((fixedEvenEnergy T k-fixedEvenEnergy S k)-
           (fixedEvenEnergy T (2*k)-fixedEvenEnergy S (2*k))) else 0

private theorem energy_agrees (T d : ℕ) : (fixedEvenEnergy T d:ℝ)=PALRH.EvenWindows.energy T d := by
  dsimp only [fixedEvenEnergy,PALRH.EvenWindows.energy]
  split_ifs <;> push_cast <;> rfl

private theorem source_agrees (T N : ℕ) : (fixedEvenSource T N:ℝ)=PALRH.EvenRemainders.base T N := by
  rw [fixedEvenSource,PALRH.EvenRemainders.base,Rat.cast_mul,Rat.cast_natCast,Rat.cast_sum]
  apply congrArg (fun v : ℝ => (T:ℝ)*v)
  apply Finset.sum_congr rfl;intro a _
  rw [Rat.cast_sum];apply Finset.sum_congr rfl;intro b _
  rw [Rat.cast_mul,Rat.cast_natCast,Rat.cast_sum]
  try unfold PALRH.CubicCarry.response
  apply congrArg
  apply Finset.sum_congr rfl
  intro n _
  have iff : (n=3^(Nat.log 3 n)) ↔ ∃ c : ℕ,n=3^c := by
    constructor
    · exact fun h => ⟨_,h⟩
    · rintro ⟨c,rfl⟩;rw [Nat.log_pow (by decide)]
  by_cases h : n=3^(Nat.log 3 n)
  · rw [if_pos h,if_pos (iff.mp h),PALRH.CubicWeights.cubic]
    push_cast
    rfl
  · rw [if_neg h,if_neg (fun e => h (iff.mpr e)),Rat.cast_zero]

private theorem cutoff_agrees {j : ℕ} (jp : 0<j) (k : ℕ) : PALRH.ReflectedCarry.cutoff j<k ↔ j^10<k^3 := by
  let D:=PALRH.ReflectedCarry.cutoff j
  have pow : D^3≤j^10 := Nat.findGreatest_spec (P:=fun n : ℕ => n^3≤j^10) (Nat.zero_le _) (by simp)
  constructor
  · intro hit
    by_contra! small
    have lim : j^10≤(j^4)^3 := by rw [←pow_mul];exact Nat.pow_le_pow_right jp (by decide)
    have inside : k≤j^4 := by
      by_contra! out;exact (not_lt_of_ge (small.trans lim)) (Nat.pow_lt_pow_left out (by decide : 3≠0))
    exact (not_lt_of_ge (Nat.le_findGreatest inside small)) hit
  · intro big
    by_contra! no
    exact (not_lt_of_ge ((Nat.pow_le_pow_left no 3).trans pow)) big

private theorem correct {j : ℕ} (jp : 0<j) : (fixedEvenWindow j:ℝ)=
    PALRH.EvenRemainders.retained (2*j^4) (2*(j^4+j^2)) (Nat.log 2 (j^4+j^2)+1) (PALRH.ReflectedCarry.cutoff j) := by
  unfold fixedEvenWindow PALRH.EvenRemainders.retained
  rw [Rat.cast_add,Rat.cast_sub,source_agrees,source_agrees,Rat.cast_sum,PALRH.EvenRemainders.aggregate]
  congr 1
  apply Finset.sum_congr rfl;intro a _
  rw [Rat.cast_sum];apply Finset.sum_congr rfl;intro b _
  rw [Rat.cast_mul,Rat.cast_natCast,Rat.cast_sum]
  apply congrArg;apply Finset.sum_congr rfl
  intro d _
  dsimp only
  have mk : ((PALRH.TaperedNewton.marks d:ℚ):ℝ)=
      (((ArithmeticFunction.moebius d:ℚ):ℝ)*(if d.Coprime 6 then 1 else 0)) := by
    change (((ArithmeticFunction.moebius d:ℚ)*(if d.Coprime 6 then 1 else 0):ℚ):ℝ)=_
    by_cases h : d.Coprime 6
    · simp only [if_pos h,mul_one]
    · simp only [if_neg h,mul_zero,Rat.cast_zero]
  simp only [cutoff_agrees jp,mk]
  by_cases high : j^10<(d*(2^a*3^b)^2)^3
  · by_cases rough : d.Coprime 6
    · have both : j^10<(d*(2^a*3^b)^2)^3 ∧ d.Coprime 6 := ⟨high,rough⟩
      simp only [if_pos both,if_pos high,if_pos rough,mul_one,
        Rat.cast_mul,Rat.cast_sub,energy_agrees,PALRH.EvenRemainders.variation]
    · have no : ¬(j^10<(d*(2^a*3^b)^2)^3 ∧ d.Coprime 6) := fun h => rough h.2
      simp only [if_neg no,if_pos high,if_neg rough,Rat.cast_zero,mul_zero,zero_mul]
  · have no : ¬(j^10<(d*(2^a*3^b)^2)^3 ∧ d.Coprime 6) := fun h => high h.1
    simp only [if_neg no,if_neg high,Rat.cast_zero,mul_zero]

theorem evenRemainderReduction (funded : ∃ B : ℕ, ∀ j : ℕ, B≤j → 0≤fixedEvenWindow j) :
    RiemannHypothesis := by
  apply PALRH.EvenRemainders.rh_of_even_remainders
  obtain ⟨B,ok⟩:=funded
  refine ⟨B,?_⟩
  intro j late jp
  change 0≤PALRH.EvenRemainders.retained _ _ _ _
  rw [←correct jp]
  exact_mod_cast ok j late

#print axioms evenRemainderReduction
