import PALRH.PrimitiveRecovery
import PALRH.QuarticBoards
import PALRH.SieveFrame
import PALRH.PascalCarry

open Finset
open scoped BigOperators

noncomputable section
namespace PALRH.OneSidedBoard
open PrimeBoard PrimeBand QuarticBoards LinearPrimeIntegral PrimeDivisorPrimitive

theorem reciprocal_read {t : ℝ} (ht : t∈Set.Ioc (0:ℝ) 1) :
    PrimitiveMellin.remainder t=(LogPrimitive.primitive (1/t):ℂ) := by
  let x:=1/t
  have xp : 0<x := by dsimp [x];exact one_div_pos.mpr ht.1
  have one : 1≤x := (one_le_div ht.1).mpr ht.2
  have xt : x*t=1 := by simp [x,one_div,ht.1.ne']
  have finite : PrimitiveMellin.reading t=∑ d ∈ Icc 1 ⌊x⌋₊,
      WeightedPrimePulse.term PrimitiveMellin.window d t := by
    unfold PrimitiveMellin.reading WeightedPrimePulse.reading
    apply tsum_eq_sum
    intro d out
    by_cases dz : d=0
    · simp [dz,WeightedPrimePulse.term]
    have dp:=Nat.pos_of_ne_zero dz
    have late : x<(d:ℝ) := (Nat.floor_lt xp.le).mp
      (lt_of_not_ge (fun q => out (mem_Icc.mpr ⟨dp,q⟩)))
    have high:=mul_lt_mul_of_pos_right late ht.1
    rw [xt] at high
    simp [WeightedPrimePulse.term,PrimitiveMellin.window,Set.indicator_of_notMem
      (fun h => (not_le_of_gt high) h.2 : (d:ℝ)*t∉Set.Ioc (0:ℝ) 1)]
  have sum : PrimitiveMellin.reading t=∑ d ∈ Icc 1 ⌊x⌋₊,
      ArithmeticFunction.vonMangoldt d*(Real.log (x/d)-1+d/x) := by
    rw [finite]
    apply Finset.sum_congr rfl
    intro d hd
    have dp : 0<(d:ℝ) := by exact_mod_cast (mem_Icc.mp hd).1
    have small : (d:ℝ)≤x := (Nat.le_floor_iff xp.le).mp (mem_Icc.mp hd).2
    have last:=mul_le_mul_of_nonneg_right small ht.1.le
    rw [xt] at last
    have inside : (d:ℝ)*t∈Set.Ioc (0:ℝ) 1 := ⟨mul_pos dp ht.1,last⟩
    rw [WeightedPrimePulse.term,PrimitiveMellin.window,Set.indicator_of_mem inside,
      show x/d=((d:ℝ)*t)⁻¹ by dsimp [x];ring,Real.log_inv,
      show (d:ℝ)/x=(d:ℝ)*t by simp [x,div_eq_mul_inv]]
    ring
  unfold PrimitiveMellin.remainder PrimitiveMellin.center
  rw [Set.indicator_of_mem ht,sum,LogPrimitive.exact_value one]

theorem rh_of_real_upper {C : ℝ} (cn : 0≤C) (bound : ∀ x : ℝ, 1≤x → value x≤C*Real.sqrt x) :
    RiemannHypothesis := by
  apply PrimitiveMellin.rh_of_primitive_bound (D:=4*(2*C+24)) (by positivity)
  intro t ht
  rw [reciprocal_read ht,Complex.norm_real,Real.norm_eq_abs]
  have h:=PrimitiveRecovery.primitive_bound cn bound (x:=1/t) (by have:=ht.1;positivity)
  simpa only [one_div,Real.sqrt_inv,mul_inv_rev,div_eq_mul_inv,one_mul] using h

private theorem real_head {C : ℝ} (cn : 0≤C)
    (bound : ∀ n : ℕ, 0<n → error n≤C*n*Real.sqrt n)
    {x : ℝ} (large : 1≤x) : value x≤(2*C+1)*Real.sqrt x := by
  let M:=⌊x⌋₊
  let N:=M+1
  have xp := zero_lt_one.trans_le large
  have np : 0<N := Nat.succ_pos _
  have nr : 0<(N:ℝ) := by exact_mod_cast np
  have xN : x<(N:ℝ) := by simpa [N,M] using Nat.lt_floor_add_one x
  have close : (N:ℝ)≤x+1 := by
    dsimp [N,M];push_cast;linarith only [Nat.floor_le xp.le]
  have shift : (∑ d ∈ Icc 1 M, ArithmeticFunction.vonMangoldt d*(1-d/x))≤
      ∑ d ∈ Icc 1 N, ArithmeticFunction.vonMangoldt d*(1-d/(N:ℝ)) := by
    calc
      _ ≤ ∑ d ∈ Icc 1 M, ArithmeticFunction.vonMangoldt d*(1-d/(N:ℝ)) := by
        apply Finset.sum_le_sum
        intro d _
        exact mul_le_mul_of_nonneg_left (sub_le_sub_left
          (div_le_div_of_nonneg_left (Nat.cast_nonneg _) xp xN.le) _) ArithmeticFunction.vonMangoldt_nonneg
      _ ≤ _ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro d hd;exact mem_Icc.mpr ⟨(mem_Icc.mp hd).1,(mem_Icc.mp hd).2.trans (Nat.le_succ _)⟩
        · intro d hd _
          have dw : (d:ℝ)≤N := by exact_mod_cast (mem_Icc.mp hd).2
          exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (sub_nonneg.mpr ((div_le_one nr).mpr dw))
  have eq : (∑ d ∈ Icc 1 N, ArithmeticFunction.vonMangoldt d*(1-d/(N:ℝ)))=fullWalk N/N := by
    rw [fullWalk,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro d _
    field_simp
  rw [eq] at shift
  have cost:=bound N np
  unfold error at cost
  have top : fullWalk N/N≤(N:ℝ)/2+C*Real.sqrt N := by
    apply (div_le_iff₀ nr).mpr
    nlinarith only [cost]
  have root : Real.sqrt (N:ℝ)≤2*Real.sqrt x := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    rw [mul_pow,Real.sq_sqrt xp.le]
    linarith only [large,close]
  unfold value
  rw [if_pos large]
  change _-(x/2)≤_
  nlinarith only [shift,top,close,Real.one_le_sqrt.mpr large,mul_le_mul_of_nonneg_left root cn]

/-- All sufficiently large fourth-power heads may supply only an upper prime-power area. -/
theorem rh_of_eventual_upper_area (K : ℕ) {C : ℝ} (cn : 0≤C)
    (priced : ∀ k : ℕ, K≤k → 0<k → error (k^4)≤C*(k:ℝ)^6) :
    RiemannHypothesis := by
  let early := ∑ j ∈ range K, |error (j^4)|
  have en : 0≤early := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  let D:=C+early
  have dn : 0≤D := add_nonneg cn en
  have knots (k : ℕ) : error (k^4)≤D*(k:ℝ)^6 := by
    by_cases kz : k=0
    · subst k;simp [error,fullWalk]
    have kp:=Nat.pos_of_ne_zero kz
    by_cases large : K≤k
    · exact (priced k large kp).trans (mul_le_mul_of_nonneg_right (show C≤D by dsimp [D];linarith) (by positivity))
    · have kept : |error (k^4)|≤early := Finset.single_le_sum (fun i (_ : i∈range K) => abs_nonneg (error (i^4)))
        (mem_range.mpr (lt_of_not_ge large))
      have one : (1:ℝ)≤k := by exact_mod_cast kp
      have power : (1:ℝ)≤(k:ℝ)^6 := one_le_pow₀ one
      exact (le_abs_self _).trans (kept.trans ((show early≤D by dsimp [D];linarith).trans
        (by simpa using mul_le_mul_of_nonneg_left power dn)))
  have cost : 0≤64*D+256 := by positivity
  exact rh_of_real_upper (by positivity : 0≤2*(64*D+256)+1)
    (fun _ xh => real_head cost (fun _ np => quartic_upper_envelope dn knots np) xh)

/-- A single eventual bound on excess demand, at fourth powers only, implies stock RH. -/
theorem rh_of_eventual_overflow (K : ℕ)
    (funded : ∀ k : ℕ, K≤k → 0<k → demand (k^4)≤capacity (k^4)*allowance (k^4)) :
    RiemannHypothesis := by
  obtain ⟨C,cn,price⟩:=full_walk_upper_price
  apply rh_of_eventual_upper_area K cn
  intro k late kp
  have h:=price (k^4) (pow_pos kp _) (funded k late kp)
  have root : Real.sqrt ((k:ℝ)^4)=(k:ℝ)^2 := by
    rw [show (k:ℝ)^4=((k:ℝ)^2)^2 by ring,Real.sqrt_sq (by positivity)]
  unfold error
  push_cast at h ⊢
  rw [root] at h
  calc
    _ ≤ _ := h
    _ = _ := by ring

/-- The entire remaining Pascal input is the comparison of two explicitly computed coprime integers. -/
theorem rh_of_eventual_pascal_exchange (K : ℕ)
    (exchange : ∀ k : ℕ, K≤k → 0<k →
      PascalBoard.oneWay (k^4)/PascalBoard.shared (k^4)≤PascalBoard.subsetStates (k^4)/PascalBoard.shared (k^4)) :
    RiemannHypothesis := by
  apply rh_of_eventual_overflow K
  intro k late kp
  have fits:=PascalCarry.exchange_pays (exchange k late kp)
  have cost:=(full_cost (le_refl (k^4).sqrt)).2
  exact cost.trans (Nat.mul_le_mul_right _ fits)

/-- A single eventual fit of the factorial-gcd frame also suffices. -/
theorem rh_of_eventual_factorial_fit (K : ℕ)
    (fits : ∀ k : ℕ, K≤k → 0<k → SieveFrame.frameCount (k^4) (k^2).factorial≤capacity (k^4)) :
    RiemannHypothesis := by
  apply rh_of_eventual_overflow K
  intro k late kp
  have eq:=SieveFrame.frame_count_exact (k^4)
  rw [SieveFrame.root_of_quartic] at eq
  have fund:=fits k late kp
  rw [eq] at fund
  have cost:=(full_cost (le_refl (k^4).sqrt)).2
  rw [SieveFrame.root_of_quartic] at cost
  exact cost.trans (Nat.mul_le_mul_right _ fund)

/-- One direction of the actual gcd-selected dials, before matching subset factors. -/
def oneFrameDirection (n F : ℕ) : ℕ :=
  ∏ m ∈ Icc 2 n, if m.gcd F=1 then m^(n-m) else 1

theorem frame_square (n F : ℕ) :
    SieveFrame.frameCount n F=n.factorial^n*(oneFrameDirection n F)^2 := by
  unfold SieveFrame.frameCount oneFrameDirection
  rw [←Finset.prod_pow]
  congr 1
  apply Finset.prod_congr rfl
  intro m _
  by_cases keep : m.gcd F=1
  · simp only [keep,if_true,←pow_mul,Nat.mul_comm (n-m) 2]
  · simp [keep]

/-- The sole eventual premise compares a gcd-selected product with one row of Pascal's triangle. -/
theorem rh_of_one_subset_comparison (K : ℕ)
    (pay : ∀ k : ℕ, K≤k → 0<k → oneFrameDirection (k^4) (k^2).factorial≤PascalBoard.subsetStates (k^4)) :
    RiemannHypothesis := by
  apply rh_of_eventual_factorial_fit K
  intro k late kp
  rw [frame_square]
  exact (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (pay k late kp) 2)).trans
    (PascalBoard.two_pascal_rows_fit (k^4))

#print axioms PALRH.OneSidedBoard.rh_of_real_upper
#print axioms PALRH.OneSidedBoard.rh_of_eventual_overflow
#print axioms PALRH.OneSidedBoard.rh_of_eventual_pascal_exchange
#print axioms PALRH.OneSidedBoard.rh_of_eventual_factorial_fit
#print axioms PALRH.OneSidedBoard.rh_of_one_subset_comparison
end PALRH.OneSidedBoard
