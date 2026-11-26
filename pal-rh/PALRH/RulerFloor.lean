import PALRH.DoubledPrice

open Finset
open scoped BigOperators
noncomputable section
namespace PALRH.RulerFloor
open DoubledRuler DoubledPrice

private theorem ink_ge_step {N m : ℕ} (mp : 0<m) (mn : m≤N) :
    potential N (m-1)-potential N m-30*(N:ℝ)^5 ≤ (ink N m:ℝ) := by
  let t : ℝ := (N:ℝ)-m
  have mr : (1:ℝ)≤m := by exact_mod_cast mp
  have tn : 0≤t := sub_nonneg.mpr (by exact_mod_cast mn)
  have tp : 0 ≤ t+1 := by positivity
  have within : t+1≤N := by dsimp [t]; linarith only [mr]
  have first : (t+1)^6-t^6 ≤ 6*(t+1)^5 := by
    have h : 0 ≤ 15*t^4+40*t^3+45*t^2+24*t+5 := by positivity
    nlinarith only [h]
  have second : (t+1)^5-t^5 ≤ 5*(t+1)^4 := by
    have h : 0 ≤ 10*t^3+20*t^2+15*t+4 := by positivity
    nlinarith only [h]
  have prod := mul_le_mul_of_nonneg_left first (sub_nonneg.mpr mr)
  have prod2 := mul_le_mul_of_nonneg_left second (sub_nonneg.mpr mr)
  have bound := mul_le_mul (by exact_mod_cast (show m-1 ≤ N by omega) :
      (((m-1:ℕ):ℝ)) ≤ N) (pow_le_pow_left₀ tp within 4) (pow_nonneg tp _) (Nat.cast_nonneg N)
  rw [Nat.cast_sub (by omega : 1≤m),Nat.cast_one] at bound
  unfold ink potential
  push_cast [Nat.cast_sub (show 1≤m by omega)]
  rw [show (N:ℝ)-((m:ℝ)-1)=t+1 by dsimp [t];ring,
      show (7*(m:ℝ)-N)=6*m-t by dsimp [t];ring]
  change ((m:ℝ)-1)*(t+1)^6-(m:ℝ)*t^6-30*(N:ℝ)^5 ≤ t^5*(6*m-t)
  nlinarith only [prod,prod2,bound,pow_nonneg tn 5]

private theorem lower_sum (N L : ℕ) (cap : L ≤ N) :
    (N:ℝ)^7-((N:ℝ)-L)^7-7*((N:ℝ)^6-((N:ℝ)-L)^6) ≤
      7*∑ m ∈ Icc 1 L, ((N:ℝ)-m)^6 := by
  induction L with
  | zero => simp
  | succ k old =>
    have prior := old (by omega : k≤N)
    rw [sum_Icc_succ_top (by omega : 1≤k+1),mul_add]
    push_cast
    let t : ℝ := (N:ℝ)-(k+1)
    have tn : 0 ≤ t := sub_nonneg.mpr (by exact_mod_cast cap)
    have price : (t+1)^7-t^7 ≤ 7*(t+1)^6 := by
      have h : 0 ≤ 21*t^5+70*t^4+105*t^3+84*t^2+35*t+6 := by positivity
      nlinarith only [h]
    rw [show (N:ℝ)-k=t+1 by dsimp [t];ring] at prior
    linarith only [prior,price]

private theorem log_telescope (N : ℕ) :
    (∑ m ∈ Icc 1 N,(Real.log ((m:ℝ)+1)-Real.log m))=Real.log ((N:ℝ)+1) := by
  induction N with
  | zero => simp
  | succ n old => rw [sum_Icc_succ_top (by omega : 1≤n+1),old];push_cast;ring

theorem ordinary_lower (N : ℕ) :
    (N:ℝ)^7/7 - (N:ℝ)^6*(1+31*Real.log ((N:ℝ)+1)) ≤ ordinary N := by
  let incr := fun m : ℕ => Real.log ((m:ℝ)+1)-Real.log m
  have fee : (∑ m ∈ Icc 1 N,((N:ℝ)-m)^6) - (N:ℝ)^6*Real.log ((N:ℝ)+1) ≤
       ∑ m ∈ Icc 1 N, potential N m*incr m := by
    rw [←log_telescope,mul_sum,←sum_sub_distrib]
    apply sum_le_sum
    intro m hm
    have mp : 0<(m:ℝ) := by exact_mod_cast (mem_Icc.mp hm).1
    have mn : (m:ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hm).2
    have step := Real.one_sub_inv_le_log_of_pos (show 0<((m:ℝ)+1)/m by positivity)
    rw [Real.log_div (by positivity) mp.ne',show 1-(((m:ℝ)+1)/m)⁻¹=1/(m+1) by field_simp;ring] at step
    have one := (div_le_iff₀ (by positivity : 0<(m:ℝ)+1)).mp step
    have inc : 0 ≤ incr m := (by positivity : (0:ℝ)≤1/(m+1)).trans step
    have a := pow_le_pow_left₀ (sub_nonneg.mpr mn) (sub_le_self (N:ℝ) mp.le) 6
    have p := mul_le_mul_of_nonneg_right a inc
    have q := mul_le_mul_of_nonneg_left one (by positivity : 0≤((N:ℝ)-m)^6)
    dsimp [incr] at p ⊢
    unfold potential
    nlinarith only [p,q]
  have comp : (∑ m ∈ Icc 1 N,(potential N (m-1)-potential N m)*Real.log m) -
      30*(N:ℝ)^6*Real.log ((N:ℝ)+1) ≤ ordinary N := by
    have single : ∀ m ∈ Icc 1 N,
        (potential N (m-1)-potential N m)*Real.log m -
          30*(N:ℝ)^5*Real.log ((N:ℝ)+1) ≤ Real.log m*(ink N m:ℝ) := by
      intro m hm
      have hp := (mem_Icc.mp hm).1
      have rr := ink_ge_step hp (mem_Icc.mp hm).2
      have lm := Real.log_nonneg (show 1≤(m:ℝ) by exact_mod_cast hp)
      have ln := Real.log_le_log (show 0<(m:ℝ) by exact_mod_cast hp)
        (show (m:ℝ)≤(N:ℝ)+1 by have h:=(mem_Icc.mp hm).2;exact_mod_cast (show m≤N+1 by omega))
      have a := mul_le_mul_of_nonneg_right rr lm
      have b := mul_le_mul_of_nonneg_left ln (by positivity : 0≤30*(N:ℝ)^5)
      nlinarith only [a,b]
    have total:=sum_le_sum single
    rw [sum_sub_distrib] at total
    simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul] at total
    unfold ordinary
    nlinarith only [total]
  have lower:=lower_sum N N le_rfl
  rw [log_steps] at comp
  simp only [sub_self,zero_pow (by decide : 7≠0),zero_pow (by decide : 6≠0),sub_zero] at lower
  simp [potential] at comp fee
  dsimp [incr] at fee
  linarith only [lower,comp,fee]

#print axioms PALRH.RulerFloor.ordinary_lower
end PALRH.RulerFloor
