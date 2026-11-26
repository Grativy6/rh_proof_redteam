import PALRH.RulerOmissions
import PALRH.RulerFloor
import PALRH.AreaBracket

open Finset
open scoped BigOperators
noncomputable section
namespace PALRH.PrimeCopies
open DoubledRuler DoubledPrice RulerOmissions LinearPrimeIntegral

def pays (copies k : ℕ) : Prop :=
  (k^4+1)^ticks k ≤ (k^4)^ticks k * (primeSettings (k^4))^copies

def demand (k : ℕ) : ℝ :=
  (k:ℝ)^4*(k^4-k^2)^2*(Real.log ((k:ℝ)^4+1)-Real.log ((k:ℝ)^4))

private theorem packet_pos (n : ℕ) : 0 < primeSettings n := by
  apply Finset.prod_pos
  intro d hd
  split_ifs with p
  · exact pow_pos p.1.pos _
  · decide

theorem pays_iff {k : ℕ} (kp : 0<k) (copies : ℕ) :
    pays copies k ↔ demand k ≤ (copies:ℝ)*earned (k^4) := by
  let n:=k^4
  let N:=2*n
  have np : 0<n := pow_pos kp _
  have nr : 0<(n:ℝ) := by exact_mod_cast np
  have pr : 0<(primeSettings n:ℝ) := by exact_mod_cast packet_pos n
  have pos : 0<(N:ℝ)^5 := by dsimp [N];positivity
  have cut : k^2≤n := Nat.pow_le_pow_right kp (by decide)
  have clock : (ticks k:ℝ)=(N:ℝ)^5*(n:ℝ)*(n-(k:ℝ)^2)^2 := by
    change (((2*n)^5*n*(n-k^2)^2:ℕ):ℝ)=_
    push_cast [Nat.cast_sub cut]
    dsimp [N];push_cast;ring
  have same : demand k = (n:ℝ)*((n:ℝ)-(k:ℝ)^2)^2*(Real.log ((n:ℝ)+1)-Real.log (n:ℝ)) := by
    dsimp [demand,n];push_cast;rfl
  change (n+1)^ticks k ≤ n^ticks k*(primeSettings n)^copies ↔ _
  rw [←Nat.cast_le (α:=ℝ)]
  push_cast
  rw [←Real.log_le_log_iff (by positivity) (by positivity),Real.log_mul (by positivity) (by positivity)]
  simp only [Real.log_pow]
  rw [same,clock]
  change _ ↔ _ ≤ copies*(Real.log (primeSettings n:ℝ)/(N:ℝ)^5)
  rw [←mul_div_assoc,le_div_iff₀ pos]
  constructor <;> intro h <;> nlinarith only [h]

private theorem demand_band {k : ℕ} (kp : 0<k) :
    (k:ℝ)^8-3*k^6 ≤ demand k ∧ demand k ≤ (k:ℝ)^8 := by
  let n:ℝ:=(k:ℝ)^4
  have kr : 1≤(k:ℝ) := by exact_mod_cast kp
  have nr : 0<n := by dsimp [n];positivity
  have small : (k:ℝ)^2 ≤ n := pow_le_pow_right₀ kr (by decide)
  have factor : 0 ≤ n*(n-(k:ℝ)^2)^2 := by positivity
  have lo := Real.one_sub_inv_le_log_of_pos (show 0<(n+1)/n by positivity)
  have hi := Real.log_le_sub_one_of_pos (show 0<(n+1)/n by positivity)
  rw [Real.log_div (by positivity) nr.ne',show 1-((n+1)/n)⁻¹=1/(n+1) by field_simp;ring] at lo
  rw [Real.log_div (by positivity) nr.ne',show ((n+1)/n)-1=1/n by field_simp;ring] at hi
  have lower := mul_le_mul_of_nonneg_left lo factor
  have upper := mul_le_mul_of_nonneg_left hi factor
  change _ ≤ n*(n-(k:ℝ)^2)^2*(Real.log (n+1)-Real.log n) ∧ n*(n-(k:ℝ)^2)^2*(_-_) ≤ _
  have low : n^2-2*n*k^2-n ≤ n*(n-(k:ℝ)^2)^2*(1/(n+1)) := by
    rw [one_div,←div_eq_mul_inv]
    apply (le_div_iff₀ (by positivity : 0<n+1)).mpr
    nlinarith only [mul_nonneg nr.le (sq_nonneg ((k:ℝ)^2)),nr.le,
      mul_nonneg nr.le (sq_nonneg (k:ℝ))]
  have upper_id : n*(n-(k:ℝ)^2)^2*(1/n)=(n-(k:ℝ)^2)^2 := by field_simp
  rw [upper_id] at upper
  have sq := pow_le_pow_left₀ (sub_nonneg.mpr small) (sub_le_self n (sq_nonneg (k:ℝ))) 2
  have k46 : (k:ℝ)^4 ≤ (k:ℝ)^6 := pow_le_pow_right₀ kr (by decide)
  dsimp [n] at low lower upper sq ⊢
  constructor <;> nlinarith only [low,lower,upper,sq,k46]

private theorem log_cap {k : ℕ} (kp : 0<k) :
    Real.log (((2*k^4:ℕ):ℝ)+1) ≤ 8*k := by
  have kr : 1 ≤ (k:ℝ) := by exact_mod_cast kp
  have k4 : (1:ℝ)≤(k:ℝ)^4 := one_le_pow₀ kr
  have mon := Real.log_le_log (by positivity : 0<(((2*k^4:ℕ):ℝ)+1))
    (show (((2*k^4:ℕ):ℝ)+1) ≤ ((2:ℝ)*k)^4 by push_cast;nlinarith only [k4])
  rw [Real.log_pow] at mon
  have h:=Real.log_le_sub_one_of_pos (show 0<(2:ℝ)*k by positivity)
  push_cast at mon ⊢
  linarith only [mon,h]

private theorem analytic_band {k : ℕ} (large : 2≤k) :
    (4/7:ℝ)*(k:ℝ)^8-498*k^5 ≤ outlay (k^4) ∧
    outlay (k^4) ≤ (4/7:ℝ)*(k:ℝ)^8+96*k^5 ∧
    (62/125:ℝ)*(k:ℝ)^8-256*k^5 ≤ fullWalk (k^4) ∧
    fullWalk (k^4) ≤ (63/125:ℝ)*(k:ℝ)^8+256*k^5 := by
  let n:=k^4
  let N:=2*n
  have kp : 0<k := by omega
  have kr : 1≤(k:ℝ) := by exact_mod_cast kp
  have np : 0<n := pow_pos kp _
  have nr : 0<(n:ℝ) := by exact_mod_cast np
  have Np : 0<(N:ℝ) := by dsimp [N];positivity
  have lo := RulerFloor.ordinary_lower N
  have hi := ordinary_price N
  have cap := log_cap kp
  change Real.log ((N:ℝ)+1)≤8*k at cap
  have lowerlog := (Real.log_le_log Np (by linarith : (N:ℝ)≤N+1)).trans cap
  have smalllog := (Real.log_le_log (by positivity : 0<(n:ℝ)+1)
      (show (n:ℝ)+1≤(N:ℝ)+1 by dsimp [N];push_cast;linarith only [nr])).trans cap
  have pay1:=mul_le_mul_of_nonneg_left cap (by positivity : 0≤31*(N:ℝ)^6)
  have pay2:=mul_le_mul_of_nonneg_left lowerlog (by positivity : 0≤6*(N:ℝ)^6)
  have raw:=AreaBracket.raw_box (n:=n) (by
    change 2^4 ≤ k^4
    exact Nat.pow_le_pow_left large 4)
  have pay3:=mul_le_mul_of_nonneg_left smalllog (by positivity : 0≤32*(n:ℝ))
  change _ ≤ outlay n ∧ outlay n ≤ _ ∧ _ ≤ fullWalk n ∧ fullWalk n ≤ _
  have nN : (N:ℝ)=2*(k:ℝ)^4 := by dsimp [N,n];push_cast;rfl
  have nr_eq : (n:ℝ)=(k:ℝ)^4 := by dsimp [n];push_cast;rfl
  have k4k5:=pow_le_pow_right₀ kr (by decide : 4≤5)
  refine ⟨?_,?_,?_,?_⟩
  · unfold outlay
    change _ ≤ ordinary N/(N:ℝ)^5
    apply (le_div_iff₀ (pow_pos Np _)).mpr
    rw [nN] at lo pay1 ⊢
    have toll:=mul_le_mul_of_nonneg_left k4k5 (by positivity : 0≤2*(2*(k:ℝ)^4)^5)
    nlinarith only [lo,pay1,toll]
  · unfold outlay
    change ordinary N/(N:ℝ)^5 ≤ _
    apply (div_le_iff₀ (pow_pos Np _)).mpr
    rw [nN] at hi pay2 ⊢
    nlinarith only [hi,pay2]
  · rw [nr_eq] at pay3 raw
    nlinarith only [raw.1,pay3]
  · rw [nr_eq] at pay3 raw
    nlinarith only [raw.2,pay3]

theorem clock_price_bands {k : ℕ} (large : 2≤k) :
    (k:ℝ)^8-3*k^6 ≤ demand k ∧ demand k ≤ (k:ℝ)^8 ∧
    (4/7:ℝ)*(k:ℝ)^8-498*k^5 ≤ outlay (k^4) ∧ outlay (k^4) ≤ (4/7:ℝ)*(k:ℝ)^8+96*k^5 := by
  have clock:=demand_band (by omega : 0<k)
  have moved:=analytic_band large
  exact ⟨clock.1,clock.2,moved.1,moved.2.1⟩

/-- Thirteen copies fail on every original quartic board from index 512 onward. -/
theorem thirteen_fail {k : ℕ} (large : 512≤k) : ¬ pays 13 k := by
  have kp : 0<k := by omega
  have kr : 1≤(k:ℝ) := by exact_mod_cast kp
  have input:=analytic_band (by omega : 2≤k)
  have gross:=earned_upper (n:=k^4) (pow_pos kp _)
  have cap:=(demand_band kp).1
  rw [pays_iff kp]
  intro proof
  have k56:=pow_le_pow_right₀ kr (by decide : 5≤6)
  have kbig := mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (by norm_num : (0:ℝ)≤512) (by exact_mod_cast large : (512:ℝ)≤k) 2)
    (pow_nonneg (Nat.cast_nonneg (α:=ℝ) k) 6)
  norm_num only [Nat.cast_ofNat] at proof
  nlinarith only [proof,input.2.1,input.2.2.1,gross,cap,k56,kbig,
    pow_pos (by exact_mod_cast kp : 0<(k:ℝ)) 6]

private theorem low_label {k d : ℕ} (late : 200000^2≤k) (short : d^8≤(k^4)^7) :
    d ≤ k^4/200000 := by
  apply (Nat.le_div_iff_mul_le (by decide : 0<200000)).mpr
  apply (Nat.pow_le_pow_iff_left (by decide : (8:ℕ)≠0)).mp
  have reserve : 200000^8≤k^4 := by
    exact Nat.pow_le_pow_left late 4
  rw [mul_pow]
  exact (Nat.mul_le_mul short reserve).trans_eq (by ring)

/-- Fifteen copies pay the exact original clock at every index from 200000 squared. -/
theorem fifteen_pay {k : ℕ} (late : 200000^2≤k) : pays 15 k := by
  have kp : 0<k := by omega
  have kr : 1≤(k:ℝ) := by exact_mod_cast kp
  let n:=k^4
  let N:=2*n
  let D:=n/200000
  have np : 0<n := pow_pos kp _
  have nr : 0<(n:ℝ) := by exact_mod_cast np
  have within : D≤2*n := (Nat.div_le_self n 200000).trans (by omega)
  have L:=earned_lower (n:=n) (D:=D) np within (fun _ h => low_label late h)
  have box:=analytic_band (by omega : 2≤k)
  have clock:=(demand_band kp).2
  have Np : 1 ≤ (N:ℝ) := by dsimp [N];exact_mod_cast (show 1≤2*n by omega)
  have root : Real.sqrt (N:ℝ)≤2*k^2 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    dsimp [N,n];push_cast; nlinarith only [pow_nonneg (Nat.cast_nonneg (α:=ℝ) k) 4]
  have cap := log_cap kp
  change Real.log ((N:ℝ)+1) ≤ 8*k at cap
  have logn := (Real.log_le_log (zero_lt_one.trans_le Np) (by linarith : (N:ℝ)≤N+1)).trans cap
  have repeats := Chebyshev.psi_sub_theta_le (x:=(N:ℝ)) Np
  have raw := mul_le_mul root logn (Real.log_nonneg Np) (by positivity)
  have small:=Chebyshev.psi_le_const_mul_self (x:=(D:ℝ)) (Nat.cast_nonneg _)
  have four : Real.log 4 ≤ 2 := by
    rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [Real.log_two_lt_d9.le]
  have dcap : 200000*(D:ℝ)≤n := by
    exact_mod_cast (Nat.mul_div_le n 200000)
  have stop:=mul_le_mul_of_nonneg_right four (Nat.cast_nonneg (α:=ℝ) D)
  have cost : Chebyshev.psi (N:ℝ)-Chebyshev.theta (N:ℝ)+Chebyshev.psi D ≤
      32*k^3 + (6/200000:ℝ)*n := by
    nlinarith only [raw,repeats,small,stop,dcap]
  have funded:=mul_le_mul_of_nonneg_left cost (by positivity : 0≤14*(n:ℝ))
  have nN : (N:ℝ)=2*(n:ℝ) := by dsimp [N];push_cast;rfl
  rw [nN] at funded
  dsimp only [n] at L funded
  push_cast at L funded
  have k57:=pow_le_pow_right₀ kr (by decide : 5≤7)
  have kbig := mul_le_mul_of_nonneg_right (by exact_mod_cast late : (200000:ℝ)^2≤k)
    (pow_nonneg (Nat.cast_nonneg (α:=ℝ) k) 7)
  rw [pays_iff kp]
  norm_num only [Nat.cast_ofNat]
  nlinarith only [clock,box.1,box.2.2.2,L,funded,k57,kbig,pow_nonneg (Nat.cast_nonneg (α:=ℝ) k) 7]

#print axioms PALRH.PrimeCopies.thirteen_fail
#print axioms PALRH.PrimeCopies.fifteen_pay
end PALRH.PrimeCopies
