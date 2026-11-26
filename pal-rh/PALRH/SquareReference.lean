import PALRH.ClockShortfall

open Finset
open scoped BigOperators
namespace PALRH.SquareReference
open LinearPrimeIntegral DoubledRuler PrimeCopies QuarticBoards RulerOmissions

/-- Integer reference after a specified deduction in the doubled ruler's original units. -/
def bill (k credit : ℕ) : ℕ :=
  (∑ r ∈ range (2*k^4), r^6) - (16*(k^4)^7+credit)

def pays (k credit : ℕ) : Prop :=
  (k^4+1)^(k^4*bill k credit) ≤ (k^4)^(k^4*bill k credit)*primeSettings (k^4)

noncomputable section
theorem area_from_credit {k credit : ℕ} {reserve : ℝ} (large : 2≤k)
    (creditCap : (credit:ℝ) ≤ reserve*(k:ℝ)^6*((2*k^4:ℕ):ℝ)^5)
    (pay : pays k credit) : error (k^4) ≤ (102+reserve)*(k:ℝ)^6 := by
  let n:=k^4
  let N:=2*n
  let B:=bill k credit
  let W:=∑ r ∈ range N,r^6
  have kp : 0<k := by omega
  have kr : 1≤(k:ℝ) := by exact_mod_cast kp
  have np : 0<n := pow_pos kp _
  have nr : 0<(n:ℝ) := by exact_mod_cast np
  have Np : 0<(N:ℝ) := by dsimp [N];positivity
  have spec : W≤B+(16*n^7+credit) := by
    dsimp [W,B,N,n,bill]
    omega
  have less : B≤W := Nat.sub_le _ _
  have paid := pay
  change (n+1)^(n*B) ≤ n^(n*B)*primeSettings n at paid
  have packet : 0 < primeSettings n := by
    apply prod_pos
    intro d hd
    split_ifs with yes
    · exact pow_pos yes.1.pos _
    · decide
  have logs:=Real.log_le_log (by positivity : 0<(((n+1)^(n*B):ℕ):ℝ))
    (by exact_mod_cast paid : (((n+1)^(n*B):ℕ):ℝ)≤((n^(n*B)*primeSettings n:ℕ):ℝ))
  push_cast at logs
  rw [Real.log_mul (by positivity) (by positivity)] at logs
  simp only [Real.log_pow, Nat.cast_mul] at logs
  have changeLog:=Real.one_sub_inv_le_log_of_pos (show 0<((n:ℝ)+1)/n by positivity)
  rw [Real.log_div (by positivity) nr.ne',show 1-(((n:ℝ)+1)/n)⁻¹=1/(n+1) by field_simp;ring] at changeLog
  have spent:=mul_le_mul_of_nonneg_left changeLog (by positivity : 0≤(n:ℝ)*B)
  have spent2 : (n:ℝ)*B/(n+1) ≤ Real.log (primeSettings n:ℝ) := by
    calc
      _ = (n:ℝ)*B*(1/(n+1)) := by ring
      _ ≤ _ := spent.trans (by rw [mul_sub]; linarith only [logs])
  have round : (B:ℝ) ≤ Real.log (primeSettings n:ℝ)+(W:ℝ)/(n+1) := by
    have same : (B:ℝ)=(n:ℝ)*B/(n+1)+B/(n+1) := by field_simp
    have rest:=div_le_div_of_nonneg_right (by exact_mod_cast less : (B:ℝ)≤W) (by positivity : 0≤(n:ℝ)+1)
    linarith only [same,spent2,rest]
  have power := DoubledMass.boundary_bracket N
  change (N:ℝ)^7-7*(N:ℝ)^6 ≤ 7*(∑ r ∈ range N,(r:ℝ)^6) ∧ _ at power
  have Wcast : (W:ℝ) = ∑ r ∈ range N,(r:ℝ)^6 := by dsimp [W];push_cast;rfl
  rw [←Wcast] at power
  have nN : (N:ℝ)=2*(n:ℝ) := by dsimp [N];push_cast;rfl
  have toll : (W:ℝ)/(n+1) ≤ 4*(n:ℝ)*(N:ℝ)^5 := by
    apply (div_le_iff₀ (by positivity : 0<(n:ℝ)+1)).mpr
    rw [nN] at power ⊢
    nlinarith only [power.2,pow_nonneg nr.le 6,pow_nonneg nr.le 7]
  have ordered : (W:ℝ)≤(B:ℝ)+(16*(n:ℝ)^7+credit) := by exact_mod_cast spec
  have ref := creditCap
  have actual:=earned_upper np
  obtain ⟨_,_,_,outlayCap⟩:=clock_price_bands large
  have raw : fullWalk n ≤ outlay n - Real.log (primeSettings n:ℝ)/(N:ℝ)^5 := by
    change Real.log (primeSettings n:ℝ)/(N:ℝ)^5≤outlay n-fullWalk n at actual
    linarith only [actual]
  have useRaw:=mul_le_mul_of_nonneg_right raw (pow_nonneg Np.le 5)
  rw [sub_mul,div_mul_cancel₀ _ (pow_pos Np _).ne'] at useRaw
  have used:=mul_le_mul_of_nonneg_right outlayCap (pow_nonneg Np.le 5)
  change outlay n*(N:ℝ)^5 ≤ _ at used
  have ke : (n:ℝ)=(k:ℝ)^4 := by dsimp [n];push_cast;rfl
  change (credit:ℝ) ≤ reserve*(k:ℝ)^6*(N:ℝ)^5 at ref
  have k46 := pow_le_pow_right₀ kr (by decide : 4≤6)
  have k56 := pow_le_pow_right₀ kr (by decide : 5≤6)
  apply le_of_mul_le_mul_right (a:=(N:ℝ)^5) _ (pow_pos Np _)
  change (fullWalk n-(n:ℝ)^2/2)*(N:ℝ)^5 ≤ _
  simp only [nN,ke] at power toll ordered ref useRaw used round ⊢
  have a:=mul_le_mul_of_nonneg_right k46 (by positivity : 0≤(2*(k:ℝ)^4)^5)
  have b:=mul_le_mul_of_nonneg_right k56 (by positivity : 0≤(2*(k:ℝ)^4)^5)
  nlinarith only [useRaw,used,power.1,toll,round,ordered,ref,a,b]

#print axioms PALRH.SquareReference.area_from_credit
end
end PALRH.SquareReference
