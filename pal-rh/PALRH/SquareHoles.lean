import PALRH.ClockShortfall

open Finset
open scoped BigOperators
namespace PALRH.SquareHoles
open LinearPrimeIntegral DoubledRuler DoubledPrice PrimeCopies QuarticBoards RulerOmissions

/-- Differences of squares in the second quotient band. Both factors exceed one. -/
def trace (n b : ℕ) : Finset ℕ :=
  ((Icc 1 (b-2)).image (fun t => b^2-t^2)).filter (fun m => 2*n<3*m ∧ m≤n)

def erased (k s : ℕ) : Finset ℕ :=
  (range s).biUnion (fun a => trace (k^4) (k^2+a))

def refund (k s : ℕ) : ℕ := ∑ d ∈ erased k s,(extra (k^4) d).toNat

/-- The reciprocal cutoff integral, with the old quadratic reference and
the returns of distinct composite labels removed. -/
def bill (k s : ℕ) : ℕ :=
  (∑ r ∈ range (2*k^4), r^6) - (16*(k^4)^7+refund k s)

def pays (k s : ℕ) : Prop :=
  (k^4+1)^(k^4*bill k s) ≤ (k^4)^(k^4*bill k s) * primeSettings (k^4)

theorem erased_label {k s d : ℕ} (hd : d∈erased k s) :
    0<d ∧ d≤k^4 ∧ ¬d.Prime := by
  obtain ⟨a,_,ha⟩:=mem_biUnion.mp hd
  obtain ⟨image,band⟩:=mem_filter.mp ha
  obtain ⟨t,ht,same⟩:=mem_image.mp image
  let b:=k^2+a
  have tp:0<t := (mem_Icc.mp ht).1
  have enough:t≤b-2 := (mem_Icc.mp ht).2
  have inside:t≤b := by omega
  have factors : (b-t)*(b+t)=b^2-t^2 := by
    have equal : b-t+t=b := Nat.sub_add_cancel inside
    apply Nat.eq_sub_of_add_eq
    calc
      (b-t)*(b+t)+t^2 = (b-t+t)^2 := by
        nth_rw 2 [←equal]
        ring
      _ = b^2 := congrArg (fun x : ℕ => x^2) equal
  have pos:0<d := by omega
  refine ⟨pos,band.2,?_⟩
  change b^2-t^2=d at same
  rw [←same,←factors]
  apply Nat.not_prime_mul <;> omega

theorem trace_count (n b : ℕ) : (trace n b).card≤b := by
  unfold trace
  exact (card_filter_le _ _).trans
    (card_image_le.trans (by simp [Nat.card_Icc]))

theorem erased_count (k s : ℕ) :
    (erased k s).card ≤ s*(k^2+s) := by
  unfold erased
  apply card_biUnion_le.trans
  calc
    _ ≤ ∑ _ ∈ range s, (k^2+s) := sum_le_sum (s:=range s) fun a ha =>
      (trace_count (k^4) (k^2+a)).trans (by have h:=mem_range.mp ha;omega)
    _ = _ := by simp

noncomputable section
private theorem refund_cap {k s : ℕ} (within : s≤k^2) :
    (refund k s:ℝ) ≤ (28:ℝ)*s*(k:ℝ)^6*(((2*k^4:ℕ):ℝ)^5) := by
  let N:=2*k^4
  have per {d : ℕ} (hd : d∈erased k s) : ((extra (k^4) d).toNat:ℝ) ≤ 7*(N:ℝ)^6 := by
    obtain ⟨dp,cap,_⟩:=erased_label hd
    have near : d≤N := cap.trans (by dsimp [N];omega)
    have same : ((extra (k^4) d).toNat:ℝ)=(extra (k^4) d:ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg (extra_nonneg dp near)
    rw [same]
    exact extra_cap dp near
  have count : (erased k s).card≤2*s*k^2 := (erased_count k s).trans
    (by nlinarith only [Nat.mul_le_mul_left s within])
  have total:=sum_le_sum (s:=erased k s) (fun d hd => per hd)
  rw [sum_const,nsmul_eq_mul] at total
  have fee:=mul_le_mul_of_nonneg_right (by exact_mod_cast count :
      ((erased k s).card:ℝ)≤2*s*(k:ℝ)^2) (by positivity : 0≤7*(N:ℝ)^6)
  unfold refund
  push_cast
  dsimp [N] at total fee
  push_cast at total fee
  nlinarith only [total,fee]

/-- Paying the bill after removing s actual square traces gives a pointwise area
estimate with its dependence on the physical number of centers exposed. -/
theorem area_of_payment {k s : ℕ} (large : 2≤k) (within : s≤k^2) (pay : pays k s) :
    error (k^4) ≤ (102+28*(s:ℝ))*(k:ℝ)^6 := by
  let n:=k^4
  let N:=2*n
  let B:=bill k s
  let W:=∑ r ∈ range N,r^6
  have kp : 0<k := by omega
  have kr : 1≤(k:ℝ) := by exact_mod_cast kp
  have np : 0<n := pow_pos kp _
  have nr : 0<(n:ℝ) := by exact_mod_cast np
  have Np : 0<(N:ℝ) := by dsimp [N];positivity
  have spec : W≤B+(16*n^7+refund k s) := by
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
  have ordered : (W:ℝ)≤(B:ℝ)+(16*(n:ℝ)^7+refund k s) := by exact_mod_cast spec
  have ref:=refund_cap within
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
  change (refund k s:ℝ) ≤ 28*(s:ℝ)*(k:ℝ)^6*(N:ℝ)^5 at ref
  have k46 := pow_le_pow_right₀ kr (by decide : 4≤6)
  have k56 := pow_le_pow_right₀ kr (by decide : 5≤6)
  apply le_of_mul_le_mul_right (a:=(N:ℝ)^5) _ (pow_pos Np _)
  change (fullWalk n-(n:ℝ)^2/2)*(N:ℝ)^5 ≤ _
  simp only [nN,ke] at power toll ordered ref useRaw used round ⊢
  have a:=mul_le_mul_of_nonneg_right k46 (by positivity : 0≤(2*(k:ℝ)^4)^5)
  have b:=mul_le_mul_of_nonneg_right k56 (by positivity : 0≤(2*(k:ℝ)^4)^5)
  nlinarith only [useRaw,used,power.1,toll,round,ordered,ref,a,b]

theorem rh_of_two_traces (K : ℕ) (late : ∀ k : ℕ, K≤k → pays k 2) : RiemannHypothesis := by
  apply OneSidedBoard.rh_of_eventual_upper_area (max K 2) (C:=158) (by norm_num)
  intro k hk _
  have large:2≤k := (le_max_right _ _).trans hk
  have bound:=area_of_payment large (by nlinarith only [large, Nat.pow_le_pow_left large 2] : 2≤k^2)
    (late k ((le_max_left _ _).trans hk))
  norm_num at bound
  exact bound

#print axioms PALRH.SquareHoles.erased_label
#print axioms PALRH.SquareHoles.area_of_payment
#print axioms PALRH.SquareHoles.rh_of_two_traces
end
end PALRH.SquareHoles
