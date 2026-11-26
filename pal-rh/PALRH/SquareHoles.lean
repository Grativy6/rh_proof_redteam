import PALRH.SquareReference

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
  exact SquareReference.area_from_credit large (refund_cap within) pay

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
