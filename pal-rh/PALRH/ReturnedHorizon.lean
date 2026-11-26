import PALRH.PrefixReturn

open Finset
open scoped BigOperators

noncomputable section
namespace PALRH.ReturnedHorizon
open PrefixReturn ShapeObservation ShapeStrip

def root (j : ℕ) := 4^(j+1)*(j+1)^2
def board (j : ℕ) := (root j)^2

/-- Pay the missing short distances in the same units as the receiving strip.
Both inequalities use only integer counts and a fixed fraction of the board area. -/
def fits (j m : ℕ) : Prop :=
  let n:=board j
  let seen:=prefixJobs n m+smallReturn n m
  let reference:=root j*plainArea n m
  13*seen≤13*reference+n^2 ∧ 13*reference≤13*seen+n^2

private theorem cost_of_return (n m : ℕ) : smallReturn n m≤n^2 := by
  have area (v : ℕ) : plainArea n v≤n*v := by
    unfold plainArea
    calc
      _ ≤ ∑ _ ∈ Icc 1 v,n := sum_le_sum (fun d _ => Nat.sub_le n d)
      _ = _ := by simp [mul_comm]
  have sq : n.sqrt^2≤n := by simpa [pow_two] using Nat.sqrt_le n
  calc
    _ ≤ n.sqrt*(n*min m n.sqrt) := Nat.mul_le_mul_left _ (area _)
    _ ≤ n.sqrt*(n*n.sqrt) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (min_le_right _ _))
    _ = n*n.sqrt^2 := by ring
    _ ≤ n^2 := by simpa only [pow_two] using Nat.mul_le_mul_left n sq

private theorem covers (j : ℕ) : 4*16^j≤board j := by
  have sq : ((4:ℕ)^j)^2=16^j := by rw [←pow_mul,mul_comm j 2,pow_mul];rfl
  have one : 1≤(j+1)^2 := Nat.pow_pos (Nat.succ_pos _)
  have r : 4*4^j≤root j := by
    unfold root;rw [pow_succ];nlinarith only [Nat.mul_le_mul_left (4^j*4) one]
  have b:=Nat.pow_le_pow_left r 2
  change 4*16^j≤(root j)^2
  rw [←sq]
  nlinarith only [b]

private theorem reading_error (data : ∀ j m : ℕ, m≤16^j → fits j m)
    {j m : ℕ} (mh : m≤16^j) :
    |Chebyshev.theta m-(m:ℝ)|≤28*((4:ℝ)^j*((j:ℝ)+1)^2) := by
  let n:=board j
  let x:=root j
  have rootPos : 0<x := by dsimp [x,root];positivity
  have xr : 0<(x:ℝ) := by exact_mod_cast rootPos
  have np : 0<n := Nat.pow_pos rootPos
  have nr : 0<(n:ℝ) := by exact_mod_cast np
  have xsq : (n:ℝ)=(x:ℝ)^2 := by dsimp [n,x,board];push_cast;rfl
  have nx : n.sqrt=x := Nat.sqrt_eq' _
  have narrow:=covers j
  have mn : m≤n := (show m≤4*16^j by omega).trans narrow
  have obs (i : ℕ) (ih : i≤16^j) :
      |weighted n (fun d => (tickAt n d:ℝ)-x) i|≤2*(n:ℝ)^2 := by
    have inn : i≤n := (show i≤4*16^j by omega).trans narrow
    rw [ShapeObservation.reading n i x inn]
    obtain ⟨a,b⟩:=data j i ih
    change 13*(prefixJobs n i+smallReturn n i)≤13*(x*plainArea n i)+n^2 at a
    change 13*(x*plainArea n i)≤13*(prefixJobs n i+smallReturn n i)+n^2 at b
    have left : prefixJobs n i≤x*plainArea n i+2*n^2 := by omega
    have bound:=cost_of_return n i
    have right : x*plainArea n i≤prefixJobs n i+2*n^2 := by omega
    have l : (prefixJobs n i:ℝ)≤(x:ℝ)*plainArea n i+2*(n:ℝ)^2 := by exact_mod_cast left
    have r : (x:ℝ)*plainArea n i≤(prefixJobs n i:ℝ)+2*(n:ℝ)^2 := by exact_mod_cast right
    exact abs_sub_le_iff.mpr ⟨by linarith only [l],by linarith only [r]⟩
  have f:=untilted n (16^j) np narrow _ (by positivity) obs m mh
  have div : 2*(2*(n:ℝ)^2)/n=4*n := by field_simp;norm_num
  rw [div] at f
  have flat : |(∑ d ∈ Icc 1 m,(tickAt n d:ℝ))-(x:ℝ)*m|≤4*n := by
    simpa [plainPrefix,Finset.sum_sub_distrib,mul_comm] using f
  have logCost:=prefix_calibration n m np mn
  rw [nx,abs_sub_comm] at logCost
  have fee : |(x:ℝ)*(Chebyshev.theta m-(m:ℝ))|≤7*n := by
    calc
      _ = |((x:ℝ)*Chebyshev.theta m-(∑ d ∈ Icc 1 m,(tickAt n d:ℝ)))+
          ((∑ d ∈ Icc 1 m,(tickAt n d:ℝ))-(x:ℝ)*m)| := by ring_nf
      _ ≤ _ := (abs_add_le _ _).trans (by linarith only [logCost,flat])
  rw [abs_mul,abs_of_pos xr,xsq] at fee
  have result : |Chebyshev.theta m-(m:ℝ)|≤7*x := by
    apply le_of_mul_le_mul_left (a:=(x:ℝ)) _ xr
    nlinarith only [fee]
  convert result using 1
  dsimp [x,root];push_cast;rw [pow_succ (4:ℝ) j];ring

/-- All scales, one rational allowance and no unspecified threshold or normalization. -/
theorem rh_of_returned_horizons (data : ∀ j m : ℕ, m≤16^j → fits j m) : RiemannHypothesis := by
  apply (DyadicShape.infer_density_and_rh (fun _ => 1) ?_).2
  intro b bh _
  obtain ⟨D,dn,price⟩:=root_price b bh
  refine ⟨28*D,by positivity,?_⟩
  intro j m _ mh
  rw [one_mul]
  exact (reading_error data mh).trans (by linarith only [price j])


/-- Both directions of error are retained by a single natural number. -/
def mismatch (j m : ℕ) : ℕ :=
  let seen:=prefixJobs (board j) m+smallReturn (board j) m
  let reference:=root j*plainArea (board j) m
  (seen-reference)+(reference-seen)

def largestError (j : ℕ) := (range (16^j+1)).sup (mismatch j)

theorem one_board (j m : ℕ) : fits j m ↔ 13*mismatch j m≤(board j)^2 := by
  dsimp only [fits,mismatch]
  omega

/-- One whole-number comparison per board, with the amount, scale and origin fixed. -/
theorem rh_of_one_thirteenth (every : ∀ j : ℕ, 13*largestError j≤(board j)^2) :
    RiemannHypothesis := by
  apply rh_of_returned_horizons
  intro j m mh
  apply (one_board j m).mpr
  have under : mismatch j m≤largestError j := Finset.le_sup (f:=mismatch j) (mem_range.mpr (by omega))
  exact (Nat.mul_le_mul_left 13 under).trans (every j)

theorem unreturned_root {x : ℕ} (two : 2≤x) :
    prefixJobs (x^2) x=0 ∧ (x^2)^2<13*(x*plainArea (x^2) x) := by
  let n:=x^2
  have nx : n.sqrt=x := Nat.sqrt_eq' _
  have blank:=first_strip n x (by rw [nx])
  simp only [smallReturn,nx,min_self] at blank
  have rootRoom : 2*x≤n := by dsimp [n];nlinarith only [Nat.mul_le_mul_left x two]
  have half : n*x≤2*plainArea n x := by
    calc
      _ = ∑ _ ∈ Icc 1 x,n := by simp [mul_comm]
      _ ≤ ∑ i ∈ Icc 1 x,2*(n-i) := by
        apply sum_le_sum
        intro i hi
        have ix:=(mem_Icc.mp hi).2
        omega
      _ = _ := (Finset.mul_sum _ _ _).symm
  have price := Nat.mul_le_mul_left x half
  have pos : 0<n^2 := by dsimp [n];positivity
  have eq : x*(n*x)=n^2 := by dsimp [n];ring
  rw [eq] at price
  change prefixJobs n x=0 ∧ n^2<13*(x*plainArea n x)
  exact ⟨by omega,by nlinarith only [price,pos]⟩

#print axioms PALRH.ReturnedHorizon.rh_of_one_thirteenth
#print axioms PALRH.ReturnedHorizon.unreturned_root

#print axioms PALRH.ReturnedHorizon.rh_of_returned_horizons
end PALRH.ReturnedHorizon
