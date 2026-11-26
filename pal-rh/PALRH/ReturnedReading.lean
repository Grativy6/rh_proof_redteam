import PALRH.ReturnedHorizon

open Finset
open scoped BigOperators

noncomputable section
namespace PALRH.ReturnedReading
open ShapeObservation PrefixReturn ShapeStrip ReturnedHorizon

private def increment (n d : ℕ) : ℝ :=
  (tickAt n d:ℝ)+(if d≤n.sqrt then (n.sqrt:ℝ) else 0)-n.sqrt

private theorem cutset (n m : ℕ) : (Icc 1 m).filter (fun d => d≤n.sqrt)=Icc 1 (min m n.sqrt) := by
  ext d;simp only [mem_filter,mem_Icc,le_min_iff];tauto

private theorem plain (n m : ℕ) :
    plainPrefix (increment n) m=(∑ d ∈ Icc 1 m,(tickAt n d:ℝ))+
      (n.sqrt:ℝ)*(min m n.sqrt:ℕ)-(n.sqrt:ℝ)*m := by
  unfold plainPrefix increment
  rw [sum_sub_distrib,sum_add_distrib,←sum_filter,cutset]
  simp [mul_comm]

private theorem weight (n m : ℕ) (mn : m≤n) :
    weighted n (increment n) m=(prefixJobs n m+smallReturn n m:ℕ)-(n.sqrt:ℝ)*plainArea n m := by
  have eq : weighted n (increment n) m=weighted n (fun d => (tickAt n d:ℝ)-n.sqrt) m+
      ∑ d ∈ Icc 1 m,(if d≤n.sqrt then ((n:ℝ)-d)*(n.sqrt:ℝ) else 0) := by
    unfold weighted
    rw [←sum_add_distrib]
    apply sum_congr rfl
    intro d _
    dsimp [increment]
    split_ifs <;> ring
  rw [eq,ShapeObservation.reading n m n.sqrt mn,←sum_filter,cutset]
  have price : ∑ d ∈ Icc 1 (min m n.sqrt),((n:ℝ)-d)*(n.sqrt:ℝ)=(smallReturn n m:ℝ) := by
    unfold smallReturn plainArea
    push_cast;rw [mul_sum]
    apply sum_congr rfl
    intro d hd
    rw [Nat.cast_sub (((mem_Icc.mp hd).2.trans (min_le_left _ _)).trans mn)]
    ring
  rw [price,Nat.cast_add]
  ring

private theorem blank_ticks (n m : ℕ) (small : m≤n.sqrt) :
    (∑ d ∈ Icc 1 m,(tickAt n d:ℝ))=0 := by
  apply sum_eq_zero
  intro d hd
  have hi:=(mem_Icc.mp hd).2.trans small
  have dn:=hi.trans (Nat.sqrt_le_self n)
  have no : ¬(2≤d ∧ d.gcd n.sqrt.factorial=1) := by
    rintro ⟨lo,g⟩
    exact (not_lt_of_ge hi) ((SieveFrame.factorial_test lo dn).mp g).2
  simp [tickAt,no]

/-- A bound on the change of the prime-counting error between the root and each later
cut controls the genuine weighted board reading, including both signs and all rounding. -/
theorem paid_readout (n M : ℕ) (np : 0<n) (Mn : M≤n) {D : ℝ} (dn : 0≤D)
    (primeChange : ∀ i : ℕ, n.sqrt < i → i ≤ M → |(Chebyshev.theta i-i)-(Chebyshev.theta n.sqrt-n.sqrt)| ≤ D)
    {m : ℕ} (mh : m≤M) :
    |(prefixJobs n m+smallReturn n m:ℕ)-(n.sqrt:ℝ)*plainArea n m|≤
      (n:ℝ)*(3*M+(n.sqrt:ℝ)*D) := by
  let B:ℝ:=3*M+(n.sqrt:ℝ)*D
  have bn : 0≤B := by dsimp [B];positivity
  have each (i : ℕ) (ih : i≤M) : |plainPrefix (increment n) i|≤B := by
    rw [plain]
    by_cases little : i≤n.sqrt
    · rw [blank_ticks n i little,min_eq_left little,zero_add,sub_self,abs_zero]
      exact bn
    · have dist:=primeChange i (lt_of_not_ge little) ih
      have rem:=tick_remainder n i np (ih.trans Mn)
      dsimp only at rem
      rw [min_eq_right (le_of_not_ge little)] at rem ⊢
      have plus : (∑ d ∈ Icc 1 i,(tickAt n d:ℝ))+(n.sqrt:ℝ)*n.sqrt-(n.sqrt:ℝ)*i=
          ((∑ d ∈ Icc 1 i,(tickAt n d:ℝ))-(n.sqrt:ℝ)*(Chebyshev.theta i-Chebyshev.theta n.sqrt))+
          (n.sqrt:ℝ)*((Chebyshev.theta i-i)-(Chebyshev.theta n.sqrt-n.sqrt)) := by ring
      rw [plus]
      apply (abs_add_le _ _).trans
      rw [abs_of_nonneg rem.1,abs_mul,abs_of_nonneg (Nat.cast_nonneg n.sqrt)]
      exact add_le_add (rem.2.trans (by exact_mod_cast Nat.mul_le_mul_left 3 ih))
        (mul_le_mul_of_nonneg_left dist (Nat.cast_nonneg _))
  rw [←weight n m (mh.trans Mn),prefix_identity]
  apply (abs_add_le _ _).trans
  have tail : |∑ i ∈ range m,plainPrefix (increment n) i|≤(m:ℝ)*B := by
    calc
      _ ≤ ∑ i ∈ range m,|plainPrefix (increment n) i| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ ∈ range m,B := sum_le_sum (fun i hi => each i ((mem_range.mp hi).le.trans mh))
      _ = _ := by simp
  have lead : 0≤(n:ℝ)-m := sub_nonneg.mpr (by exact_mod_cast mh.trans Mn)
  rw [abs_mul,abs_of_nonneg lead]
  calc
    _ ≤ ((n:ℝ)-m)*B+m*B := add_le_add (mul_le_mul_of_nonneg_left (each m mh) lead) tail
    _ = _ := by dsimp [B];ring


/-- A price for the observed change of theta on one board pays that board's exact
integer comparison. The finite prime estimates in the paper enter at this interface. -/
theorem one_board_from_prime_change (j : ℕ) {D : ℝ} (dn : 0≤D)
    (delta : ∀ i : ℕ, root j < i → i ≤ 16^j → |(Chebyshev.theta i-i)-(Chebyshev.theta (root j)-root j)| ≤ D)
    (price : 13*(3*((16^j:ℕ):ℝ)+(root j:ℝ)*D)≤(board j:ℝ)) :
    13*largestError j≤(board j)^2 := by
  let n:=board j
  let M:ℕ:=16^j
  let x:=root j
  have np : 0<n := by dsimp [n,board,root];positivity
  have nx : n.sqrt=x := Nat.sqrt_eq' _
  have first : 4^j≤x := by
    change 4^j≤4^(j+1)*(j+1)^2
    have a : 4^j≤4^(j+1) := by rw [pow_succ];omega
    exact a.trans (Nat.le_mul_of_pos_right _ (Nat.pow_pos (Nat.succ_pos _)))
  have Mn : M≤n := by
    change 16^j≤x^2
    have sq : (4^j)^2=(16:ℕ)^j := by rw [←pow_mul,mul_comm j 2,pow_mul];rfl
    rw [←sq];exact Nat.pow_le_pow_left first 2
  have cost : (n:ℝ)*(3*(M:ℝ)+(x:ℝ)*D)*13≤(n:ℝ)^2 := by
    nlinarith only [mul_le_mul_of_nonneg_left price (Nat.cast_nonneg (α:=ℝ) n)]
  have each (i : ℕ) (ih : i≤M) : mismatch j i≤n^2/13 := by
    have localDelta (a : ℕ) (large : n.sqrt<a) (small : a≤M) :
        |(Chebyshev.theta a-a)-(Chebyshev.theta n.sqrt-n.sqrt)|≤D := by
      rw [nx] at large ⊢;exact delta a large small
    have amount:=paid_readout n M np Mn dn localDelta ih
    rw [nx] at amount
    obtain ⟨left,right⟩:=abs_sub_le_iff.mp amount
    have f : fits j i := by
      change 13*(prefixJobs n i+smallReturn n i)≤13*(x*plainArea n i)+n^2 ∧
        13*(x*plainArea n i)≤13*(prefixJobs n i+smallReturn n i)+n^2
      constructor
      · exact_mod_cast (show (13:ℝ)*((prefixJobs n i+smallReturn n i:ℕ):ℝ)≤
            13*((x:ℝ)*plainArea n i)+(n:ℝ)^2 by nlinarith only [left,cost])
      · exact_mod_cast (show (13:ℝ)*((x:ℝ)*plainArea n i)≤
            13*((prefixJobs n i+smallReturn n i:ℕ):ℝ)+(n:ℝ)^2 by nlinarith only [right,cost])
    exact (Nat.le_div_iff_mul_le (by decide : 0<13)).mpr (by simpa [Nat.mul_comm] using (one_board j i).mp f)
  have top : largestError j≤n^2/13 :=
    Finset.sup_le (fun i hi => each i (by simpa [M] using mem_range.mp hi))
  simpa [n,Nat.mul_comm] using (Nat.le_div_iff_mul_le (by decide : 0<13)).mp top

#print axioms PALRH.ReturnedReading.one_board_from_prime_change

#print axioms PALRH.ReturnedReading.paid_readout
end PALRH.ReturnedReading
