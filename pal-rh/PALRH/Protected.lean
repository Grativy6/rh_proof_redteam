import PALRH.OneTick

open Finset
open scoped BigOperators
noncomputable section
namespace PALRH.OneTick

/-- One legal binary copy with scale m. -/
def binaryCopy (m k : ℕ) : ℚ := ((k/m)%2:ℕ)

theorem binaryCopy_mem {m : ℕ} (hm : 0<m) : binaryCopy m∈fits := by
  have eq : binaryCopy m = (2:ℚ) • dilate m (turn 2) := by
    funext k
    simp only [binaryCopy,dilate,turn,Pi.smul_apply,smul_eq_mul,Nat.cast_ofNat]
    ring
  rw [eq]
  apply fits.smul_mem
  by_cases one : m=1
  · have id : dilate m (turn 2) = turn 2 := by funext k; simp [dilate,one]
    rw [id]; exact turn_mem (by decide)
  · exact dilate_mem (by omega) (turn_mem (by decide))

private def pivot (m : ℕ) := binaryCopy m - binaryCopy (m+1)

private lemma pivot_before {k m : ℕ} (h : k<m) : pivot m k=0 := by
  simp [pivot,binaryCopy,Nat.div_eq_of_lt h,Nat.div_eq_of_lt (by omega : k<m+1)]

private lemma pivot_here {m : ℕ} (h : 0<m) : pivot m m=1 := by
  simp [pivot,binaryCopy,Nat.div_self h,Nat.div_eq_of_lt (by omega : m<m+1)]

private lemma pivot_cap (m k : ℕ) : ‖(pivot m k:ℝ)‖≤1 := by
  rcases Nat.mod_two_eq_zero_or_one (k/m) with a|a <;>
    rcases Nat.mod_two_eq_zero_or_one (k/(m+1)) with b|b <;> norm_num [pivot,binaryCopy,a,b]

private lemma target_sum {T f : ℕ → ℚ} (hT : bounded T) (hf : f∈fits) :
    Summable (fun n : ℕ => rowWeight n*((T (n+1):ℝ)-(f (n+1):ℝ))^2) := by
  obtain ⟨A,hA⟩ := hT
  obtain ⟨B,hB⟩ := (fit_properties hf).2
  have nonneg (n : ℕ) : 0≤rowWeight n*((T (n+1):ℝ)-(f (n+1):ℝ))^2 :=
    mul_nonneg (by unfold rowWeight; positivity) (sq_nonneg _)
  apply Summable.of_nonneg_of_le nonneg _ (rowWeight_hasSum.summable.mul_right ((A+B)^2))
  intro n
  apply mul_le_mul_of_nonneg_left _ (by unfold rowWeight; positivity)
  rw [←sq_abs ((T (n+1):ℝ)-(f (n+1):ℝ))]
  exact pow_le_pow_left₀ (abs_nonneg _) ((norm_sub_le _ _).trans (add_le_add (hA _) (hB _))) 2

private lemma real_loss (T f : ℕ → ℚ) :
    loss T f = ∑' n : ℕ, rowWeight n*((T (n+1):ℝ)-(f (n+1):ℝ))^2 := by simp [loss,cost]

/-- A single rational repair matches row m, preserves every earlier row and has
a quantitative full-loss bound independent of the previous fit's period. -/
theorem protect_row {S : Submodule ℚ (ℕ → ℚ)} (legal : S≤fits)
    (copies : ∀ m : ℕ, 0<m → binaryCopy m∈S) {T f : ℕ → ℚ} (hT : bounded T)
    (hf : f∈S) {m : ℕ} (hm : 0<m) :
    ∃ g ∈ S, (∀ k<m, g k=f k) ∧ g m=T m ∧
      loss T g ≤ (2+2*(m:ℝ)*(m+1))*loss T f := by
  let a := T m-f m
  let g := f+a • pivot m
  have hg : g∈S := S.add_mem hf (S.smul_mem a (S.sub_mem (copies m hm) (copies (m+1) (by omega))))
  refine ⟨g,hg,fun k hk => by simp [g,Pi.smul_apply,smul_eq_mul,pivot_before hk],
    by simp [g,a,Pi.smul_apply,smul_eq_mul,pivot_here hm],?_⟩
  have hl := (target_sum hT (legal hf)).le_tsum (m-1) (fun n _ =>
    mul_nonneg (by unfold rowWeight; positivity) (sq_nonneg _))
  rw [show m-1+1=m by omega,←real_loss T f] at hl
  have w : rowWeight (m-1) = 1/((m:ℝ)*(m+1)) := by
    simp only [rowWeight,Nat.cast_sub (by omega : 1≤m),Nat.cast_one]; ring
  rw [w] at hl
  have first : ((a:ℝ))^2 ≤ (m:ℝ)*(m+1)*loss T f := by
    have hdiv : ((T m:ℝ)-(f m:ℝ))^2/((m:ℝ)*(m+1)) ≤ loss T f := by simpa only [one_div,div_eq_inv_mul,mul_one] using hl
    simpa [a,mul_comm] using (div_le_iff₀ (show 0<(m:ℝ)*(m+1) by positivity)).mp hdiv
  have each (n : ℕ) : rowWeight n*((f (n+1):ℝ)-(g (n+1):ℝ))^2 ≤ rowWeight n*(a:ℝ)^2 := by
    simp only [g,Pi.add_apply,Pi.smul_apply,smul_eq_mul,Rat.cast_add,Rat.cast_mul,sub_add_cancel_left,neg_sq,mul_pow]
    have hu : (pivot m (n+1):ℝ)^2≤1 := by
      simpa only [Real.norm_eq_abs,sq_abs,one_pow] using
        pow_le_pow_left₀ (norm_nonneg _) (pivot_cap m (n+1)) 2
    apply mul_le_mul_of_nonneg_left _ (by unfold rowWeight; positivity)
    exact mul_le_of_le_one_right (sq_nonneg _) hu
  have step := (target_sum (fit_properties (legal hf)).2 (legal hg)).tsum_le_tsum each
    (rowWeight_hasSum.summable.mul_right ((a:ℝ)^2))
  rw [←real_loss,tsum_mul_right,rowWeight_hasSum.tsum_eq,one_mul] at step
  have tri := loss_triangle T f g hT (fit_properties (legal hf)).2 (fit_properties (legal hg)).2
  nlinarith

/-- Requiring any fixed finite positive prefix exactly costs nothing in the
all-tolerance limit when the supply of new legal scales remains open. -/
theorem exact_heads_iff {S : Submodule ℚ (ℕ → ℚ)} (legal : S≤fits)
    (copies : ∀ m : ℕ, 0<m → binaryCopy m∈S) (T : ℕ → ℚ) (hT : bounded T) :
    (∀ ε : ℝ, 0<ε → ∃ f ∈ S, loss T f < ε) ↔
    ∀ H : ℕ, ∀ ε : ℝ, 0<ε → ∃ g ∈ S, (∀ k : ℕ, 0<k → k≤H → g k=T k) ∧ loss T g < ε := by
  constructor
  · intro can H
    induction H with
    | zero =>
      intro ε hε
      obtain ⟨f,hf,he⟩ := can ε hε
      exact ⟨f,hf,fun k hk h => by omega,he⟩
    | succ H ih =>
      intro ε hε
      let C : ℝ := 2+2*((H+1:ℕ):ℝ)*(((H+1:ℕ):ℝ)+1)
      have pos : 0<C := by dsimp [C]; positivity
      obtain ⟨f,hf,hhead,hsmall⟩ := ih (ε/C) (div_pos hε pos)
      obtain ⟨g,hg,keep,hit,gain⟩ := protect_row legal copies hT hf (by omega : 0<H+1)
      refine ⟨g,hg,fun k hk hle => ?_,gain.trans_lt ?_⟩
      · by_cases top : k=H+1
        · simpa [top] using hit
        · exact (keep k (by omega)).trans (hhead k hk (by omega))
      · simpa only [mul_comm (loss T f) C] using (lt_div_iff₀ pos).mp hsmall
  · intro all ε pos
    obtain ⟨f,hf,_,small⟩ := all 0 ε pos
    exact ⟨f,hf,small⟩

#print axioms PALRH.OneTick.protect_row
#print axioms PALRH.OneTick.exact_heads_iff

/-- One index names both the head to preserve and the tolerance to attain.
The coefficient support can extend beyond this index. -/
def ProtectedCertificates : Prop :=
  ∀ H : ℕ, ∃ g ∈ fits, (∀ k : ℕ, 0<k → k≤H → g k=tick k) ∧ loss tick g < 1/((H:ℝ)+1)

theorem protected_iff_certificates : ProtectedCertificates ↔ FiniteCertificates := by
  rw [←first_tick_iff_certificates]
  have hb : bounded tick := ⟨1,fun k => by by_cases q:k=1 <;> simp [tick,q]⟩
  have exactHeads := exact_heads_iff (S:=fits) le_rfl (fun _ h => binaryCopy_mem h) tick hb
  constructor
  · intro exact ε he
    obtain ⟨H,hH⟩ := exists_nat_one_div_lt he
    obtain ⟨g,hg,_,small⟩ := exact H
    exact ⟨g,hg,small.trans hH⟩
  · intro can H
    exact exactHeads.mp can H (1/((H:ℝ)+1)) (by positivity)

theorem rh_of_protected_certificates (h : ProtectedCertificates) : RiemannHypothesis :=
  rh_of_finite_certificates (protected_iff_certificates.mp h)

#print axioms PALRH.OneTick.protected_iff_certificates
#print axioms PALRH.OneTick.rh_of_protected_certificates

end PALRH.OneTick
