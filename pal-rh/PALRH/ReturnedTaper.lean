import PALRH.ReturnedReading
import PALRH.OrderedTransport

open Finset
open scoped BigOperators

namespace PALRH.ReturnedTaper

/-- A decreasing nonnegative reweighting only spends the first weight times the
largest signed prefix bound. The input increments may have either sign. -/
theorem positive_coefficients (m : ℕ) (w g : ℕ → ℝ) {E : ℝ}
    (down : ∀ i<m, w (i+1)≤w i) (last : 0≤w m)
    (cap : ∀ k≤m, (∑ i ∈ range k,g i)≤E) :
    (∑ i ∈ range m,w i*g i)≤w 0*E := by
  have along (k : ℕ) (inside : k≤m) :
      (∑ i ∈ range k,w i*g i)≤(w 0-w k)*E+w k*(∑ i ∈ range k,g i) := by
    induction k with
    | zero => simp
    | succ k ih =>
      have old:=ih (by omega)
      have step:=mul_le_mul_of_nonneg_left (cap (k+1) inside) (sub_nonneg.mpr (down k (by omega)))
      rw [sum_range_succ] at step
      rw [sum_range_succ,sum_range_succ]
      nlinarith only [old,step]
  nlinarith only [along m le_rfl,mul_le_mul_of_nonneg_left (cap m le_rfl) last]

/-- Zero index i represents distance i+1. A smaller triangular reading is a
positive combination of the longer board's signed prefix readings. -/
theorem shorter_taper (n m : ℕ) (room : m+1<n) (v : ℕ → ℝ) {E : ℝ}
    (cap : ∀ k≤m, (∑ i ∈ range k,((n:ℝ)-i-1)*v i)≤E) :
    (∑ i ∈ range m,((m:ℝ)-i)*v i)≤(m:ℝ)/(n-1)*E := by
  let w:=fun i : ℕ => ((m:ℝ)-i)/((n:ℝ)-i-1)
  let g:=fun i : ℕ => ((n:ℝ)-i-1)*v i
  have nr : (m:ℝ)+1<n := by exact_mod_cast room
  have down (i : ℕ) (im : i<m) : w (i+1)≤w i := by
    have ir : (i:ℝ)+1≤m := by exact_mod_cast im
    dsimp [w];push_cast
    apply (div_le_div_iff₀ (by linarith) (by linarith)).mpr
    nlinarith only [nr]
  have zero : 0≤w m := by simp [w]
  have bound:=positive_coefficients m w g down zero cap
  have eq : (∑ i ∈ range m,w i*g i)=∑ i ∈ range m,((m:ℝ)-i)*v i := by
    apply sum_congr rfl
    intro i hi
    have im : (i:ℝ)<m := by exact_mod_cast (mem_range.mp hi)
    have nz : (n:ℝ)-i-1≠0 := by linarith
    dsimp [w,g];field_simp
  rw [eq] at bound
  simpa [w] using bound

theorem shorter_taper_lower (n m : ℕ) (room : m+1<n) (v : ℕ → ℝ) {E : ℝ}
    (floor : ∀ k≤m, -E≤∑ i ∈ range k,((n:ℝ)-i-1)*v i) :
    -((m:ℝ)/(n-1)*E)≤∑ i ∈ range m,((m:ℝ)-i)*v i := by
  have h:=shorter_taper n m room (fun i => -v i) (E:=E) (by
    intro k hk
    simpa only [mul_neg,Finset.sum_neg_distrib,neg_le] using floor k hk)
  simpa only [mul_neg,Finset.sum_neg_distrib,neg_le] using h


/-- A buffer whose released ordinals only increase gives a single compatible placement
at all cuts. Its first group may already use the initially available pocket. -/
theorem prefix_placement (N : ℕ) (mass room : ℕ → ℕ) (grows : Monotone room) :
    (∀ p<N, (∑ i ∈ range (p+1),mass i)≤room p) ↔
    ∃ put : ℕ → ℕ → ℕ, (∀ p<N, ∀ t<mass p, put p t<room p) ∧
      (∀ p<N, ∀ q<N, ∀ t<mass p, ∀ u<mass q, put p t=put q u → p=q ∧ t=u) := by
  have interval (p : ℕ) : Icc 0 p=range (p+1) := by ext i;simp
  constructor
  · intro cap
    have all (i j : ℕ) (_ij : i≤j) (jn : j<N) :
        (0:ℕ)+∑ k ∈ Icc i j,mass k≤room j := by
      rw [zero_add]
      apply le_trans _ (cap j jn)
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro a ha;exact mem_range.mpr (Nat.lt_succ_of_le (mem_Icc.mp ha).2)
      · intro _ _ _;omega
    obtain ⟨lands,inj⟩:=OrderedTransport.greedy_injection (left:=fun _ => 0) all
    refine ⟨fun p t => OrderedTransport.firstSlot (fun _ => 0) mass p+t,?_,?_⟩
    · intro p pn t tm;exact (mem_Ico.mp (lands p pn t tm)).2
    · intro p _ q _ t tm u um eq;exact inj p q t tm u um eq
  · rintro ⟨put,lands,inj⟩ p pn
    have small (i : ℕ) (hin : i<N) (t : ℕ) (ht : t<mass i) :
        put i t∈Ico 0 (room i) := mem_Ico.mpr ⟨Nat.zero_le _,lands i hin t ht⟩
    have h:=OrderedTransport.necessary_interval (left:=fun _ => 0) (right:=room)
      (fun _ _ _ => le_rfl) grows (fun _ _ => Nat.zero_le _) put small inj (i:=0) (j:=p) (Nat.zero_le p) pn
    simpa [interval] using h

#print axioms PALRH.ReturnedTaper.prefix_placement

#print axioms PALRH.ReturnedTaper.shorter_taper
#print axioms PALRH.ReturnedTaper.shorter_taper_lower
end PALRH.ReturnedTaper
