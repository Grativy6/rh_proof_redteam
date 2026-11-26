import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic

open Finset
open scoped BigOperators

namespace PALRH.BenfordBlocks

/-- Approximate the increments on this block while retaining the actual incoming phase. -/
theorem local_trace (z : ℕ → ℂ) (q : ℂ) (unit : ‖q‖=1) {H : ℕ} {E : ℝ}
    (close : ∀ i<H, ‖z (i+1)-q*z i‖≤E) : ∀ i≤H, ‖z i-q^i*z 0‖≤(i:ℝ)*E := by
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
    intro bound
    have old:=ih (by omega)
    have eq : z (i+1)-q^(i+1)*z 0=(z (i+1)-q*z i)+q*(z i-q^i*z 0) := by rw [pow_succ];ring
    rw [eq]
    apply (norm_add_le _ _).trans
    rw [norm_mul,unit,one_mul];push_cast
    linarith only [close i (by omega),old]

theorem one_block (z : ℕ → ℂ) (q : ℂ) (unit : ‖q‖=1) (incoming : ‖z 0‖=1)
    {H : ℕ} {E D : ℝ} (en : 0≤E) (dp : 0<D) (away : D≤‖q-1‖)
    (close : ∀ i<H, ‖z (i+1)-q*z i‖≤E) :
    ‖∑ i ∈ range H,z i‖≤2/D+(H:ℝ)^2*E := by
  have nz:q≠1 := by rintro rfl;simp at away;linarith
  have geometric : (∑ i ∈ range H,q^i)*(q-1)=q^H-1 := geom_sum_mul q H
  have cone : ‖∑ i ∈ range H,q^i‖≤2/D := by
    apply (le_div_iff₀ dp).mpr
    apply (mul_le_mul_of_nonneg_left away (norm_nonneg _)).trans
    rw [←norm_mul,geometric]
    have h:=norm_sub_le (q^H) 1
    norm_num [norm_pow,unit] at h
    exact h
  have deviation : ‖∑ i ∈ range H,(z i-q^i*z 0)‖≤(H:ℝ)^2*E := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _ ∈ range H,(H:ℝ)*E := by
        apply sum_le_sum
        intro i hi
        have ii:=(mem_range.mp hi).le
        exact (local_trace z q unit close i ii).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast ii) en)
      _ = _ := by simp;ring
  have eq : (∑ i ∈ range H,z i)=(∑ i ∈ range H,q^i)*z 0+∑ i ∈ range H,(z i-q^i*z 0) := by
    rw [sum_sub_distrib,Finset.sum_mul];abel
  rw [eq]
  exact (norm_add_le _ _).trans (add_le_add (by simpa only [norm_mul,incoming,mul_one] using cone) deviation)

/-- Sum the individual block prices without assuming their incoming phases coincide. -/
theorem block_collection (z : ℕ → ℂ) (H B : ℕ) (bad : Finset ℕ) (live : bad⊆range B)
    {E : ℝ} (en : 0≤E) (unit : ∀ n, ‖z n‖≤1)
    (good : ∀ b<B, b∉bad → ‖∑ i ∈ range H,z (b*H+i)‖≤E) :
    ‖∑ i ∈ range (B*H),z i‖≤(bad.card:ℝ)*H+(B:ℝ)*E := by
  have partition (k : ℕ) : (∑ i ∈ range (k*H),z i)=∑ b ∈ range k,∑ i ∈ range H,z (b*H+i) := by
    induction k with
    | zero => simp
    | succ k ih => rw [Nat.succ_mul,sum_range_add,ih,sum_range_succ]
  have loose (b : ℕ) : ‖∑ i ∈ range H,z (b*H+i)‖≤(H:ℝ) := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _ ∈ range H,(1:ℝ) := sum_le_sum (fun i _ => unit _)
      _ = _ := by simp
  rw [partition]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ b ∈ range B,((if b∈bad then (H:ℝ) else 0)+E) := by
      apply sum_le_sum;intro b hb
      by_cases found : b∈bad
      · rw [if_pos found];linarith only [en,loose b]
      · rw [if_neg found,zero_add];exact good b (mem_range.mp hb) found
    _ = _ := by
      rw [sum_add_distrib,←sum_filter]
      have same : (range B).filter (fun b => b∈bad)=bad := by
        ext b;simp only [mem_filter];exact ⟨fun h => h.2,fun h => ⟨live h,h⟩⟩
      rw [same];simp


/-- A second local proof may keep every increment exact. This prices a change of
reciprocal weight without assuming that either the primes or their ratios are smooth. -/
theorem reciprocal_change {r s : ℂ} {D : ℝ} (dp : 0<D)
    (first : D≤‖r-1‖) (second : D≤‖s-1‖) :
    ‖(r-1)⁻¹-(s-1)⁻¹‖≤‖s-r‖/D^2 := by
  have rn : r-1≠0 := norm_pos_iff.mp (dp.trans_le first)
  have sn : s-1≠0 := norm_pos_iff.mp (dp.trans_le second)
  have eq : (r-1)⁻¹-(s-1)⁻¹=(s-r)/((r-1)*(s-1)) := by field_simp;ring
  rw [eq,norm_div,norm_mul]
  exact div_le_div_of_nonneg_left (norm_nonneg _) (sq_pos_of_pos dp)
    (by simpa only [pow_two] using mul_le_mul first second dp.le (norm_nonneg _))

#print axioms PALRH.BenfordBlocks.reciprocal_change

#print axioms PALRH.BenfordBlocks.local_trace
#print axioms PALRH.BenfordBlocks.one_block
#print axioms PALRH.BenfordBlocks.block_collection
end PALRH.BenfordBlocks
