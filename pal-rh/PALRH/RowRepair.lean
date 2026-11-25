import PALRH.Sieve
import Mathlib.Data.Nat.Totient

open Finset
open scoped BigOperators
noncomputable section
namespace PALRH.RowRepair
open OneTick

/-- Allowed calendar moduli from 2 up to a finite height. -/
def frame (B : ℕ) : Finset ℕ := Finset.Icc 2 B

def signal (B : ℕ) (x : ℕ → ℚ) : ℕ → ℚ :=
  ∑ d ∈ frame B, ((d:ℚ)*x d) • turn d

def column (B : ℕ) (x : ℕ → ℚ) (e : ℕ) : ℚ :=
  ∑ d ∈ frame B, if e ∣ d then x d else 0

def edgeEnergy (L : ℕ) (f : ℕ → ℚ) : ℚ :=
  (∑ t ∈ Finset.range L, (f (t+1)-f t)^2)/(L:ℚ)

def sieveSum (B : ℕ) : ℚ := ∑ e ∈ frame B, (ArithmeticFunction.moebius e:ℚ)^2 / e.totient

theorem signal_mem (B : ℕ) (x : ℕ → ℚ) : signal B x ∈ fits := by
  apply Submodule.sum_mem
  intro d hd
  exact fits.smul_mem _ (turn_mem (Finset.mem_Icc.mp hd).1)

theorem signal_one (B : ℕ) (x : ℕ → ℚ) : signal B x 1 = ∑ d ∈ frame B, x d := by
  simp only [signal, Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro d hd
  have h := (Finset.mem_Icc.mp hd).1
  simp [turn,Nat.mod_eq_of_lt (by omega : 1<d)]
  field_simp

/-- A unit change at the physical row m preserves all rows strictly below m. -/
theorem repair_pivot {m : ℕ} (hm : 2≤m) {f : ℕ → ℚ} (hf : f∈fits) (one : f 1=1) :
    contrast m 1 f ∈ fits ∧ (∀ k<m, contrast m 1 f k=0) ∧ contrast m 1 f m=1 := by
  refine ⟨contrast_mem hm 1 hf,?_,?_⟩
  · intro k hk
    simp [contrast,dilate,Nat.div_eq_of_lt hk,Nat.div_eq_of_lt (by omega : k<m+1)]
  · simp [contrast,dilate,Nat.div_self (by omega : 0<m),Nat.div_eq_of_lt (by omega : m<m+1),one,(fit_properties hf).1]

private lemma drop_one {n B : ℕ} (hn : 0<n) (inside : n≤B) (v : ℕ → ℚ) :
    (∑ e ∈ frame B, if e ∣ n then v e else 0) = (∑ e ∈ n.divisors, v e)-v 1 := by
  have setEq : (frame B).filter (fun e => e ∣ n) = n.divisors.erase 1 := by
    ext e
    simp only [Finset.mem_filter,frame,Finset.mem_Icc,Finset.mem_erase,Nat.mem_divisors]
    constructor
    · rintro ⟨⟨he,_⟩,hd⟩
      exact ⟨by omega,hd,hn.ne'⟩
    · rintro ⟨ho,hd,_⟩
      have hp := Nat.pos_of_dvd_of_pos hd hn
      exact ⟨⟨by omega,(Nat.le_of_dvd hn hd).trans inside⟩,hd⟩
  rw [← Finset.sum_filter,setEq]
  have h := Finset.sum_erase_add n.divisors v (Nat.one_mem_divisors.mpr hn.ne')
  linarith

private lemma phi_pair {a b B : ℕ} (ha : a ∈ frame B) (_hb : b ∈ frame B) :
    (∑ e ∈ frame B, if e ∣ a ∧ e ∣ b then (e.totient:ℚ) else 0) =
      (a.gcd b:ℕ)- (1:ℚ) := by
  have ha' := Finset.mem_Icc.mp ha
  have hg := Nat.gcd_pos_of_pos_left b (show 0<a by omega)
  simp only [←Nat.dvd_gcd_iff]
  rw [drop_one hg ((Nat.gcd_le_left _ (by omega)).trans ha'.2)]
  simp only [←Nat.cast_sum,Nat.sum_totient,Nat.totient_one,Nat.cast_one]

private lemma mu_balance {B : ℕ} (x : ℕ → ℚ) :
    (∑ e ∈ frame B, (ArithmeticFunction.moebius e:ℚ)*column B x e) = -(∑ d ∈ frame B, x d) := by
  unfold column
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm, ←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  have hd' := Finset.mem_Icc.mp hd
  have hsum := DFunLike.congr_fun ArithmeticFunction.moebius_mul_coe_zeta d
  rw [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply,if_neg (by omega : d≠1)] at hsum
  have hz : (∑ e ∈ d.divisors, (ArithmeticFunction.moebius e:ℚ))=0 := by exact_mod_cast hsum
  have val := drop_one (by omega : 0<d) hd'.2 (fun e => (ArithmeticFunction.moebius e:ℚ))
  rw [hz] at val
  simp only [ArithmeticFunction.moebius_apply_one,Int.cast_one,zero_sub] at val
  calc
    _ = (∑ e ∈ frame B, if e ∣ d then (ArithmeticFunction.moebius e:ℚ) else 0)*x d := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro e _
      by_cases h : e ∣ d <;> simp [h]
    _ = -x d := by rw [val]; ring

private lemma gram_entry {a b L : ℕ} (ha : 0<a) (hb : 0<b) (pa : a ∣ L) (pb : b ∣ L)
    (x y : ℚ) :
    (∑ t ∈ Finset.range L, ((a:ℚ)*x*(turn a (t+1)-turn a t))*
        ((b:ℚ)*y*(turn b (t+1)-turn b t))) =
      (L:ℚ)*x*y*((a.gcd b:ℕ)-(1:ℚ)) := by
  have lc : 0<a.lcm b := Nat.lcm_pos ha hb
  have g : (a.gcd b:ℚ)*(a.lcm b:ℕ)=(a:ℚ)*b := by exact_mod_cast Nat.gcd_mul_lcm a b
  calc
    _ = ((a:ℚ)*b*x*y)*(∑ t ∈ Finset.range L, (turn a (t+1)-turn a t)*(turn b (t+1)-turn b t)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      ring
    _ = _ := by
      rw [edge_gram_period ha hb pa pb]
      field_simp
      linear_combination -(L:ℚ)*x*y*g

/-- Over a common period, complete the gcd Gram form into positive independent divisor coordinates. -/
theorem edge_diagonal (B : ℕ) {L : ℕ} (hL : 0<L) (cover : ∀ d ∈ frame B, d ∣ L) (x : ℕ → ℚ) :
    edgeEnergy L (signal B x) = ∑ e ∈ frame B, (e.totient:ℚ)*(column B x e)^2 := by
  let step := fun d t : ℕ => (d:ℚ)*x d*(turn d (t+1)-turn d t)
  have inc (t : ℕ) : signal B x (t+1) - signal B x t = ∑ d ∈ frame B, step d t := by
    simp only [signal, Finset.sum_apply,Pi.smul_apply,smul_eq_mul,←Finset.sum_sub_distrib,step,mul_sub]
  have eq (e a b : ℕ) : (e.totient:ℚ)*
      ((if e ∣ a then x a else 0)*(if e ∣ b then x b else 0)) =
      x a*x b*(if e ∣ a ∧ e ∣ b then (e.totient:ℚ) else 0) := by
    by_cases h : e ∣ a <;> by_cases k : e ∣ b <;> simp [h,k]
    ring
  unfold edgeEnergy
  apply (div_eq_iff (by positivity : (L:ℚ)≠0)).mpr
  simp_rw [inc, sq,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ a ∈ frame B, ∑ b ∈ frame B, (L:ℚ)*x a*x b*((a.gcd b:ℕ)-(1:ℚ)) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b hb
      exact gram_entry (by have := (Finset.mem_Icc.mp ha).1; omega)
        (by have := (Finset.mem_Icc.mp hb).1; omega) (cover a ha) (cover b hb) _ _
    _ = (∑ e ∈ frame B, (e.totient:ℚ)*(column B x e * column B x e))*(L:ℚ) := by
      simp only [column,Finset.sum_mul,Finset.mul_sum,eq]
      conv_rhs => rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      conv_rhs => rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b hb
      rw [←Finset.sum_mul, ←Finset.mul_sum, phi_pair hb ha, Nat.gcd_comm b a]
      ring
    _ = _ := Finset.sum_mul _ _ _


private def optimal (B e : ℕ) : ℚ :=
  -(ArithmeticFunction.moebius e:ℚ) / ((e.totient:ℚ)*sieveSum B)

private lemma sieveSum_pos {B : ℕ} (hB : 2≤B) : 0<sieveSum B := by
  have h2 : 2 ∈ frame B := Finset.mem_Icc.mpr ⟨le_rfl,hB⟩
  apply Finset.sum_pos' (fun i _ => by positivity) ⟨2,h2,?_⟩
  norm_num [ArithmeticFunction.moebius_apply_prime Nat.prime_two,Nat.totient_prime Nat.prime_two]

private theorem optimal_normal {B : ℕ} (hB : 2≤B) :
    (∑ e ∈ frame B, (ArithmeticFunction.moebius e:ℚ)*optimal B e) = -1 := by
  have hG := sieveSum_pos hB
  have term (e : ℕ) (he : e ∈ frame B) :
      (ArithmeticFunction.moebius e:ℚ)*optimal B e =
      (-1/sieveSum B)*((ArithmeticFunction.moebius e:ℚ)^2/e.totient) := by
    unfold optimal
    ring
  rw [Finset.sum_congr rfl term,← Finset.mul_sum]
  change (-1/sieveSum B) * sieveSum B = -1
  field_simp

private lemma represent_columns (B : ℕ) (target : ℕ → ℚ) :
    ∃ x : ℕ → ℚ, ∀ e ∈ frame B, column B x e=target e := by
  induction B generalizing target with
  | zero => exact ⟨0,fun e he => by have := (Finset.mem_Icc.mp he); omega⟩
  | succ B ih =>
    by_cases big : 2≤B+1
    · let k := B+1
      let old := fun e : ℕ => target e - (if e ∣ k then target k else 0)
      obtain ⟨x,hx⟩ := ih old
      let y := Function.update x k (target k)
      have sets : frame (B+1)=insert k (frame B) := by
        ext e
        simp only [frame,Finset.mem_Icc,Finset.mem_insert,k]
        omega
      have out : k∉frame B := by simp [k,frame]
      have base (e : ℕ) : (∑ d ∈ frame B, if e ∣ d then y d else 0)=column B x e := by
        apply Finset.sum_congr rfl
        intro d hd
        simp [y,Function.update_of_ne (show d≠k by intro eq; exact out (eq ▸ hd))]
      have atrow (e : ℕ) : column (B+1) y e=(if e ∣ k then target k else 0)+column B x e := by
        unfold column
        rw [sets,Finset.sum_insert out,base]
        simp [y,column]
      refine ⟨y,fun e he => ?_⟩
      rw [sets,Finset.mem_insert] at he
      rcases he with rfl|he
      · rw [atrow]
        have z : column B x k=0 := by
          apply Finset.sum_eq_zero
          intro d hd
          have dh := Finset.mem_Icc.mp hd
          have no : ¬k ∣ d := by intro dvd; have := Nat.le_of_dvd (by omega : 0<d) dvd; dsimp [k] at this; omega
          simp [no]
        simp [z]
      · rw [atrow,hx e he]
        dsimp [old]
        ring
    · exact ⟨0, fun e he => by have := Finset.mem_Icc.mp he; omega⟩

/-- The exact excess over the optimal leading squared cost is a sum of squares. -/
theorem edge_excess {B L : ℕ} (hB : 2≤B) (hL : 0<L) (cover : ∀ d ∈ frame B, d ∣ L)
    (x : ℕ → ℚ) (unit : signal B x 1=1) :
    edgeEnergy L (signal B x) = 1/sieveSum B +
      ∑ e ∈ frame B, (e.totient:ℚ)*(column B x e-optimal B e)^2 := by
  have G := sieveSum_pos hB
  have norm := mu_balance (B:=B) x
  rw [←signal_one B x,unit] at norm
  have term (e : ℕ) (he : e ∈ frame B) :
      (e.totient:ℚ)*(column B x e-optimal B e)^2 =
      (e.totient:ℚ)*(column B x e)^2 +
        (2/sieveSum B)*((ArithmeticFunction.moebius e:ℚ)*column B x e) +
        (1/(sieveSum B)^2)*((ArithmeticFunction.moebius e:ℚ)^2/e.totient) := by
    have hepos : 0<e := by have := (Finset.mem_Icc.mp he).1; omega
    have hp := Nat.totient_pos.mpr hepos
    unfold optimal
    field_simp
    ring
  rw [edge_diagonal B hL cover,Finset.sum_congr rfl term,Finset.sum_add_distrib,Finset.sum_add_distrib,
    ←Finset.mul_sum,←Finset.mul_sum,norm]
  change _ = 1/sieveSum B + (_+(2/sieveSum B)*(-1)+(1/(sieveSum B)^2)*sieveSum B)
  field_simp
  ring

/-- The best mean squared edge cost among every normalized parent up to height B.
Both the lower bound and its finite rational attaining parent are included. -/
theorem least_edge_cost {B L : ℕ} (hB : 2≤B) (hL : 0<L) (cover : ∀ d ∈ frame B, d ∣ L) :
    (∀ x : ℕ → ℚ, signal B x 1=1 → 1/sieveSum B ≤ edgeEnergy L (signal B x)) ∧
    ∃ x : ℕ → ℚ, signal B x 1=1 ∧ edgeEnergy L (signal B x)=1/sieveSum B := by
  constructor
  · intro x unit
    rw [edge_excess hB hL cover x unit]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun e _ => by positivity))
  · obtain ⟨x,hx⟩ := represent_columns B (optimal B)
    have normal := mu_balance (B:=B) x
    have sub : (∑ e ∈ frame B, (ArithmeticFunction.moebius e:ℚ)*column B x e) =
        ∑ e ∈ frame B, (ArithmeticFunction.moebius e:ℚ)*optimal B e := by
      apply Finset.sum_congr rfl
      intro e he
      rw [hx e he]
    rw [sub,optimal_normal hB] at normal
    have unit : signal B x 1=1 := by rw [signal_one]; linarith
    refine ⟨x,unit,?_⟩
    rw [edge_excess hB hL cover x unit]
    have eq : (∑ e ∈ frame B, (e.totient:ℚ)*(column B x e-optimal B e)^2)=0 := by
      apply Finset.sum_eq_zero
      intro e he
      simp [hx e he]
    rw [eq,add_zero]

#print axioms PALRH.RowRepair.least_edge_cost
#print axioms PALRH.RowRepair.repair_pivot

end PALRH.RowRepair
