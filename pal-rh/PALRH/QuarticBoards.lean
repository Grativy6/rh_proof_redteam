import PALRH.PrimeBoard

open Finset
open scoped BigOperators Classical

noncomputable section
namespace PALRH.QuarticBoards
open LinearPrimeIntegral PrimeBoard

private def extended (B : ℕ) (x : ℝ) :=
  ∑ k ∈ Icc 1 B, ArithmeticFunction.vonMangoldt k * max 0 (x-k)

private theorem extended_integer {n B : ℕ} (hn : n≤B) : extended B n=fullWalk n := by
  calc
    extended B n = ∑ k ∈ Icc 1 n, ArithmeticFunction.vonMangoldt k * max 0 ((n:ℝ)-k) := by
      unfold extended
      symm
      apply Finset.sum_subset (fun k hk => mem_Icc.mpr ⟨(mem_Icc.mp hk).1,(mem_Icc.mp hk).2.trans hn⟩)
      intro k hk out
      have beyond : n<k := by
        by_contra! h
        exact out (mem_Icc.mpr ⟨(mem_Icc.mp hk).1,h⟩)
      rw [max_eq_left (sub_nonpos.mpr (by exact_mod_cast beyond.le)),mul_zero]
    _ = _ := by
      unfold fullWalk
      apply Finset.sum_congr rfl
      intro k hk
      rw [max_eq_right (sub_nonneg.mpr (by exact_mod_cast (mem_Icc.mp hk).2)),mul_comm]

private theorem hinge {a v b k : ℝ} (lo : a≤v) (hi : v≤b) :
    (b-a)*max 0 (v-k)≤(b-v)*max 0 (a-k)+(v-a)*max 0 (b-k) := by
  by_cases s : v-k≤0
  · rw [max_eq_left s,mul_zero]
    exact add_nonneg (mul_nonneg (by linarith) (le_max_left _ _))
      (mul_nonneg (by linarith) (le_max_left _ _))
  · rw [max_eq_right (le_of_not_ge s)]
    calc
      _ = (b-v)*(a-k)+(v-a)*(b-k) := by ring
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (le_max_right _ _) (by linarith))
        (mul_le_mul_of_nonneg_left (le_max_right _ _) (by linarith))

def error (n : ℕ) := fullWalk n-(n:ℝ)^2/2

private theorem chord {a n b : ℕ} (lo : a≤n) (hi : n≤b) :
    ((b:ℝ)-a)*error n ≤ ((b:ℝ)-n)*error a + ((n:ℝ)-a)*error b +
      ((b:ℝ)-a)*((n:ℝ)-a)*((b:ℝ)-n)/2 := by
  have full : ((b:ℝ)-a)*fullWalk n≤((b:ℝ)-n)*fullWalk a+((n:ℝ)-a)*fullWalk b := by
    rw [←extended_integer hi,←extended_integer (lo.trans hi),←extended_integer (n:=b) le_rfl]
    unfold extended
    rw [Finset.mul_sum,Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro k _
    have h:=hinge (k:=(k:ℝ)) (by exact_mod_cast lo : (a:ℝ)≤n) (by exact_mod_cast hi : (n:ℝ)≤b)
    have weight:=mul_le_mul_of_nonneg_left h (ArithmeticFunction.vonMangoldt_nonneg (n:=k))
    nlinarith only [weight]
  unfold error
  nlinarith only [full]

/-- Three adjacent readings bound every intermediate one for a positive prime-power area. -/
private theorem between {l a n b : ℕ} {T W : ℝ}
    (la : l<a) (an : a≤n) (nb : n≤b) (ab : a<b)
    (tn : 0≤T) (span : (b:ℝ)-l≤W) (ratio : (b:ℝ)-a≤15*((a:ℝ)-l))
    (ea : |error a|≤T) (el : |error l|≤T) (eb : |error b|≤T) :
    |error n|≤31*T+W^2 := by
  have lr : (l:ℝ)<a := by exact_mod_cast la
  have ar : (a:ℝ)≤n := by exact_mod_cast an
  have nr : (n:ℝ)≤b := by exact_mod_cast nb
  have br : (a:ℝ)<b := by exact_mod_cast ab
  have product_bound (x y : ℝ) (xn : 0≤x) (yn : 0≤y) (xw : x≤W) (yw : y≤W) :
      x*y/2≤W^2 := by
    have v:=mul_le_mul xw yw yn (xn.trans xw)
    nlinarith only [v,sq_nonneg W]
  have upper := chord an nb
  have lower := chord la.le an
  have hu := product_bound ((n:ℝ)-a) ((b:ℝ)-n) (by linarith) (by linarith) (by linarith) (by linarith)
  have hd' := product_bound ((n:ℝ)-l) ((n:ℝ)-a) (by linarith) (by linarith) (by linarith) (by linarith)
  rw [abs_le] at el ea eb ⊢
  constructor
  · apply le_of_mul_le_mul_left (a:=((a:ℝ)-l)) _ (by linarith : 0<(a:ℝ)-l)
    nlinarith only [lower,
      mul_le_mul_of_nonneg_left ea.1 (by linarith : 0≤(n:ℝ)-l),
      mul_le_mul_of_nonneg_left el.2 (by linarith : 0≤(n:ℝ)-a),
      mul_le_mul_of_nonneg_left hd' (by linarith : 0≤(a:ℝ)-l),
      mul_le_mul_of_nonneg_right (by linarith : (n:ℝ)-a≤15*((a:ℝ)-l)) tn]
  · apply le_of_mul_le_mul_left (a:=((b:ℝ)-a)) _ (by linarith : 0<(b:ℝ)-a)
    nlinarith only [upper,
      mul_le_mul_of_nonneg_left ea.2 (by linarith : 0≤(b:ℝ)-n),
      mul_le_mul_of_nonneg_left eb.2 (by linarith : 0≤(n:ℝ)-a),
      mul_le_mul_of_nonneg_left hu (by linarith : 0≤(b:ℝ)-a),
      mul_nonneg (by linarith : 0≤(b:ℝ)-a) tn]

private theorem quartic_bracket (n : ℕ) (np : 0<n) :
    ∃ j : ℕ, (j+1)^4≤n ∧ n<(j+2)^4 := by
  let r:=n.sqrt
  let k:=r.sqrt
  have kp : 0<k := Nat.sqrt_pos.mpr (Nat.sqrt_pos.mpr np)
  have low : k^4≤n := calc
    k^4 = (k*k)*(k*k) := by ring
    _ ≤ r*r := Nat.mul_le_mul (Nat.sqrt_le r) (Nat.sqrt_le r)
    _ ≤ n := Nat.sqrt_le n
  have high : n<(k+1)^4 := calc
    n < (r+1)*(r+1) := Nat.lt_succ_sqrt n
    _ ≤ ((k+1)*(k+1))*((k+1)*(k+1)) :=
      Nat.mul_le_mul (Nat.lt_succ_sqrt r) (Nat.lt_succ_sqrt r)
    _ = (k+1)^4 := by ring
  obtain ⟨j,h⟩:=Nat.exists_eq_succ_of_ne_zero kp.ne'
  exact ⟨j,by simpa [h] using low,by simpa [h,Nat.add_assoc] using high⟩

/-- Values at fourth powers bound the whole prime-power area by convex interpolation. -/
theorem quartic_envelope {C : ℝ} (cn : 0≤C)
    (knots : ∀ k : ℕ, |error (k^4)|≤C*(k:ℝ)^6)
    {n : ℕ} (np : 0<n) :
    |error n|≤(1984*C+256)*n*Real.sqrt n := by
  obtain ⟨j,left,right⟩:=quartic_bracket n np
  let t : ℝ := j
  have tn : 0≤t := Nat.cast_nonneg _
  have anchor (k : ℕ) (kr : k≤j+2) : |error (k^4)|≤64*C*(t+1)^6 := by
    have lift : (k:ℝ)≤2*(t+1) := by
      have z : (k:ℝ)≤(j:ℝ)+2 := by exact_mod_cast kr
      dsimp [t] at *
      linarith only [z,tn]
    have h:=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg k) lift 6) cn
    calc
      _ ≤ _ := knots k
      _ ≤ _ := h
      _ = _ := by ring
  have t2 : 0≤t^2 := by positivity
  have t3 : 0≤t^3 := by positivity
  have span : (((j+2)^4:ℕ):ℝ)-((j^4:ℕ):ℝ)≤16*(t+1)^3 := by
    push_cast
    change (t+2)^4-t^4≤16*(t+1)^3
    nlinarith only [tn,t2,t3]
  have ratio : (((j+2)^4:ℕ):ℝ)-(((j+1)^4:ℕ):ℝ)≤15*((((j+1)^4:ℕ):ℝ)-((j^4:ℕ):ℝ)) := by
    push_cast
    change (t+2)^4-(t+1)^4≤15*((t+1)^4-t^4)
    nlinarith only [tn,t2,t3]
  have top : (j+1)^4<(j+2)^4 := Nat.pow_lt_pow_left (by omega) (by decide)
  have prior : j^4<(j+1)^4 := Nat.pow_lt_pow_left (by omega) (by decide)
  have all:=between prior left right.le top (show 0≤64*C*(t+1)^6 by positivity) span ratio
    (anchor (j+1) (by omega)) (anchor j (by omega)) (anchor (j+2) le_rfl)
  have xl : (t+1)^4≤(n:ℝ) := by dsimp [t];exact_mod_cast left
  have rr : (t+1)^2≤Real.sqrt n := (Real.le_sqrt (by positivity) (Nat.cast_nonneg _)).mpr
    (by convert xl using 1; ring)
  have root := mul_le_mul xl rr (by positivity : 0≤(t+1)^2) (Nat.cast_nonneg n)
  have power : (t+1)^6≤(n:ℝ)*Real.sqrt n := by
    calc
      _ = (t+1)^4*(t+1)^2 := by ring
      _ ≤ _ := root
  calc
    _ ≤ _ := all
    _ = (1984*C+256)*(t+1)^6 := by ring
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left power (by positivity)

/-- Natural-number comparisons are needed only at n=k^4. -/
theorem rh_of_quartic_boards
    (funded : ∀ k : ℕ, 0<k → demand (k^4)≤capacity (k^4) ∧
      capacity (k^4)≤demand (k^4)*allowance (k^4)) : RiemannHypothesis := by
  obtain ⟨C,cn,price⟩:=full_walk_price
  apply rh_of_full_walk (C:=1984*C+256) (by positivity)
  intro n np
  apply quartic_envelope cn _ np
  intro k
  by_cases kz : k=0
  · subst k;simp [error,fullWalk]
  have kp:=Nat.pos_of_ne_zero kz
  have value:=price (k^4) (pow_pos kp _) (funded k kp)
  have root : Real.sqrt ((k:ℝ)^4)=(k:ℝ)^2 := by
    rw [show (k:ℝ)^4=((k:ℝ)^2)^2 by ring,Real.sqrt_sq (by positivity)]
  unfold error
  push_cast at value ⊢
  rw [root] at value
  calc
    _ ≤ _ := value
    _ = _ := by ring

theorem rh_of_quartic_pairs
    (funded : ∀ k : ℕ, 0<k →
      (k^4).factorial^(k^4)*pairWhole (k^4)≤capacity (k^4)*pairLeft (k^4) ∧
      capacity (k^4)≤demand (k^4)*allowance (k^4)) : RiemannHypothesis :=
  rh_of_quartic_boards (fun k kp => ⟨pair_return (k^4) (pow_pos kp _) (funded k kp).1,
    (funded k kp).2⟩)

#print axioms PALRH.QuarticBoards.quartic_envelope
#print axioms PALRH.QuarticBoards.rh_of_quartic_boards
#print axioms PALRH.QuarticBoards.rh_of_quartic_pairs
end PALRH.QuarticBoards
