import PALRH.SieveFrame

open Finset
open scoped BigOperators

namespace PALRH.HorizonPairs

/-- Just below the square-root cutoff, the only composite survivors are unordered prime pairs. -/
theorem sieve_classes {c m n : ℕ} (lo : 2≤m) (hi : m≤n) (cube : n<(c+1)^3) :
    m.Coprime c.factorial ↔
      (m.Prime ∧ c<m) ∨ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ c<p ∧ p≤q ∧ m=p*q := by
  constructor
  · intro clear
    have beyond:= (Nat.coprime_factorial_iff (by omega : m≠1)).mp clear
    by_cases prime : m.Prime
    · rw [prime.minFac_eq] at beyond
      exact Or.inl ⟨prime,beyond⟩
    right
    let p:=m.minFac
    let q:=m/p
    have pp : p.Prime:=Nat.minFac_prime (by omega)
    have div : p∣m := Nat.minFac_dvd m
    have back : p*q=m := Nat.mul_div_cancel' div
    have pq : p≤q := Nat.minFac_le_div (by omega) prime
    have qm : q∣m := ⟨p,by rw [←back,mul_comm]⟩
    have qp : q.Prime := by
      by_contra composite
      have qr : 0<q := pp.pos.trans_le pq
      have qr2:=Nat.minFac_sq_le_self qr composite
      have rprime:=Nat.minFac_prime (by have:=pp.two_le;omega : q≠1)
      have pr : p≤q.minFac := Nat.minFac_le_of_dvd rprime.two_le ((Nat.minFac_dvd q).trans qm)
      have pcut : c+1≤p := beyond
      have rcut : c+1≤q.minFac := pcut.trans pr
      have qcut : (c+1)^2≤q := (Nat.pow_le_pow_left rcut 2).trans qr2
      have impossible : (c+1)^3≤m := by
        rw [show (c+1)^3=(c+1)*(c+1)^2 by ring,←back]
        exact Nat.mul_le_mul pcut qcut
      omega
    exact ⟨p,q,pp,qp,beyond,pq,back.symm⟩
  · rintro (⟨pm,cm⟩ | ⟨p,q,pp,qp,cp,pq,rfl⟩)
    · exact pm.coprime_factorial_of_lt cm
    · exact (pp.coprime_factorial_of_lt cp).mul_left (qp.coprime_factorial_of_lt (cp.trans_le pq))

/-- Factoring one external product recovers the two internal primes in a fixed order. -/
theorem one_unordered_pair {p q r s : ℕ} (pp : p.Prime) (_qp : q.Prime)
    (rp : r.Prime) (sp : s.Prime) (pq : p≤q) (rs : r≤s) (same : p*q=r*s) : p=r ∧ q=s := by
  have dst : p∣r*s := same ▸ (dvd_mul_right p q)
  rcases pp.dvd_mul.mp dst with d|d
  · have eq:= (Nat.prime_dvd_prime_iff_eq pp rp).mp d
    subst r
    exact ⟨rfl,Nat.eq_of_mul_eq_mul_left pp.pos same⟩
  · have eq:= (Nat.prime_dvd_prime_iff_eq pp sp).mp d
    subst s
    rw [Nat.mul_comm r p] at same
    have qr:=Nat.eq_of_mul_eq_mul_left pp.pos same
    omega

/-- After shifting the lower corner to zero, diagonal j has j+1 sites and t-j levels. -/
def triangle (t : ℕ) := ∑ j ∈ range t,(j+1)*(t-j)

private theorem layer_size (t : ℕ) :
    2*(∑ j ∈ range t, (j+1))=t*(t+1) := by
  induction t with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ]
    nlinarith only [ih]

private theorem added_layer (t : ℕ) :
    triangle (t+1)=triangle t+(∑ j ∈ range t, (j+1))+(t+1) := by
  unfold triangle
  rw [sum_range_succ]
  simp only [Nat.add_sub_cancel_left,mul_one]
  congr 1
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have := mem_range.mp hj
  rw [show t+1-j=(t-j)+1 by omega]
  ring

theorem triangle_volume (t : ℕ) : 6*triangle t=t*(t+1)*(t+2) := by
  induction t with
  | zero => simp [triangle]
  | succ k ih =>
    rw [added_layer]
    nlinarith only [ih,layer_size k]

/-- The centered product cut has a curved correction given by the product of the two offsets. -/
theorem product_offset (x u v : ℝ) :
    x^2-(x+u)*(x+v)= -x*(u+v)-u*v := by ring

#print axioms PALRH.HorizonPairs.sieve_classes
#print axioms PALRH.HorizonPairs.one_unordered_pair
#print axioms PALRH.HorizonPairs.triangle_volume
end PALRH.HorizonPairs
