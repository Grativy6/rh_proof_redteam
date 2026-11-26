import PALRH.PrimeCopies
import PALRH.SignedStrip
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas

open Finset
open scoped BigOperators
noncomputable section
namespace PALRH.GapClock
open PrimeCopies DoubledPrice QuarticBoards PrimeDivisorPrimitive

/-- A paid address eventually appears within each prescribed subpower search distance. -/
def subpowerHits : Prop :=
  ∀ q : ℕ, 0<q → ∃ K : ℕ, ∀ k : ℕ, K≤k →
    ∃ j : ℕ, k≤j ∧ (j-k)^q≤k ∧ pays 14 j

private theorem surround (hits : subpowerHits) {q : ℕ} (qp : 0<q) :
    ∃ K : ℕ, ∀ k : ℕ, K≤k → ∃ l r : ℕ,
      0<l ∧ l≤k ∧ k+1≤r ∧ (r-l)^q≤k ∧ pays 14 l ∧ pays 14 r := by
  obtain ⟨A, search⟩ := hits (2*q) (by omega)
  refine ⟨2*(A+1)+4^(2*q),?_⟩
  intro k late
  let m:=Nat.nthRoot (2*q) (k+1)
  have nz : 2*q≠0 := by omega
  have mp : 4≤m := (Nat.le_nthRoot_iff nz).mpr (by omega)
  have power : m^(2*q)≤k+1 := Nat.pow_nthRoot_le (Or.inl nz)
  have square : m^2≤m^(2*q) := Nat.pow_le_pow_right (by omega) (by omega)
  have size : 2*m+1<m^2 := by
    have h:=Nat.mul_le_mul_right m mp
    nlinarith only [h,mp]
  have half : 2*m+1<k+1 := size.trans_le (square.trans power)
  have lateA : 2*(A+1) ≤ k := (Nat.le_add_right _ _).trans late
  have prior : A<k-m := by omega
  obtain ⟨l,lo,lw,lp⟩:=search (k-m) prior.le
  obtain ⟨r,hi,rw,rp⟩:=search (k+1) (by omega)
  have dl : l-(k-m)≤m := (Nat.le_nthRoot_iff nz).mpr (lw.trans (by omega))
  have dr : r-(k+1)≤m := (Nat.le_nthRoot_iff nz).mpr rw
  have width : r-l ≤ 2*m+1 := by omega
  have charge:=(Nat.pow_le_pow_left width q).trans_lt (Nat.pow_lt_pow_left size qp.ne')
  rw [←pow_mul] at charge
  exact ⟨l,r,by omega,by omega,hi,by omega,lp,rp⟩

/-- The actual arithmetic at two paying quartics prices the entire intervening
area. The square of the missing index width is the only gap-dependent factor. -/
theorem intervening {k l r n : ℕ} (_kp : 0<k) (lp : 0<l) (left : l≤k) (right : k+1≤r)
    (near : r≤2*k) (lo : k^4≤n) (hi : n≤(k+1)^4)
    (leftPay : pays 14 l) (rightPay : pays 14 r) :
    error n ≤ 3456*(k:ℝ)^6*((r-l:ℕ):ℝ)^2 := by
  have lr : l<r := by omega
  have rp : 0<r := by omega
  have al := (Nat.pow_le_pow_left left 4).trans lo
  have ar := hi.trans (Nat.pow_le_pow_left right 4)
  have paidL:=area_of_fourteen lp leftPay
  have paidR:=area_of_fourteen rp rightPay
  have enlarged:=mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (Nat.cast_nonneg (α:=ℝ) l) (by exact_mod_cast lr.le : (l:ℝ)≤r) 6)
    (by norm_num : (0:ℝ)≤52)
  have chord:=upper_chord al ar (paidL.trans enlarged) paidR
  push_cast at chord
  let d:ℝ:=(r:ℝ)-l
  have dr : 1≤d := by
    dsimp [d];have e : (l:ℝ)+1≤r := by exact_mod_cast lr
    linarith only [e]
  have rr : 0≤(r:ℝ) := Nat.cast_nonneg _
  have ll : 0≤(l:ℝ) := Nat.cast_nonneg _
  have leR : (l:ℝ)≤r := by exact_mod_cast lr.le
  have g : (r:ℝ)^4-l^4 ≤ 4*d*r^3 := by
    have z:=mul_le_mul (show (r:ℝ)+l≤2*r by linarith)
      (show (r:ℝ)^2+l^2≤2*r^2 by nlinarith only [pow_le_pow_left₀ ll leR 2])
      (add_nonneg (sq_nonneg _) (sq_nonneg _)) (by positivity : 0≤2*(r:ℝ))
    have e:=mul_le_mul_of_nonneg_left z (zero_le_one.trans dr)
    dsimp [d] at e ⊢
    nlinarith only [e]
  have gapNon : 0≤(r:ℝ)^4-l^4 := sub_nonneg.mpr (pow_le_pow_left₀ ll leR 4)
  have square:=pow_le_pow_left₀ gapNon g 2
  have dd : 1≤d^2 := one_le_pow₀ dr
  have join:=mul_le_mul_of_nonneg_right dd (pow_nonneg rr 6)
  have rg : (r:ℝ)^6 ≤ (2*(k:ℝ))^6 :=
    pow_le_pow_left₀ rr (by exact_mod_cast near) 6
  have scale:=mul_le_mul_of_nonneg_right rg (sq_nonneg d)
  rw [Nat.cast_sub lr.le]
  change error n ≤ 3456*(k:ℝ)^6*d^2
  nlinarith only [chord,square,join,scale]

private theorem integer_powers (hits : subpowerHits) {b : ℝ} (bh : 1/2<b) :
    ∃ C : ℝ, 0≤C ∧ ∀ n : ℕ, 0<n → error n ≤ C*n*(n:ℝ)^b := by
  obtain ⟨i,threshold⟩:=exists_nat_one_div_lt (show 0<b-1/2 by linarith)
  let q:=i+1
  have qp : 0<q := Nat.succ_pos _
  have qr : 0<(q:ℝ) := by exact_mod_cast qp
  have delta : 6+2/(q:ℝ) ≤ 4*(1+b) := by
    have th : 1/(q:ℝ)<b-1/2 := by simpa [q] using threshold
    rw [show 2/(q:ℝ)=2*(1/q) by ring]
    linarith only [th,bh]
  obtain ⟨K,tests⟩:=surround hits qp
  let early:=∑ j ∈ range ((K+1)^4+1), |error j|
  have en : 0≤early := sum_nonneg (fun _ _ => abs_nonneg _)
  refine ⟨3456+early,by positivity,?_⟩
  intro n np
  obtain ⟨k,kp,lo,hi⟩:=root_interval np
  have kr : 1≤(k:ℝ) := by exact_mod_cast kp
  have nr : 1≤(n:ℝ) := by exact_mod_cast np
  have bp : 0≤b := by linarith only [bh]
  have nw:=Real.one_le_rpow nr bp
  by_cases late : K≤k
  · obtain ⟨l,r,lp,left,right,budget,ly,ry⟩:=tests k late
    have positive : 0<r-l := by omega
    have atleast : r-l≤(r-l)^q := Nat.le_self_pow qp.ne' _
    have near : r≤2*k := by omega
    have raw:=intervening kp lp left right near lo hi.le ly ry
    let g:ℝ:=((r-l:ℕ):ℝ)
    have gn : 0≤g := Nat.cast_nonneg _
    have cmp : g^2 ≤ (k:ℝ)^(2/(q:ℝ)) := by
      have h : g^q≤(k:ℝ) := by dsimp [g]; exact_mod_cast budget
      have e:=Real.rpow_le_rpow (pow_nonneg gn q) h (by positivity : (0:ℝ)≤2/q)
      rw [←Real.rpow_natCast_mul gn,show (q:ℝ)*(2/q)=2 by field_simp,
          Real.rpow_two] at e
      exact e
    have kN : ((k:ℝ)^4)≤n := by exact_mod_cast lo
    have exp : (k:ℝ)^6*g^2 ≤ (n:ℝ)*(n:ℝ)^b := calc
      _ ≤ (k:ℝ)^6*(k:ℝ)^(2/(q:ℝ)) := mul_le_mul_of_nonneg_left cmp (by positivity)
      _ = (k:ℝ)^(6+2/(q:ℝ)) := by rw [Real.rpow_add (zero_lt_one.trans_le kr)];norm_num
      _ ≤ (k:ℝ)^(4*(1+b)) := Real.rpow_le_rpow_of_exponent_le kr delta
      _ = ((k:ℝ)^4)^(1+b) := by rw [←Real.rpow_natCast_mul (Nat.cast_nonneg (α:=ℝ) k)];norm_num
      _ ≤ (n:ℝ)^(1+b) := Real.rpow_le_rpow (by positivity) kN (by positivity)
      _ = (n:ℝ)*(n:ℝ)^b := by rw [Real.rpow_add (zero_lt_one.trans_le nr),Real.rpow_one]
    change error n ≤ 3456*(k:ℝ)^6*g^2 at raw
    nlinarith only [raw,exp,mul_nonneg en (mul_nonneg (Nat.cast_nonneg (α:=ℝ) n) (zero_le_one.trans nw))]
  · have bound : n<(K+1)^4+1 := by
      have e:=Nat.pow_le_pow_left (show k+1≤K+1 by omega) 4
      omega
    have inside := single_le_sum (s:=range ((K+1)^4+1)) (f:=fun j => |error j|)
      (fun j _ => abs_nonneg (error j)) (mem_range.mpr bound)
    change |error n|≤early at inside
    have unit : 1≤(n:ℝ)*(n:ℝ)^b := one_le_mul_of_one_le_of_one_le nr nw
    have growth:=mul_le_mul_of_nonneg_left unit en
    nlinarith only [le_abs_self (error n),inside,growth,unit]

theorem rh_of_subpower_hits (hits : subpowerHits) : RiemannHypothesis := by
  apply PowerRecovery.rh_of_signed_value 1 (Or.inl rfl)
  intro b bh _
  obtain ⟨C,cn,heads⟩:=integer_powers hits bh
  have bp : 0≤b := by linarith only [bh]
  refine ⟨C*(2:ℝ)^b+1,by positivity,?_⟩
  intro t large
  let N:=⌊t⌋₊
  have np : 0<N := Nat.floor_pos.mpr large
  have before : (N:ℝ)≤t := Nat.floor_le (zero_le_one.trans large)
  have after : t<(N:ℝ)+1 := Nat.lt_floor_add_one _
  have hi := heads (N+1) (Nat.succ_pos _)
  have valueUpper : value (N+1:ℕ) ≤ C*((N+1:ℕ):ℝ)^b := by
    rw [SignedStrip.value_integer (Nat.succ_pos _)]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith only [hi]
  have monotone:=SignedStrip.signal_mono large after.le
  have one:=Real.one_le_rpow large bp
  have cap : ((N:ℝ)+1)^b ≤ (2:ℝ)^b*t^b := by
    rw [←Real.mul_rpow (by norm_num : (0:ℝ)≤2) (zero_le_one.trans large)]
    exact Real.rpow_le_rpow (by positivity) (by linarith only [before,large]) bp
  push_cast at valueUpper
  rw [one_mul]
  nlinarith only [valueUpper,monotone,before,one,mul_le_mul_of_nonneg_left cap cn]

#print axioms PALRH.GapClock.intervening
#print axioms PALRH.GapClock.rh_of_subpower_hits
end PALRH.GapClock
