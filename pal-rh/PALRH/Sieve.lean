import PALRH.CloseClocks
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

open Finset Filter
open scoped Topology BigOperators
noncomputable section
namespace PALRH.OneTick

/-- A concrete first-tick comparator: numbers surviving division by every prime up to B. -/
def sieveMask (B k : ℕ) : ℚ := if k.Coprime B.factorial then 1 else 0

theorem sieve_on_prefix {k B : ℕ} (hk : 0 < k) (inFrame : k ≤ B) :
    sieveMask B k = tick k := by
  unfold sieveMask tick
  simp only [Nat.coprime_iff_gcd_eq_one, Nat.gcd_eq_left (Nat.dvd_factorial hk inFrame)]

theorem sieve_loss (B : ℕ) : loss tick (sieveMask B) ≤ 1/((B:ℝ)+1) := by
  let f : ℕ → ℝ := fun n => rowWeight n * ((tick (n+1) - sieveMask B (n+1) : ℚ):ℝ)^2
  have hb (n : ℕ) : ((tick (n+1) - sieveMask B (n+1) : ℚ):ℝ)^2 ≤ 1 := by
    unfold tick sieveMask
    split_ifs <;> norm_num
  have hle (n : ℕ) : f n ≤ rowWeight n :=
    mul_le_of_le_one_right (by unfold rowWeight; positivity) (hb n)
  have hnonneg (n : ℕ) : 0 ≤ f n := mul_nonneg (by unfold rowWeight; positivity) (sq_nonneg _)
  have hs : Summable f := Summable.of_nonneg_of_le hnonneg hle rowWeight_hasSum.summable
  have hz : ∑ n ∈ Finset.range B, f n = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    have h := sieve_on_prefix (by omega : 0 < n+1) (Nat.succ_le_of_lt (Finset.mem_range.mp hn))
    simp [f,h]
  change (∑' n, f n) ≤ _
  rw [← hs.sum_add_tsum_nat_add B, hz, zero_add, ← rowWeight_tail B]
  exact ((summable_nat_add_iff B).mpr hs).tsum_le_tsum (fun n => hle _)
    ((summable_nat_add_iff B).mpr rowWeight_hasSum.summable)

/-- The exact sieve cannot be supplied by a finite legal fit once both 2 and 3 enter. -/
theorem sieve_not_finite {B : ℕ} (hB : 3 ≤ B) : sieveMask B ∉ fits := by
  intro hf
  obtain ⟨N,c,hc⟩ := as_array hf
  let T := (N+1).factorial * B.factorial
  let L := 6*T
  have ht : 0 < T := Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
  have hL : 6 ≤ L := by dsimp [L]; omega
  have divB : B.factorial ∣ L := (dvd_mul_left _ _).trans (dvd_mul_left T 6)
  have cover (i : Fin N) : i.val + 2 ∣ L := by
    have h : i.val+2 ∣ (N+1).factorial := Nat.dvd_factorial (by omega) (by omega)
    exact h.trans ((dvd_mul_right _ _).trans (dvd_mul_left T 6))
  have hprev : (L-1).Coprime L := by
    have hh : (L-1).Coprime ((L-1)+1) := by simp
    simpa only [Nat.sub_add_cancel (show 1 ≤ L by omega)] using hh
  have hlast : sieveMask B (L-1)=1 := by simp [sieveMask,Nat.Coprime.of_dvd_right divB hprev]
  have hlow : sieveMask B 2=0 := by rw [sieve_on_prefix (by decide) (by omega)]; norm_num [tick]
  have triple : 3 ∣ L-3 := Nat.dvd_sub (by exact dvd_trans (by decide : 3 ∣ 6) (dvd_mul_right 6 T)) (dvd_refl _)
  have hac : ¬(L-3).Coprime B.factorial := by
    intro h
    have hd := Nat.dvd_gcd triple (Nat.dvd_factorial (by decide : 0<3) hB)
    rw [h.gcd_eq_one] at hd
    norm_num at hd
  have hnear : sieveMask B (L-3)=0 := by simp [sieveMask,hac]
  have h := second_row_trace c (L := L) (by omega) cover
  linarith [hc 2, hc (L-1), hc (L-3)]

private theorem mu_divisor_sum (n : ℕ) :
    (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℚ)) = if n=1 then 1 else 0 := by
  have h := DFunLike.congr_fun ArithmeticFunction.moebius_mul_coe_zeta n
  rw [ArithmeticFunction.coe_mul_zeta_apply,ArithmeticFunction.one_apply] at h
  by_cases eq : n=1 <;> simp only [eq,if_true,if_false] at h ⊢ <;> exact_mod_cast h

private theorem common_divisor_sum {Q : ℕ} (hQ0 : 0<Q) (k : ℕ) :
    (∑ d ∈ Q.divisors, if d ∣ k then (ArithmeticFunction.moebius d : ℚ) else 0) =
      if k.Coprime Q then 1 else 0 := by
  have hf : Q.divisors.filter (fun d => d ∣ k) = (k.gcd Q).divisors := by
    ext d
    have hgpos : 0 < k.gcd Q := Nat.gcd_comm k Q ▸ Nat.gcd_pos_of_pos_left k hQ0
    simp only [Finset.mem_filter,Nat.mem_divisors,Nat.dvd_gcd_iff]
    exact ⟨fun h => ⟨⟨h.2,h.1.1⟩,hgpos.ne'⟩,fun h => ⟨⟨h.1.2,hQ0.ne'⟩,h.1.1⟩⟩
  rw [← Finset.sum_filter,hf,mu_divisor_sum]

/-- Forward signed sieve signal in the exact finite residue span. -/
def mobiusSignal (Q k : ℕ) : ℚ := ∑ d ∈ Q.divisors, (ArithmeticFunction.moebius d:ℚ)*turn d k

/-- Same origin and the opposite orientation in each component's own frame. -/
def reversedSignal (Q k : ℕ) : ℚ :=
  ∑ d ∈ Q.divisors, (ArithmeticFunction.moebius d:ℚ)*turn d (d-k%d)

theorem mobiusSignal_mem (Q : ℕ) : mobiusSignal Q ∈ fits := by
  have he : mobiusSignal Q = ∑ d ∈ Q.divisors, (ArithmeticFunction.moebius d:ℚ) • turn d := by
    funext k
    simp [mobiusSignal, Finset.sum_apply]
  rw [he]
  apply Submodule.sum_mem
  intro d hd
  by_cases h : d=1
  · subst d
    have hzero : turn 1 = 0 := by funext k; simp [turn, Nat.mod_one]
    simp [hzero]
  · have hpos := Nat.pos_of_mem_divisors hd
    exact fits.smul_mem _ (turn_mem (by omega))

theorem reflected_sieve_identity {B : ℕ} (hB : 2≤B) (k : ℕ) :
    mobiusSignal B.factorial k + reversedSignal B.factorial k = -sieveMask B k := by
  let Q := B.factorial
  have hQ0 : 0 < Q := Nat.factorial_pos _
  have hQ2 : 2 ∣ Q := Nat.dvd_factorial (by decide) hB
  have hQ1 : Q ≠ 1 := fun h => by rw [h] at hQ2; norm_num at hQ2
  have term (d : ℕ) (hd : d ∈ Q.divisors) :
      (ArithmeticFunction.moebius d : ℚ) * turn d k +
          (ArithmeticFunction.moebius d : ℚ) * turn d (d-k%d) =
      (ArithmeticFunction.moebius d : ℚ) -
          (if d ∣ k then (ArithmeticFunction.moebius d : ℚ) else 0) := by
    rw [← mul_add,opposite_turn (Nat.pos_of_mem_divisors hd)]
    by_cases h : d ∣ k
    · simp [h,Nat.mod_eq_zero_of_dvd h]
    · simp [h,show k%d ≠ 0 from fun eq => h (Nat.dvd_of_mod_eq_zero eq)]
  change (∑ d ∈ Q.divisors, _) + (∑ d ∈ Q.divisors, _) = _
  rw [← Finset.sum_add_distrib,Finset.sum_congr rfl term,Finset.sum_sub_distrib,
      mu_divisor_sum,if_neg hQ1,common_divisor_sum hQ0,zero_sub]
  rfl

def density (Q : ℕ) : ℚ := ∑ d ∈ Q.divisors, (ArithmeticFunction.moebius d:ℚ)/d
def survivorCount (B k : ℕ) : ℚ := ∑ t ∈ Finset.range k, sieveMask B (t+1)

theorem signed_sieve_count (B k : ℕ) :
    mobiusSignal B.factorial k = (k:ℚ)*density B.factorial - survivorCount B k := by
  let Q := B.factorial
  have hpos : 0<Q := Nat.factorial_pos _
  have step (j : ℕ) : mobiusSignal Q (j+1) - mobiusSignal Q j = density Q - sieveMask B (j+1) := by
    change (∑ d ∈ Q.divisors, _) - (∑ d ∈ Q.divisors, _) =
      (∑ d ∈ Q.divisors, _) - (if (j+1).Coprime Q then 1 else 0)
    rw [← common_divisor_sum hpos, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    rw [← mul_sub,turn_step (Nat.pos_of_mem_divisors hd)]
    by_cases h : d ∣ j+1
    · simp [h,div_eq_mul_inv]; ring
    · simp [h,div_eq_mul_inv]
  induction k with
  | zero => simp [mobiusSignal,turn,survivorCount]
  | succ k ih =>
    have hs := step k
    dsimp [Q] at hs
    simp only [survivorCount, Finset.sum_range_succ, Nat.cast_add, Nat.cast_one] at ih ⊢
    linarith

theorem count_prefix {k B : ℕ} (hk : 0<k) (inFrame : k≤B) : survivorCount B k = 1 := by
  unfold survivorCount
  calc
    _ = ∑ i ∈ Finset.range k, tick (i+1) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact sieve_on_prefix (by omega) ((Nat.succ_le_of_lt (Finset.mem_range.mp hi)).trans inFrame)
    _ = _ := by simp [tick,hk.ne']

/-- A natural full-layer repair. The apparent survivor counts are a legal residue fit. -/
def adjacentRepair (p k : ℕ) : ℚ :=
  survivorCount (p-1) k - (p:ℚ)*survivorCount (p-1) (k/p)

theorem adjacentRepair_mem {p : ℕ} (hp : 2≤p) : adjacentRepair p ∈ fits := by
  let Q := (p-1).factorial
  have eq : adjacentRepair p = ((p:ℚ)*density Q) • turn p - mobiusSignal Q +
        (p:ℚ) • dilate p (mobiusSignal Q) := by
    funext k
    have h := signed_sieve_count (p-1) k
    have h' := signed_sieve_count (p-1) (k/p)
    have divmod : (p:ℚ)*((k/p:ℕ):ℚ)+((k%p:ℕ):ℚ) = (k:ℚ) := by exact_mod_cast Nat.div_add_mod k p
    change survivorCount (p-1) k - (p:ℚ)*survivorCount (p-1) (k/p) =
      (p:ℚ)*density Q*turn p k - mobiusSignal Q k + (p:ℚ)*mobiusSignal Q (k/p)
    have hp0 : (p:ℚ) ≠ 0 := by positivity
    have hphase : (p:ℚ)*density Q*turn p k = density Q*((k%p:ℕ):ℚ) := by
      unfold turn; field_simp
    rw [hphase]
    dsimp only [Q]
    rw [h,h',← divmod]
    ring
  rw [eq]
  exact fits.add_mem (fits.sub_mem (fits.smul_mem _ (turn_mem hp)) (mobiusSignal_mem _))
    (fits.smul_mem _ (dilate_mem hp (mobiusSignal_mem _)))

theorem adjacentRepair_prefix {p k : ℕ} (hk : 0<k) (less : k<p) : adjacentRepair p k = 1 := by
  unfold adjacentRepair
  rw [Nat.div_eq_of_lt less, count_prefix hk (by omega : k≤p-1)]
  simp [survivorCount]

/-- Even a perfect growing prefix does not close this candidate: its first reset alone
already costs at least one sixth, for every p>=2. -/
theorem adjacentRepair_loss {p : ℕ} (hp : 2≤p) : (1:ℝ)/6 ≤ loss occupied (adjacentRepair p) := by
  have hprev := count_prefix (B:=p-1) (k:=p-1) (by omega) le_rfl
  have hOne := count_prefix (B:=p-1) (k:=1) (by decide) (by omega)
  have hcount : survivorCount (p-1) p ≤ 2 := by
    have plus : survivorCount (p-1) p = survivorCount (p-1) (p-1) + sieveMask (p-1) p := by
      have step (B n : ℕ) : survivorCount B (n+1) = survivorCount B n + sieveMask B (n+1) := by
        simp only [survivorCount,Finset.sum_range_succ]
      simpa only [Nat.sub_add_cancel (show 1≤p by omega)] using step (p-1) (p-1)
    rw [plus,hprev]
    unfold sieveMask
    split_ifs <;> norm_num
  have hval : adjacentRepair p p ≤ 2-(p:ℚ) := by
    simp only [adjacentRepair,Nat.div_self (by omega : 0<p),hOne,mul_one]
    linarith
  have hlow := fit_row_lower (adjacentRepair_mem hp) (p-1)
  rw [show p-1+1=p by omega] at hlow
  have hcast : (p:ℝ)-1 ≤ ((1-adjacentRepair p p : ℚ):ℝ) := by
    exact_mod_cast (show (p:ℚ)-1 ≤ 1-adjacentRepair p p by linarith)
  have hpR : (2:ℝ) ≤ p := by exact_mod_cast hp
  have hw : rowWeight (p-1) = 1/((p:ℝ)*(p+1)) := by
    simp only [rowWeight,Nat.cast_sub (by omega : 1≤p),Nat.cast_one]; ring
  rw [hw] at hlow
  apply le_trans _ hlow
  have hs := pow_le_pow_left₀ (show (0:ℝ) ≤ p-1 by linarith) hcast 2
  field_simp
  nlinarith [mul_nonneg (sub_nonneg.mpr hpR) (show 0 ≤ 5*(p:ℝ)-3 by linarith)]

/-- The unresolved arithmetic transport. Both errors are measured on all actual rows. -/
def ReflectionRepair : Prop :=
  ∀ ε : ℝ, 0<ε → ∃ B : ℕ, 2≤B ∧ 1/((B:ℝ)+1)<ε ∧
    ∃ f ∈ fits, loss (reversedSignal B.factorial) f < ε

private lemma mask_bounded (B : ℕ) : bounded (sieveMask B) := by
  refine ⟨1,fun k => ?_⟩
  by_cases h : k.Coprime B.factorial
  · rw [sieveMask,if_pos h]; norm_num
  · rw [sieveMask,if_neg h]; norm_num

private lemma reflection_swap {B : ℕ} (hB : 2≤B) (f : ℕ → ℚ) :
    loss (sieveMask B) (-mobiusSignal B.factorial-f) = loss (reversedSignal B.factorial) f := by
  unfold loss cost
  apply tsum_congr
  intro n
  have h := reflected_sieve_identity hB (n+1)
  have eq : sieveMask B (n+1) - (-mobiusSignal B.factorial (n+1)-f (n+1)) =
      -(reversedSignal B.factorial (n+1)-f (n+1)) := by linarith
  simp only [Pi.sub_apply,Pi.neg_apply,eq,Rat.cast_neg,neg_sq]

theorem rh_of_reflection_repair (repair : ReflectionRepair) : RiemannHypothesis := by
  apply rh_of_first_tick
  intro ε hε
  obtain ⟨B,hB,hm,f,hf,hr⟩ := repair (ε/4) (by positivity)
  let g := -mobiusSignal B.factorial - f
  have hg : g ∈ fits := fits.sub_mem (fits.neg_mem (mobiusSignal_mem _)) hf
  refine ⟨g,hg,?_⟩
  have htb : bounded tick := ⟨1,fun k => by by_cases h : k=1 <;> simp [tick,h]⟩
  have tri := loss_triangle tick (sieveMask B) g htb (mask_bounded _) (fit_properties hg).2
  have eq : loss (sieveMask B) g = loss (reversedSignal B.factorial) f := reflection_swap hB _
  linarith [sieve_loss B]

theorem reflection_repair_of_tick (can : Approximable) : ReflectionRepair := by
  intro ε hε
  have htol : 0 < ε/8 := by positivity
  obtain ⟨j,hj⟩ := exists_nat_one_div_lt htol
  let B := max 2 j
  have hB : 2≤B := le_max_left _ _
  have hBj : j≤B := le_max_right _ _
  have hcut : 1/((B:ℝ)+1) < ε/8 := lt_of_le_of_lt
    (one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hBj 1)) hj
  obtain ⟨g,hg,he⟩ := can (ε/8) htol
  let f := -mobiusSignal B.factorial - g
  have hf : f ∈ fits := fits.sub_mem (fits.neg_mem (mobiusSignal_mem _)) hg
  refine ⟨B,hB,by linarith,f,hf,?_⟩
  have htb : bounded tick := ⟨1,fun k => by by_cases h : k=1 <;> simp [tick,h]⟩
  have hsym : loss (sieveMask B) tick = loss tick (sieveMask B) := by
    unfold loss cost
    apply tsum_congr
    intro n
    simp only [Pi.sub_apply,Rat.cast_sub]
    ring
  have tri := loss_triangle (sieveMask B) tick g (mask_bounded _) htb (fit_properties hg).2
  have hfg : -mobiusSignal B.factorial - f = g := by dsimp [f]; abel
  have hs := reflection_swap hB f
  rw [hfg] at hs
  linarith [sieve_loss B]

/-- A legal pair of nearby forward transports reads the actual signed sieve edge. -/
theorem contrast_reads_sieve {B p h t r : ℕ} (hp : 0<p) (ht : 0<t)
    (scale : h*t≤p) (inside : r<p) :
    contrast p h (mobiusSignal B.factorial) (p*t+r) =
      if r<h*t then density B.factorial - sieveMask B t else 0 := by
  rw [contrast_value hp ht scale inside]
  split_ifs
  · cases t with
    | zero => omega
    | succ t =>
      simp only [Nat.add_one_sub_one,signed_sieve_count,survivorCount,Finset.sum_range_succ,
        Nat.cast_add,Nat.cast_one]
      ring
  · rfl

#print axioms PALRH.OneTick.contrast_reads_sieve
#print axioms PALRH.OneTick.rh_of_reflection_repair
#print axioms PALRH.OneTick.adjacentRepair_loss
#print axioms PALRH.OneTick.sieve_loss
#print axioms PALRH.OneTick.sieve_not_finite
#print axioms PALRH.OneTick.reflected_sieve_identity
end PALRH.OneTick
