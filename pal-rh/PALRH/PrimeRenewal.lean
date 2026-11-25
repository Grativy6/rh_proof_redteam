import PALRH.RectangleBalance
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Chebyshev

open Finset Set Filter MeasureTheory
open scoped BigOperators Topology
noncomputable section
namespace PALRH.PrimeRenewal
open RectangleBalance TaperedNewton
abbrev AR := ArithmeticFunction ℝ

def realMarks : AR := ⟨fun n => (marks n:ℝ),by simp [ArithmeticFunction.map_zero]⟩
def gate : AR := ⟨fun n => (allowed n:ℝ),by simp [ArithmeticFunction.map_zero]⟩
def timesLog (f : AR) : AR := ⟨fun n => Real.log n*f n,by simp⟩
def primePowers : AR := ArithmeticFunction.vonMangoldt.pmul gate

private lemma gate_product (a b : ℕ) : gate (a*b)=gate a*gate b := by
  have val (n : ℕ) : gate n=(if n.Coprime 6 then (1:ℝ) else 0) := by
    change ((allowed n:ℚ):ℝ)=_
    rw [show allowed n=(if n.Coprime 6 then 1 else 0) by rfl]
    split <;> norm_num
  simp only [val,Nat.coprime_mul_iff_left]
  split_ifs <;> norm_num <;> tauto

private theorem inverse : realMarks*gate=1 := by
  ext n
  have h := DFunLike.congr_fun marks_inverse n
  rw [ArithmeticFunction.mul_apply,ArithmeticFunction.one_apply] at h ⊢
  change (∑ t ∈ n.divisorsAntidiagonal,(marks t.1:ℝ)*(allowed t.2:ℝ))=_
  by_cases atone : n=1 <;> simp only [atone,if_true,if_false] at h ⊢ <;> exact_mod_cast h

theorem logarithm_product (f g : AR) : timesLog (f*g)=timesLog f*g+f*timesLog g := by
  ext n
  change Real.log n*(f*g) n=_
  rw [ArithmeticFunction.add_apply,ArithmeticFunction.mul_apply,ArithmeticFunction.mul_apply,
    ArithmeticFunction.mul_apply,Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  have eq := (Nat.mem_divisorsAntidiagonal.mp ht).1
  have ip : t.1≠0 := Nat.ne_zero_of_mem_divisorsAntidiagonal ht |>.1
  have jp : t.2≠0 := Nat.ne_zero_of_mem_divisorsAntidiagonal ht |>.2
  change Real.log n*(f t.1*g t.2)=Real.log t.1*f t.1*g t.2+f t.1*(Real.log t.2*g t.2)
  rw [←eq,Nat.cast_mul,Real.log_mul (by exact_mod_cast ip) (by exact_mod_cast jp)]
  ring

private theorem gate_log : timesLog gate=primePowers*gate := by
  ext n
  rw [ArithmeticFunction.mul_apply]
  have point (t : ℕ×ℕ) (ht : t∈n.divisorsAntidiagonal) :
      primePowers t.1*gate t.2=ArithmeticFunction.vonMangoldt t.1*gate n := by
    change (ArithmeticFunction.vonMangoldt t.1*gate t.1)*gate t.2=_
    rw [mul_assoc,←gate_product,(Nat.mem_divisorsAntidiagonal.mp ht).1]
  rw [Finset.sum_congr rfl point,Nat.sum_divisorsAntidiagonal (fun i _ => ArithmeticFunction.vonMangoldt i*gate n),
    ←Finset.sum_mul,ArithmeticFunction.vonMangoldt_sum]
  rfl

theorem log_marks : timesLog realMarks = -(realMarks*primePowers) := by
  have trivial : timesLog (1:AR)=0 := by
    ext n
    change Real.log n*(1:AR) n=0
    rw [ArithmeticFunction.one_apply]
    by_cases first : n=1 <;> simp [first]
  have eq := logarithm_product realMarks gate
  rw [inverse,trivial,gate_log,show realMarks*(primePowers*gate)=primePowers by
    calc
      _=primePowers*(realMarks*gate) := by ring
      _=primePowers := by rw [inverse,mul_one]] at eq
  calc
    timesLog realMarks = (timesLog realMarks*gate)*realMarks := by
      rw [mul_assoc,mul_comm gate realMarks,inverse,mul_one]
    _ = -(realMarks*primePowers) := by
      have cancel : timesLog realMarks*gate= -primePowers := eq_neg_of_add_eq_zero_left eq.symm
      rw [cancel];ring

/-- Every log contribution to the actual carried edge is charged to a labelled prime power. -/
theorem finite_log_renewal {x : ℝ} (xp : 0<x) :
    Real.log x*edge x+observe primePowers x =
      ∑ n ∈ Finset.Icc 1 ⌊2*x⌋₊, (marks n:ℝ)/n*taper (n/x)*Real.log (x/n) := by
  have local_charge (n : ℕ) :
      (∑ d ∈ n.divisors, (marks d:ℝ)*primePowers (n/d))= -(Real.log n*(marks n:ℝ)) := by
    have q := DFunLike.congr_fun log_marks n
    rw [ArithmeticFunction.neg_apply,ArithmeticFunction.mul_apply,
      Nat.sum_divisorsAntidiagonal (fun i j => realMarks i*primePowers j)] at q
    change Real.log n*(marks n:ℝ)= -(∑ d ∈ n.divisors,(marks d:ℝ)*primePowers (n/d)) at q
    change _= -_
    linarith
  rw [edge,Finset.mul_sum,observe_eq _ xp,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have non : (n:ℝ)≠0 := by exact_mod_cast (show 0<n from (Finset.mem_Icc.mp hn).1).ne'
  rw [local_charge,Real.log_div xp.ne' non]
  ring

theorem exterior_term {x t : ℝ} (xp : 0<x) (after : x<t) (before : t≤2*x) :
    edge (x/t)=2-t/x := by
  have tp := xp.trans after
  have low : 1/2≤x/t := (le_div_iff₀ tp).mpr (by linarith)
  have high : x/t<1 := (div_lt_one tp).mpr after
  have max_one : ⌊2*(x/t)⌋₊=1 := by
    apply le_antisymm
    · exact Nat.le_of_lt_succ ((Nat.floor_lt (by positivity)).mpr (by push_cast;linarith))
    · exact Nat.floor_pos.mpr (by linarith)
  rw [edge,max_one]
  have mone : marks 1=1 := by change (ArithmeticFunction.moebius 1:ℚ)*_=1;simp [allowed]
  simp only [Finset.Icc_self,Finset.sum_singleton,Nat.cast_one,mone,Rat.cast_one,div_one,one_mul]
  have lo : 1≤t/x := (one_le_div xp).mpr after.le
  have hi : t/x≤2 := (div_le_iff₀ xp).mpr (by linarith)
  rw [show 1/(x/t)=t/x by field_simp,taper,min_eq_right (by linarith : 2-t/x≤1),max_eq_right (by linarith : 0≤2-t/x)]

#print axioms PALRH.PrimeRenewal.log_marks
#print axioms PALRH.PrimeRenewal.finite_log_renewal
#print axioms PALRH.PrimeRenewal.exterior_term

theorem prime_charge {p k : ℕ} (prime : p.Prime) (rough : p.Coprime 6) (kp : 0<k) :
    primePowers (p^k)=Real.log p := by
  have ok : (p^k).Coprime 6 := rough.pow_left k
  change ArithmeticFunction.vonMangoldt (p^k)*(allowed (p^k):ℝ)=_
  rw [ArithmeticFunction.vonMangoldt_apply_pow kp.ne',ArithmeticFunction.vonMangoldt_apply_prime prime,
    show allowed (p^k)=(if (p^k).Coprime 6 then (1:ℚ) else 0) by rfl,if_pos ok]
  norm_num

/-- At the first scale past 25/2, the repeated five has a nonzero and explicit coefficient. -/
theorem first_square_price : primePowers 25/25*edge ((13:ℝ)/25)=Real.log 5/325 := by
  have atFive : primePowers (5^2)=Real.log 5 :=
    prime_charge (by decide : Nat.Prime 5) (by decide) (by decide)
  rw [show 25=(5:ℕ)^2 by decide,atFive,exterior_term (by norm_num : (0:ℝ)<13)
    (by norm_num : (13:ℝ)<25) (by norm_num : (25:ℝ)≤2*13)]
  ring

/-- A small removed multiplier is also small in the receiving cofactor's logarithmic frame. -/
theorem earlier_cut {u t : ℝ} (up : 0≤u) (one : 1≤t) (small : t≤(u/80)^2) :
    Real.sqrt t≤(u-Real.log t)/40 := by
  have tp : 0<t := by linarith
  have sq := Real.sq_sqrt tp.le
  have rt := Real.sqrt_pos.mpr tp
  have root : Real.sqrt t≤u/80 := le_of_sq_le_sq (by linarith) (by positivity)
  have log := Real.log_le_sub_one_of_pos rt
  have twice : 2*Real.log (Real.sqrt t)=Real.log t := by
    rw [two_mul,←Real.log_mul rt.ne' rt.ne',Real.mul_self_sqrt tp.le]
  linarith

#print axioms PALRH.PrimeRenewal.prime_charge
#print axioms PALRH.PrimeRenewal.earlier_cut


def primeMass (n : ℕ) : ℝ := if n.Prime then Real.log n else 0
def thetaN (n : ℕ) : ℝ := ∑ p ∈ Finset.Icc 1 n, primeMass p
def rootPrimes (n : ℕ) : ℝ := ∑ p ∈ Finset.Icc 1 n, primeMass p/Real.sqrt p

private theorem theta_cap (n : ℕ) : thetaN n≤4*(n:ℝ) := by
  have eq : thetaN n=Chebyshev.theta n := by
    rw [Chebyshev.theta,thetaN,Nat.floor_natCast,Finset.sum_filter]
    have I : Finset.Ioc 0 n=Finset.Icc 1 n := by ext p; simp only [Finset.mem_Ioc,Finset.mem_Icc];omega
    rw [I]
    rfl
  rw [eq]
  have bound := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg (α:=ℝ) n)
  exact bound.trans (mul_le_mul_of_nonneg_right
    (by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)] : Real.log 4≤4) (by positivity))

private lemma step_theta (n : ℕ) : thetaN (n+1)=thetaN n+primeMass (n+1) := by
  unfold thetaN;rw [Finset.sum_Icc_succ_top (by omega)]

private lemma step_root (n : ℕ) : rootPrimes (n+1)=rootPrimes n+primeMass (n+1)/Real.sqrt (n+1:ℕ) := by
  unfold rootPrimes;rw [Finset.sum_Icc_succ_top (by omega)]

theorem root_prime_budget (N : ℕ) : rootPrimes N≤8*Real.sqrt N := by
  have main (n : ℕ) (pos : 0<n) :
      rootPrimes n≤thetaN n/Real.sqrt n+4*(Real.sqrt n-1) := by
    induction n with
    | zero => omega
    | succ n old =>
      by_cases first : n=0
      · subst n;norm_num [rootPrimes,thetaN,primeMass]
      have np : 0<n := Nat.pos_of_ne_zero first
      specialize old np
      let a := Real.sqrt n
      let b := Real.sqrt ((n:ℝ)+1)
      have ap : 0<a := Real.sqrt_pos.mpr (by positivity)
      have bp : 0<b := Real.sqrt_pos.mpr (by positivity)
      have ab : a≤b := Real.sqrt_le_sqrt (by linarith)
      have aa : a^2=(n:ℝ) := Real.sq_sqrt (by positivity)
      have diff : (n:ℝ)*(1/a-1/b)=(a/b)*(b-a) := by rw [←aa];field_simp
      have unit : 0≤1/a-1/b := sub_nonneg.mpr (one_div_le_one_div_of_le ap ab)
      have norm := mul_le_mul_of_nonneg_right (theta_cap n) unit
      have t := mul_le_mul_of_nonneg_right ((div_le_one bp).mpr ab) (sub_nonneg.mpr ab)
      have pay : thetaN n*(1/a-1/b)≤4*(b-a) := by
        calc
          _ ≤ 4*(n:ℝ)*(1/a-1/b) := norm
          _ = 4*((a/b)*(b-a)) := by rw [mul_assoc,diff]
          _ ≤ _ := mul_le_mul_of_nonneg_left (by simpa using t) (by norm_num)
      rw [step_root,step_theta]
      push_cast
      change rootPrimes n+primeMass (n+1)/b≤(thetaN n+primeMass (n+1))/b+4*(b-1)
      change rootPrimes n≤thetaN n/a+4*(a-1) at old
      simp only [div_eq_mul_inv] at old pay ⊢
      linarith
  rcases N.eq_zero_or_pos with z|p
  · simp [z,rootPrimes]
  apply (main N p).trans
  have rp : 0<Real.sqrt N := Real.sqrt_pos.mpr (by positivity)
  have cap : thetaN N/Real.sqrt N≤4*Real.sqrt N := (div_le_iff₀ rp).mpr (by
    rw [mul_assoc,Real.mul_self_sqrt (by positivity)];exact theta_cap N)
  linarith

#print axioms PALRH.PrimeRenewal.root_prime_budget


private def floorLogs (N k : ℕ) :=
  ∑ d ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt d*((k/d:ℕ):ℝ)

private theorem floors_recover (N k : ℕ) (inside : k≤N) :
    floorLogs N k=∑ n ∈ Finset.Icc 1 k, Real.log n := by
  induction k with
  | zero => simp [floorLogs]
  | succ k old =>
    have step (d : ℕ) : ArithmeticFunction.vonMangoldt d*(((k+1)/d:ℕ):ℝ)-
        ArithmeticFunction.vonMangoldt d*((k/d:ℕ):ℝ)=
        if d∣k+1 then ArithmeticFunction.vonMangoldt d else 0 := by
      by_cases dvd : d∣k+1
      · rw [Nat.succ_div_of_dvd dvd,if_pos dvd];push_cast;ring
      · rw [Nat.succ_div_of_not_dvd dvd,if_neg dvd,sub_self]
    have ds : (Finset.Icc 1 N).filter (fun d => d∣k+1)=(k+1).divisors := by
      ext d
      simp only [Finset.mem_filter,Finset.mem_Icc,Nat.mem_divisors]
      constructor
      · exact fun h => ⟨h.2,by omega⟩
      · exact fun h => ⟨⟨Nat.pos_of_dvd_of_pos h.1 (by omega),(Nat.le_of_dvd (by omega) h.1).trans inside⟩,h.1⟩
    have law : floorLogs N (k+1)-floorLogs N k=Real.log (k+1:ℕ) := by
      unfold floorLogs
      rw [←Finset.sum_sub_distrib,Finset.sum_congr rfl (fun d _ => step d),←Finset.sum_filter,ds,
        ArithmeticFunction.vonMangoldt_sum]
    rw [Finset.sum_Icc_succ_top (by omega),←old (by omega)]
    linarith

theorem prime_harmonic_budget {N : ℕ} (hp : 0<N) :
    (∑ n ∈ Finset.Icc 1 N, primeMass n/n)≤Real.log N+(Real.log 4+4) := by
  let I := Finset.Icc 1 N
  have nr : 0<(N:ℝ) := by positivity
  have compare (d : ℕ) (hd : d∈I) :
      (N:ℝ)*(ArithmeticFunction.vonMangoldt d/d)≤
        ArithmeticFunction.vonMangoldt d*((N/d:ℕ):ℝ)+ArithmeticFunction.vonMangoldt d := by
    have dp : 0<d := (Finset.mem_Icc.mp hd).1
    have up : N≤(N/d+1)*d := by nlinarith only [Nat.div_add_mod N d,Nat.mod_lt N dp]
    have cast : (N:ℝ)≤(((N/d:ℕ):ℝ)+1)*d := by exact_mod_cast up
    have bound := (div_le_iff₀ (by exact_mod_cast dp : 0<(d:ℝ))).mpr cast
    have charge := mul_le_mul_of_nonneg_left bound (ArithmeticFunction.vonMangoldt_nonneg (n:=d))
    calc
      _ = ArithmeticFunction.vonMangoldt d*((N:ℝ)/d) := by ring
      _ ≤ _ := charge.trans_eq (by ring)
  have v := Finset.sum_le_sum compare
  rw [←Finset.mul_sum,Finset.sum_add_distrib] at v
  change _≤floorLogs N N+(∑ n ∈ I, ArithmeticFunction.vonMangoldt n) at v
  rw [floors_recover N N le_rfl] at v
  have first : (∑ n ∈ Finset.Icc 1 N, Real.log n)≤(N:ℝ)*Real.log N := by
    have c (n : ℕ) (hn : n∈Finset.Icc 1 N) : Real.log n≤Real.log N :=
      Real.log_le_log (by exact_mod_cast (show 0<n from (Finset.mem_Icc.mp hn).1))
        (by exact_mod_cast (Finset.mem_Icc.mp hn).2)
    simpa [Nat.card_Icc] using Finset.sum_le_sum c
  have psi : (∑ n ∈ I, ArithmeticFunction.vonMangoldt n)=Chebyshev.psi N := by
    rw [Chebyshev.psi,Nat.floor_natCast]
    have eq : Finset.Ioc 0 N=I := by ext n;simp only [I,Finset.mem_Ioc,Finset.mem_Icc];omega
    rw [eq]
  rw [psi] at v
  have pcap := Chebyshev.psi_le_const_mul_self nr.le
  have sums : (∑ n ∈ I, ArithmeticFunction.vonMangoldt n/n)≤Real.log N+(Real.log 4+4) := by
    apply le_of_mul_le_mul_left (a:=(N:ℝ)) _ nr
    linarith
  apply le_trans _ sums
  apply Finset.sum_le_sum
  intro n _
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  by_cases prime : n.Prime
  · simp [primeMass,prime,ArithmeticFunction.vonMangoldt_apply_prime prime]
  · simp [primeMass,prime,ArithmeticFunction.vonMangoldt_nonneg]

/-- Raw prime squares have an upper price with leading coefficient one half in log T. -/
theorem square_multiplier_budget {T : ℝ} (tp : 1≤T) :
    (∑ p ∈ Finset.Icc 1 ⌊Real.sqrt T⌋₊, primeMass p/p)≤Real.log T/2+(Real.log 4+4) := by
  have rt : 1≤Real.sqrt T := by simpa using Real.sqrt_le_sqrt tp
  have pos := Nat.floor_pos.mpr rt
  apply (prime_harmonic_budget pos).trans
  have cap := Real.log_le_log (by exact_mod_cast pos : 0<(⌊Real.sqrt T⌋₊:ℝ)) (Nat.floor_le (Real.sqrt_nonneg T))
  have power := Real.log_sqrt (show 0≤T by linarith)
  linarith

#print axioms PALRH.PrimeRenewal.prime_harmonic_budget
#print axioms PALRH.PrimeRenewal.square_multiplier_budget

end PALRH.PrimeRenewal
