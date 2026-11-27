import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Tactic

namespace IntegerWidth

/-- Positive whole numbers sharing 17's low word. -/
def wordTwin (k : ℕ) : ℕ := (2^64)^(k+1)+17

theorem residue (k : ℕ) : wordTwin k % 2^64 = 17 := by
  unfold wordTwin
  rw [pow_succ,Nat.add_mod,Nat.mul_mod_left]
  norm_num

theorem composite (k : ℕ) : ¬(wordTwin k).Prime := by
  have dv : 3 ∣ wordTwin k := by
    rw [Nat.dvd_iff_mod_eq_zero,wordTwin,Nat.add_mod,Nat.pow_mod]
    norm_num
  intro prime
  rcases (Nat.dvd_prime prime).mp dv with one|all
  · omega
  · have positive : 0<(2^64:ℕ)^(k+1) := by positivity
    unfold wordTwin at all
    omega

theorem same_cast (k : ℕ) : (wordTwin k).toUInt64 = (17:UInt64) := by
  apply UInt64.toNat_inj.mp
  simpa using residue k

/-- An exact prime specified by its least-factor rule, independent of digit expansion. -/
def euclidPrime (n : ℕ) : ℕ := (n.factorial+1).minFac

theorem prime_above (n : ℕ) : (euclidPrime n).Prime ∧ n<euclidPrime n := by
  let p:=euclidPrime n
  have pp : p.Prime := Nat.minFac_prime (by have := Nat.factorial_pos n; omega)
  refine ⟨pp,?_⟩
  by_contra! small
  have old : p ∣ n.factorial := Nat.dvd_factorial pp.pos small
  have next : p ∣ n.factorial+1 := Nat.minFac_dvd _
  exact pp.not_dvd_one ((Nat.dvd_add_iff_right old).mpr next)

theorem symbolic_prime :
    (euclidPrime (2^(2^100))).Prime ∧ 2^(2^100)<euclidPrime (2^(2^100)) :=
  prime_above _

theorem symbolic_composite : ¬(wordTwin (2^94-1)).Prime := composite _

/-- Every positive divisor of a common modulus gives the same report for these
two original numbers. The second number has the first as a proper factor. -/
theorem all_divisors {p m : ℕ} (pp : p.Prime) (positive : 0<m) :
    p<p*(m+1) ∧ ¬(p*(m+1)).Prime ∧ ∀ d : ℕ, d ∣ m → (p*(m+1))%d=p%d := by
  have up:=pp.pos
  refine ⟨by nlinarith only [Nat.mul_pos up positive],?_,?_⟩
  · exact Nat.not_prime_mul pp.ne_one (by omega)
  · intro d hd
    have dv : d ∣ p*m := dvd_mul_of_dvd_right hd _
    rw [Nat.mul_add,Nat.mul_one,Nat.add_mod,Nat.mod_eq_zero_of_dvd dv,zero_add,Nat.mod_mod]

/-- Even fixing the low word in advance at 17 leaves both possibilities above
every size bound. Dirichlet's theorem supplies the larger prime. -/
theorem beyond_any_word (width bound : ℕ) :
    ∃ p c : ℕ, bound<p ∧ p<c ∧ p.Prime ∧ ¬c.Prime ∧
      p%2^width=17%2^width ∧ c%2^width=17%2^width := by
  let m:=2^width
  have mp : 0<m := by dsimp [m];positivity
  have cop : Nat.Coprime 17 m := (by decide : Nat.Coprime 17 2).pow_right _
  obtain ⟨p,after,pp,congruent⟩:=Nat.forall_exists_prime_gt_and_modEq bound mp.ne' cop
  have pair:=all_divisors pp mp
  exact ⟨p,p*(m+1),after,pair.1,pp,pair.2.1,congruent,(pair.2.2 m (dvd_refl _)).trans congruent⟩

/-- Every part of a product above and below a radix cut, including the carry
made when the two low digits are multiplied. -/
theorem product_carry (m x y : ℕ) :
    ((x%m)*(y%m))%m +
      m * (((x%m)*(y%m))/m + (x/m)*(y%m) + (x%m)*(y/m) + m*(x/m)*(y/m)) = x*y := by
  calc
    _ = (((x%m)*(y%m))%m + m*(((x%m)*(y%m))/m)) +
          m*((x/m)*(y%m) + (x%m)*(y/m) + m*(x/m)*(y/m)) := by ring
    _ = (x%m+m*(x/m))*(y%m+m*(y/m)) := by rw [Nat.mod_add_div];ring
    _ = x*y := by rw [Nat.mod_add_div,Nat.mod_add_div]

theorem first_base_five_spill :
    (5^16:UInt64)*(5^16:UInt64)=3273344365508751233 ∧
    (5^32:ℕ)=1262*2^64+3273344365508751233 := by decide +kernel

/-- The released natural numeral, read independently of the original proof module. -/
def releasedExample : ℕ := 65794571027774832745588537266486439382601586586498771901135640963549130131839564588689999034983373394040350895271937

theorem released_word : releasedExample.toUInt64.toNat=586678051033346049 := by decide +kernel

theorem released_word_composite : ¬(releasedExample.toUInt64.toNat).Prime := by
  rw [released_word]
  intro prime
  have factor : 3 ∣ 586678051033346049 := ⟨195559350344448683, by norm_num⟩
  rcases (Nat.dvd_prime prime).mp factor with h|h <;> norm_num at h

theorem seventeen_is_prime : Nat.Prime 17 := by decide

#print axioms IntegerWidth.same_cast
#print axioms IntegerWidth.composite
#print axioms IntegerWidth.symbolic_prime
#print axioms IntegerWidth.beyond_any_word
#print axioms IntegerWidth.released_word_composite
#print axioms IntegerWidth.product_carry
#print axioms IntegerWidth.first_base_five_spill

end IntegerWidth

/-- The argument arrives at run time. Only short readings of the expanded integer are printed. -/
def main (args : List String) : IO Unit := do
  let some e := args.head?.bind String.toNat? | throw (IO.userError "positive exponent required")
  let n : Nat := ((1 : Nat) <<< e) - 1
  let asInt : Int := Int.ofNat n
  IO.println s!"bits={n.log2+1} bytes={(n.log2+8)/8} mod131071={asInt%131071} mod17={asInt%17} last9={n%1000000000}"
  let word : UInt64 := (18446744073709551615 : UInt64) + 1
  let whole : Nat := (18446744073709551615 : Nat) + 1
  let twin := whole+17
  IO.println s!"UInt64={word} Nat={whole} twin64={twin.toUInt64.toNat} cofactor={twin/3}"
