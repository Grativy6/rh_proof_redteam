import PALRH.AdjacentSquares

open Finset
open scoped BigOperators
namespace PALRH.OneSquare
open DoubledRuler DoubledPrice RulerOmissions

private def nextUnit (m : ℕ) :=
  if (¬5 ∣ m) ∧ (¬17 ∣ m) then m
  else if (¬5 ∣ m+1) ∧ (¬17 ∣ m+1) then m+1 else m+2

private theorem next_bounds (m : ℕ) :
    m≤nextUnit m ∧ nextUnit m≤m+2 ∧ (¬5 ∣ nextUnit m) ∧ (¬17 ∣ nextUnit m) := by
  unfold nextUnit
  split_ifs <;> omega

def center (k : ℕ) := 21*nextUnit ((k^2+20)/21)

theorem center_frame (k : ℕ) :
    k^2≤center k ∧ center k≤k^2+62 ∧ 3 ∣ center k ∧ 7 ∣ center k ∧
      (¬ 5 ∣ center k) ∧ (¬ 17 ∣ center k) := by
  let m := (k^2+20)/21
  let j := nextUnit m
  have facts : m≤j ∧ j≤m+2 ∧ (¬ 5 ∣ j) ∧ (¬ 17 ∣ j) := next_bounds m
  have div := Nat.mod_add_div (k^2+20) 21
  have rem := Nat.mod_lt (k^2+20) (by decide : 0<21)
  change k^2≤21*j ∧ 21*j≤k^2+62 ∧ 3 ∣ 21*j ∧ 7 ∣ 21*j ∧ (¬ 5 ∣ 21*j) ∧ (¬ 17 ∣ 21*j)
  change (k^2+20)%21+21*m=k^2+20 at div
  refine ⟨by omega,by omega,⟨7*j,by ring⟩,⟨3*j,by ring⟩,?_,?_⟩
  · intro h
    exact ((Nat.Prime.dvd_mul (by decide : Nat.Prime 5)).mp h).elim
      (by decide : (¬ 5 ∣ 21)) facts.2.2.1
  · intro h
    exact ((Nat.Prime.dvd_mul (by decide : Nat.Prime 17)).mp h).elim
      (by decide : (¬ 17 ∣ 21)) facts.2.2.2

def inward (k b : ℕ) : Finset ℕ :=
  ((Icc 1 (b-2)).image (fun t => b^2-t^2)).filter (fun d => 2*k^4<5*d ∧ d≤k^4)

def outward (k b : ℕ) (S : Finset ℕ) : Finset ℕ :=
  ((Icc 1 (k^2)).image (fun t => b^2+t^2)).filter
    (fun d => k^4<d ∧ d≤2*k^4 ∧ ∃ p ∈ S, 1<p ∧ p<d ∧ p ∣ d)

def labels : Finset ℕ := {2,3,5,7,17}

def marks (k b : ℕ) := inward k b ∪ outward k b labels

def credit (k b : ℕ) := ∑ d ∈ marks k b, (extra (k^4) d).toNat

def paysAt (k b : ℕ) := SquareReference.pays k (credit k b)

def pays (k : ℕ) : Prop := ∃ b ∈ Icc (k^2) (k^2+62), paysAt k b

theorem proper_marks {k b d : ℕ} (h : d∈marks k b) : 0<d ∧ d≤2*k^4 ∧ ¬d.Prime := by
  obtain left|right := mem_union.mp h
  · obtain ⟨img,low,cap⟩ := mem_filter.mp left
    obtain ⟨t,ht,equal⟩ := mem_image.mp img
    obtain ⟨tp,tc⟩ := mem_Icc.mp ht
    change t≤b-2 at tc
    have add : b-t+t=b := Nat.sub_add_cancel (by omega)
    have mul : (b-t)*(b+t)=b^2-t^2 := by
      apply Nat.eq_sub_of_add_eq
      calc
        (b-t)*(b+t)+t^2 = (b-t+t)^2 := by nth_rw 2 [←add];ring
        _ = b^2 := congrArg (fun x : ℕ => x^2) add
    refine ⟨by omega,by omega,?_⟩
    change b^2-t^2=d at equal
    rw [←equal,←mul]
    apply Nat.not_prime_mul <;> omega
  · obtain ⟨_,low,cap,p,_,proper,small,dv⟩ := mem_filter.mp right
    refine ⟨by omega,cap,?_⟩
    intro prime
    rcases (Nat.dvd_prime prime).mp dv with one|whole <;> omega

noncomputable section
theorem area_of_payment {k b : ℕ} (large : 8≤k) (bcap : b≤k^2+62) (paid : paysAt k b) :
    QuarticBoards.error (k^4) ≤ 144*(k:ℝ)^6 := by
  have square := Nat.pow_le_pow_left large 2
  have inner : (inward k b).card≤b := by
    exact (card_filter_le _ _).trans (card_image_le.trans (by simp [Nat.card_Icc]))
  have outer : (outward k b labels).card≤k^2 := by
    exact (card_filter_le _ _).trans (card_image_le.trans (by simp [Nat.card_Icc]))
  have count : (marks k b).card≤3*k^2 := by
    have total := @card_union_le ℕ _ (inward k b) (outward k b labels)
    change (marks k b).card≤_ at total
    omega
  let N:=2*k^4
  have per {d : ℕ} (hd : d∈marks k b) : ((extra (k^4) d).toNat:ℝ) ≤ 7*(N:ℝ)^6 := by
    obtain ⟨dp,cap,_⟩:=proper_marks hd
    have same : ((extra (k^4) d).toNat:ℝ)=(extra (k^4) d:ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg (extra_nonneg dp cap)
    rw [same]
    exact extra_cap dp cap
  have sum := sum_le_sum (s:=marks k b) (fun d hd => per hd)
  rw [sum_const,nsmul_eq_mul] at sum
  have scaled := mul_le_mul_of_nonneg_right
    (by exact_mod_cast count : ((marks k b).card:ℝ)≤3*(k:ℝ)^2) (by positivity : 0≤7*(N:ℝ)^6)
  have bound := SquareReference.area_from_credit (credit:=credit k b) (reserve:=42)
    (by omega : 2≤k) (by
      unfold credit
      push_cast
      dsimp [N] at sum scaled
      push_cast at sum scaled
      nlinarith only [sum,scaled]) paid
  norm_num at bound
  exact bound

theorem rh_of_one_square (K : ℕ) (late : ∀ k : ℕ, K≤k → pays k) : RiemannHypothesis := by
  apply OneSidedBoard.rh_of_eventual_upper_area (max K 8) (C:=144) (by norm_num)
  intro k hk _
  obtain ⟨b,hb,paid⟩ := late k ((le_max_left _ _).trans hk)
  exact area_of_payment ((le_max_right _ _).trans hk) (mem_Icc.mp hb).2 paid

theorem rh_of_chosen_center (K : ℕ) (late : ∀ k : ℕ, K≤k → paysAt k (center k)) :
    RiemannHypothesis := by
  apply rh_of_one_square K
  intro k hk
  exact ⟨center k,mem_Icc.mpr ⟨(center_frame k).1,(center_frame k).2.1⟩,late k hk⟩

theorem seven_with_seventeen : outward 8 64 {17} = {4097,4352,4420,5185,5321,6596,6800} := by
  decide +kernel

theorem prime_seventeen_stays : outward 2 4 {17} = ∅ := by decide +kernel

#print axioms PALRH.OneSquare.center_frame
#print axioms PALRH.OneSquare.proper_marks
#print axioms PALRH.OneSquare.area_of_payment
#print axioms PALRH.OneSquare.rh_of_one_square
#print axioms PALRH.OneSquare.rh_of_chosen_center
#print axioms PALRH.OneSquare.seven_with_seventeen
#print axioms PALRH.OneSquare.prime_seventeen_stays
end
end PALRH.OneSquare
