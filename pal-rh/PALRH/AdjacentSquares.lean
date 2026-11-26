import PALRH.SquareHoles

open Finset
namespace PALRH.AdjacentSquares
open SquareHoles

def commonSlots (b : ℕ) := trace (b^2) b ∩ trace (b^2) (b+1)

private theorem unpack {n b d : ℕ} (h : d ∈ trace n b) :
    ∃ t : ℕ, 0<t ∧ t≤b-2 ∧ d+t^2=b^2 := by
  obtain ⟨img,_⟩ := mem_filter.mp h
  obtain ⟨t,ht,eqn⟩ := mem_image.mp img
  obtain ⟨tp,cap⟩ := mem_Icc.mp ht
  refine ⟨t,tp,cap,?_⟩
  rw [←eqn]
  exact Nat.sub_add_cancel (Nat.pow_le_pow_left (by omega : t≤b) 2)

private theorem read_factors {b d : ℕ} (h : d∈commonSlots b) :
    ∃ r v : ℕ, 1<r ∧ r<v ∧ r*v=2*b+1 ∧ d=b^2-((v-r)/2)^2 := by
  obtain ⟨first,second⟩ := mem_inter.mp h
  obtain ⟨t,tp,tc,left⟩ := unpack first
  obtain ⟨u,_,_,right⟩ := unpack second
  have diff : u^2=t^2+2*b+1 := by nlinarith only [left,right]
  have tu : t<u := by
    by_contra! back
    have bound := Nat.pow_le_pow_left back 2
    omega
  let r := u-t
  let v := u+t
  have split : r+t=u := Nat.sub_add_cancel tu.le
  have prod : r*v=2*b+1 := by
    have same := congrArg (fun x : ℕ => x*(u+t)) split
    change (r+t)*(u+t)=u*(u+t) at same
    dsimp [v]
    nlinarith only [same,diff]
  have proper : 1<r := by
    by_contra! small
    have one : r=1 := by omega
    have ut : u=t+1 := by omega
    rw [ut] at diff
    nlinarith only [diff,show t+1≤b by omega]
  have vv : v=r+2*t := by dsimp [v];omega
  refine ⟨r,v,proper,by omega,prod,?_⟩
  rw [show (v-r)/2=t by omega]
  omega

/-- Every proper unequal factor pair lands in the actual band, even in its top ninth. -/
private theorem place {b r v : ℕ} (large : 4≤b) (proper : 1<r)
    (lt : r<v) (prod : r*v=2*b+1) :
    let t := (v-r)/2
    let d := b^2-t^2
    d∈commonSlots b ∧ 8*b^2<9*d ∧ ((b+1)^2-d).sqrt-(b^2-d).sqrt=r := by
  let t := (v-r)/2
  let u := (v+r)/2
  let d := b^2-t^2
  have parity : (r%2)*(v%2)%2=1 := by rw [←Nat.mul_mod,prod];omega
  have oddR : r%2=1 := by
    by_contra! h
    have z : r%2=0 := by omega
    simp [z] at parity
  have oddV : v%2=1 := by
    by_contra! h
    have z : v%2=0 := by omega
    simp [z] at parity
  have join : 2*t+r=v := by dsimp [t];omega
  have rise : u=t+r := by dsimp [u,t];omega
  have cap := Nat.mul_le_mul_right v (by omega : 3≤r)
  have tp : 0<t := by omega
  have short : 3*t<b := by omega
  have sq := Nat.pow_lt_pow_left short (by decide : 2≠0)
  have inside : t^2≤b^2 := Nat.pow_le_pow_left (by omega : t≤b) 2
  have left : d+t^2=b^2 := Nat.sub_add_cancel inside
  have upper : d+u^2=(b+1)^2 := by
    have equal := congrArg (fun x : ℕ => r*x) join
    rw [rise]
    nlinarith only [left,prod,show r*(2*t+r)=r*v from equal]
  have high : 8*b^2<9*d := by nlinarith only [left,sq]
  have band : 2*b^2<3*d ∧ d≤b^2 := by omega
  have decode : ((b+1)^2-d).sqrt-(b^2-d).sqrt=r := by
    rw [show (b+1)^2-d=u^2 by omega,show b^2-d=t^2 by omega,Nat.sqrt_eq',Nat.sqrt_eq']
    omega
  change d∈commonSlots b ∧ 8*b^2<9*d ∧ _
  refine ⟨mem_inter.mpr ⟨?_,?_⟩,high,decode⟩
  · exact mem_filter.mpr ⟨mem_image.mpr ⟨t,mem_Icc.mpr ⟨tp,by omega⟩,rfl⟩,band⟩
  · apply mem_filter.mpr
    exact ⟨mem_image.mpr ⟨u,mem_Icc.mpr ⟨by omega,by omega⟩,by omega⟩,band⟩

theorem overlap_iff {b d : ℕ} (large : 4≤b) :
    d∈commonSlots b ↔ ∃ r v : ℕ, 1<r ∧ r<v ∧ r*v=2*b+1 ∧ d=b^2-((v-r)/2)^2 := by
  refine ⟨read_factors,?_⟩
  rintro ⟨r,v,proper,lt,prod,rfl⟩
  exact (place large proper lt prod).1

theorem in_top_ninth {b d : ℕ} (large : 4≤b) (h : d∈commonSlots b) :
    8*b^2<9*d := by
  obtain ⟨r,v,proper,lt,prod,rfl⟩ := read_factors h
  exact (place large proper lt prod).2.1

/-- The smaller factor in a proper, unequal factorization of the gap. -/
def divisorsBelowRoot (b : ℕ) : Finset ℕ :=
  (range (2*b+2)).filter (fun r => 1<r ∧ r ∣ 2*b+1 ∧ r<(2*b+1)/r)

private def slot (b r : ℕ) := b^2-(((2*b+1)/r-r)/2)^2

theorem number_of_overlaps {b : ℕ} (large : 4≤b) :
    (commonSlots b).card=(divisorsBelowRoot b).card := by
  have image : commonSlots b = (divisorsBelowRoot b).image (slot b) := by
    ext d
    constructor
    · intro member
      obtain ⟨r,v,proper,lt,prod,equal⟩ := read_factors member
      have quotient : (2*b+1)/r=v := by rw [←prod,Nat.mul_div_cancel_left _ (by omega)]
      have upper : r≤2*b+1 := by
        rw [←prod]
        exact Nat.le_mul_of_pos_right _ (by omega)
      have inside : r∈divisorsBelowRoot b := mem_filter.mpr
        ⟨mem_range.mpr (by omega),proper,⟨v,prod.symm⟩,by omega⟩
      exact mem_image.mpr ⟨r,inside,by simpa [slot,quotient] using equal.symm⟩
    · intro member
      obtain ⟨r,hr,rfl⟩ := mem_image.mp member
      obtain ⟨_,proper,dv,lt⟩ := mem_filter.mp hr
      exact (place large proper lt (Nat.mul_div_cancel' dv)).1
  rw [image]
  apply card_image_iff.mpr
  intro r hr v hv eqn
  obtain ⟨_,rp,rd,rl⟩ := mem_filter.mp hr
  obtain ⟨_,vp,vd,vl⟩ := mem_filter.mp hv
  have left := (place large rp rl (Nat.mul_div_cancel' rd)).2.2
  have right := (place large vp vl (Nat.mul_div_cancel' vd)).2.2
  change ((b+1)^2-slot b r).sqrt-(b^2-slot b r).sqrt=r at left
  change ((b+1)^2-slot b v).sqrt-(b^2-slot b v).sqrt=v at right
  rw [eqn] at left
  exact left.symm.trans right

theorem board_eight : commonSlots 64 = {3696} := by decide +kernel

#print axioms PALRH.AdjacentSquares.overlap_iff
#print axioms PALRH.AdjacentSquares.in_top_ninth
#print axioms PALRH.AdjacentSquares.number_of_overlaps
#print axioms PALRH.AdjacentSquares.board_eight
end PALRH.AdjacentSquares
