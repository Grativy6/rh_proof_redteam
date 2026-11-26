import PALRH.TickBoard

namespace PALRH.TickPacking
open TickBoard PrimeBand

/-- Stored coordinates are the starting site, positive distance and layer. -/
def place (n x p i t : ℕ) : ℕ×ℕ×ℕ :=
  let half:=(n+1)/2
  (i%half, (2*(t/x)+i/half+1)*p,t%x)

def restore (n x p : ℕ) (z : ℕ×ℕ×ℕ) : ℕ×ℕ :=
  let code:=z.2.1/p-1
  ((code%2)*((n+1)/2)+z.1,(code/2)*x+z.2.2)

/-- Middle prime trips occupy disjoint multiple-labelled distances in the first half.
The actual destination recovers the large prime and the original trip. -/
private theorem place_bounded {n x p b i t : ℕ} (xp : 0<x) (prime : p.Prime) (large : n.sqrt<p)
    (room : 4*b*p≤n) (start : i<n-p) (run : t<b*x) :
    let z:=place n x p i t
    z.1+z.2.1<n ∧ z.2.1≤n/2 ∧ z.2.2<x ∧ restore n x p z=(i,t) ∧
      (∀ q : ℕ, q.Prime → n.sqrt<q → q∣z.2.1 → q=p) := by
  let half:=(n+1)/2
  let u:=t/x
  let side:=i/half
  let co:=2*u+side+1
  have inn := start.trans_le (Nat.sub_le n p)
  have np : 0<n := by omega
  have hp : 0<half := by dsimp [half];omega
  have ix : i<2*half := by dsimp [half];omega
  have side_small : side<2 := (Nat.div_lt_iff_lt_mul hp).mpr ix
  have ub : u<b := (Nat.div_lt_iff_lt_mul xp).mpr run
  have cpos : 0<co := Nat.succ_pos _
  have ccap : 2*co≤4*b := by dsimp [co];omega
  have paid : (co*p)*2≤n := calc
    _ = (2*co)*p := by ring
    _ ≤ _ := Nat.mul_le_mul_right p ccap
    _ ≤ _ := room
  have middle : co*p≤n/2 := (Nat.le_div_iff_mul_le (by decide : 0<2)).mpr paid
  have left := Nat.mod_lt i hp
  have edge : i%half+co*p<n := by
    have total : half+n/2=n := by dsimp [half];omega
    omega
  have div : co*p/p=co := Nat.mul_div_cancel _ prime.pos
  have pred : co-1=side+u*2 := by dsimp [co];simp [Nat.mul_comm,Nat.add_comm]
  have s1 : (co-1)%2=side := by rw [pred];simp [Nat.mod_eq_of_lt side_small]
  have s2 : (co-1)/2=u := by rw [pred];simp [Nat.add_mul_div_right _ _ (by decide : 0<2),Nat.div_eq_of_lt side_small]
  have back : restore n x p (place n x p i t)=(i,t) := by
    change (((co*p/p-1)%2)*half+i%half,((co*p/p-1)/2)*x+t%x)=(i,t)
    rw [div,s1,s2]
    apply Prod.ext
    · simpa [side,Nat.mul_comm,Nat.add_comm] using Nat.mod_add_div i half
    · simpa [u,Nat.mul_comm,Nat.add_comm] using Nat.mod_add_div t x
  refine ⟨edge,middle,Nat.mod_lt _ xp,back,?_⟩
  intro q qp qlarge qd
  exact unique_large_prime (Nat.mul_pos cpos prime.pos) (middle.trans (Nat.div_le_self _ _))
    qp prime qlarge large qd (dvd_mul_left p co)

/-- Middle prime trips occupy disjoint multiple-labelled distances in the first half.
The actual destination recovers the large prime and the original trip. -/
theorem owned_placement {n x p b i t : ℕ} (xp : 0<x) (prime : p.Prime) (large : n.sqrt<p)
    (bits : p≤2^b) (room : 4*b*p≤n) (start : i<n-p) (layer : t<ticks n x p) :
    let z:=place n x p i t
    z.1+z.2.1<n ∧ z.2.1≤n/2 ∧ z.2.2<x ∧ restore n x p z=(i,t) ∧
      (∀ q : ℕ, q.Prime → n.sqrt<q → q∣z.2.1 → q=p) := place_bounded xp prime large room start
    (layer.trans_le (bit_price (n:=n) xp bits))

/-- The universal middle placement also works with two entire layers physically set aside. -/
theorem two_layers_reserved {n x p b i t : ℕ} (bp : 0<b) (height : 2*b+2≤x) (prime : p.Prime) (large : n.sqrt<p)
    (bits : p≤2^b) (room : 4*(b+1)*p≤n) (start : i<n-p) (layer : t<ticks n x p) :
    let z:=place n (x-2) p i t
    z.1+z.2.1<n ∧ z.2.1≤n/2 ∧ z.2.2<x-2 ∧ restore n (x-2) p z=(i,t) ∧
      (∀ q : ℕ, q.Prime → n.sqrt<q → q∣z.2.1 → q=p) := by
  have small : 0<x-2 := by omega
  have run:=layer.trans_le (bit_price (n:=n) (by omega : 0<x) bits)
  have eq : x-2+2=x := by omega
  have afford : b*x≤(b+1)*(x-2) := by
    nlinarith only [height,congrArg (fun d : ℕ => b*d) eq,eq]
  exact place_bounded small prime large room start (run.trans_le afford)

#print axioms PALRH.TickPacking.owned_placement
#print axioms PALRH.TickPacking.two_layers_reserved
end PALRH.TickPacking
