import PALRH.ProductClock

open Finset
open scoped BigOperators

noncomputable section
namespace PALRH.ProductBridge
open ShapeObservation PrefixReturn ShapeStrip ReturnedHorizon ProductClock

/-- Number of whole columns reserved for possible separate-prime clock flags. -/
def guard (j : ℕ) := (16^j) ⌈/⌉ (root j)
def usable (j : ℕ) := root j/13-guard j
def upperTime (j m : ℕ) := root j*((m-root j)+usable j)
def lowerTime (j m : ℕ) := root j*((m-root j)-root j/13)

def upper (j m : ℕ) : Prop :=
  let x:=root j
  let h:=upperTime j m
  product (board j) m*x^h≤(x+1)^h

def lower (j m : ℕ) : Prop :=
  let x:=root j
  let h:=lowerTime j m
  (x+1)^h≤product (board j) m*x^h

private theorem root_pos (j : ℕ) : 0<root j := by unfold root;positivity
private theorem before_root {n m : ℕ} (inside : m≤n.sqrt) : tickSum n m=0 := by
  apply sum_eq_zero
  intro d hd
  have dx:=(mem_Icc.mp hd).2.trans inside
  have stop : ¬(2≤d ∧ d.gcd n.sqrt.factorial=1) := by
    rintro ⟨lo,clean⟩
    exact (not_lt_of_ge dx) ((SieveFrame.factorial_test lo (dx.trans (Nat.sqrt_le_self n))).mp clean).2
  simp [tickAt,stop]

private theorem guard_fits {j : ℕ} (jp : 0<j) : guard j≤root j/13 := by
  let r:ℕ:=4^j
  have sq : r^2=16^j := by dsimp [r];rw [←pow_mul,mul_comm j 2,pow_mul];rfl
  have low : 4≤(j+1)^2 := by nlinarith only [Nat.mul_le_mul_left (j+1) (show 2≤j+1 by omega),jp]
  have rootE : root j=4*r*(j+1)^2 := by unfold root;rw [pow_succ];dsimp [r];ring
  have cap : 13*r≤root j := by
    rw [rootE];nlinarith only [Nat.mul_le_mul_left (4*r) low,Nat.zero_le r]
  apply le_trans (b:=r)
  · apply (ceilDiv_le_iff_le_mul (root_pos j)).mpr
    rw [←sq,pow_two];exact Nat.mul_le_mul_right _ (by omega)
  · apply (Nat.le_div_iff_mul_le (by decide : 0<13)).mpr
    simpa [Nat.mul_comm] using cap

theorem row_upper {j m : ℕ} (mh : m≤16^j) (fits : upper j m) :
    tickSum (board j) m≤root j*(m-root j)+root j*(root j/13) := by
  let n:=board j
  let x:=root j
  have nx : n.sqrt=x := Nat.sqrt_eq' _
  have xp:=root_pos j
  have np : 0<n := Nat.pow_pos xp
  by_cases early : m≤x
  · rw [before_root (show m≤(board j).sqrt by simpa [n,x,nx] using early)];omega
  have jp : 0<j := by
    by_contra! z;have hz : j=0 := by omega
    subst j;norm_num [x,root] at early mh;omega
  have mn : m≤n := by have :=covers j;dsimp [n];omega
  have q:=from_one_product (n:=n) (m:=m) (h:=upperTime j m) np mn (by rw [nx];exact fits)
  have reserves : m≤x*guard j := mh.trans ((ceilDiv_le_iff_le_mul xp).mp le_rfl)
  have paid : usable j+guard j=x/13 := Nat.sub_add_cancel (guard_fits jp)
  change tickSum n m≤x*(m-x)+x*(x/13)
  change tickSum n m≤x*((m-x)+usable j)+m at q
  have eq:=congrArg (x*·) paid
  nlinarith only [q,reserves,eq]

private theorem inverse_cover {x q h : ℕ} (xp : 0<x) (price : (x+1)^h≤q*x^h) :
    h≤clock x q := by
  by_contra! late
  obtain ⟨k,hk⟩:=Nat.exists_eq_add_of_le (show clock x q+1≤h from late)
  have pay:=(integer_test (q:=q) xp).mp (le_refl (clock x q))
  rw [show h=clock x q+(k+1) by omega, pow_add (x+1) (clock x q) (k+1), pow_add x (clock x q) (k+1),
    ←Nat.mul_assoc q (x^clock x q) (x^(k+1))] at price
  have strictly : x^(k+1)<(x+1)^(k+1) := Nat.pow_lt_pow_left (Nat.lt_succ_self _) (Nat.succ_ne_zero _)
  have contra := (Nat.mul_le_mul_right (x^(k+1)) pay).trans_lt
    (Nat.mul_lt_mul_of_pos_left strictly (pow_pos (by omega) _))
  omega

theorem row_lower {j m : ℕ} (mh : m≤16^j) (fits : lower j m) :
    root j*(m-root j)≤tickSum (board j) m+root j*(root j/13) := by
  let n:=board j
  let x:=root j
  have nx : n.sqrt=x := Nat.sqrt_eq' _
  have xp:=root_pos j
  have mn : m≤n := by have :=covers j;dsimp [n];omega
  have size:=inverse_cover xp fits
  have lo:=(cumulative_rounding n m (Nat.pow_pos xp) mn).1
  rw [nx] at lo
  change x*((m-x)-x/13)≤clock x (product n m) at size
  have sum : m-x≤((m-x)-x/13)+x/13 := by omega
  have gain:=Nat.mul_le_mul_left x sum
  change x*(m-x)≤tickSum n m+x*(x/13)
  nlinarith only [lo,size,gain]

/-- A per-row balance pays the genuine triangular prefix using only nonnegative
weights. The same expression accounts for the starts that have already retired. -/
theorem weighted_sign {j m : ℕ} (mh : m≤16^j) (s : ℝ)
    (row : ∀ i≤m, s*plainPrefix (ReturnedReading.increment (board j)) i≤
      (root j:ℝ)*(root j/13:ℕ)) :
    13*(s*SignedStrip.score j m)≤(board j:ℝ)^2 := by
  let n:=board j
  let x:=root j
  let a:ℝ:=(x:ℝ)*(x/13:ℕ)
  let v:=ReturnedReading.increment n
  have nx : n.sqrt=x := Nat.sqrt_eq' _
  have mn : m≤n := by have :=covers j;dsimp [n];omega
  have sign : s*SignedStrip.score j m≤(n:ℝ)*a := by
    change s*(((prefixJobs n m+smallReturn n m:ℕ):ℝ)-(x:ℝ)*plainArea n m)≤_
    rw [←nx,←ReturnedReading.weight n m mn,ShapeStrip.prefix_identity,mul_add,mul_sum]
    have low : 0≤(n:ℝ)-m := sub_nonneg.mpr (by exact_mod_cast mn)
    have atCut:=mul_le_mul_of_nonneg_left (row m le_rfl) low
    have old : ∑ i ∈ range m,s*plainPrefix v i≤(m:ℝ)*a := by
      calc
        _ ≤ ∑ _ ∈ range m,a := sum_le_sum (fun i hi => row i (mem_range.mp hi).le)
        _ = _ := by simp
    nlinarith only [atCut,old]
  have spec : (n:ℝ)=(x:ℝ)^2 := by dsimp [n,x,board];push_cast;rfl
  have quota : 13*((x/13:ℕ):ℝ)≤x := by exact_mod_cast Nat.mul_div_le x 13
  dsimp [a] at sign
  change 13*(s*SignedStrip.score j m)≤(n:ℝ)^2
  have cut:=mul_le_mul_of_nonneg_left quota (show 0≤(n:ℝ)*(x:ℝ) by positivity)
  have equal : (n:ℝ)*x*x=(n:ℝ)^2 := by rw [spec];ring
  nlinarith only [sign,cut,equal]

theorem row_form (j i : ℕ) :
    plainPrefix (ReturnedReading.increment (board j)) i=
      (tickSum (board j) i:ℝ)-(root j:ℝ)*((i-root j:ℕ):ℝ) := by
  rw [ReturnedReading.plain,show (board j).sqrt=root j from Nat.sqrt_eq' _]
  unfold tickSum;rw [Nat.cast_sum]
  by_cases inside : i≤root j
  · rw [min_eq_left inside,Nat.sub_eq_zero_of_le inside];push_cast;ring
  · rw [min_eq_right (le_of_not_ge inside),Nat.cast_sub (le_of_not_ge inside)];ring

theorem upper_score {j m : ℕ} (fits : ∀ i≤16^j, upper j i) (mh : m≤16^j) :
    13*(1*SignedStrip.score j m)≤(board j:ℝ)^2 := by
  apply weighted_sign mh 1
  intro i im
  rw [one_mul,row_form]
  have q:=row_upper (im.trans mh) (fits i (im.trans mh))
  have realQ : (tickSum (board j) i:ℝ)≤(root j:ℝ)*((i-root j:ℕ):ℝ)+(root j:ℝ)*(root j/13:ℕ) := by
    exact_mod_cast q
  linarith only [realQ]

/-- The product alone can fund actual arrivals in the declared pocket. -/
theorem timely_of_product {j : ℕ} (fits : ∀ m≤16^j, upper j m) : SignedStrip.timely j := by
  apply (SignedStrip.timely_iff j).mpr
  intro m mh
  have z:=upper_score fits mh
  rw [one_mul,SignedStrip.score] at z
  have natural : 13*(prefixJobs (board j) m+smallReturn (board j) m)≤
      13*(root j*plainArea (board j) m)+(board j)^2 := by
    exact_mod_cast (show (13:ℝ)*((prefixJobs (board j) m+smallReturn (board j) m:ℕ):ℝ)≤
      13*((root j:ℝ)*plainArea (board j) m)+(board j:ℝ)^2 by linarith only [z])
  unfold SignedStrip.surplus;omega

theorem rh_of_upper_product (all : ∀ j m : ℕ, m≤16^j → upper j m) : RiemannHypothesis :=
  SignedStrip.rh_of_shared_placement (fun j => timely_of_product (all j))

theorem lower_score {j m : ℕ} (fits : ∀ i≤16^j, lower j i) (mh : m≤16^j) :
    13*((-1)*SignedStrip.score j m)≤(board j:ℝ)^2 := by
  apply weighted_sign mh (-1)
  intro i im
  rw [neg_one_mul,row_form]
  have q:=row_lower (im.trans mh) (fits i (im.trans mh))
  have realQ : (root j:ℝ)*((i-root j:ℕ):ℝ)≤
        (tickSum (board j) i:ℝ)+(root j:ℝ)*(root j/13:ℕ) := by exact_mod_cast q
  linarith only [realQ]

theorem rh_of_lower_product (all : ∀ j m : ℕ, m≤16^j → lower j m) : RiemannHypothesis := by
  apply SignedStrip.one_orientation (-1) (Or.inr rfl)
  intro j m mh
  have z:=lower_score (all j) mh
  nlinarith only [z,sq_nonneg ((board j):ℝ)]

private theorem grid_address {x p quota r i n : ℕ} (xp : 0<x) (live : r<x*(p-x)+quota) (endpoints : i+p<n) :
    r<quota ∨
      let d:=x+1+(r-quota)/x
      let layer:=(r-quota)%x
      d≤p ∧ i+d<n ∧ layer<x ∧ quota+(d-x-1)*x+layer=r := by
  by_cases early : r<quota
  · exact Or.inl early
  · right
    have room : r-quota<x*(p-x) := by omega
    have idx : (r-quota)/x<p-x :=
      (Nat.div_lt_iff_lt_mul xp).mpr (by simpa only [Nat.mul_comm (p-x) x] using room)
    let k:=(r-quota)/x
    change k<p-x at idx
    have kp : 0≤k := Nat.zero_le _
    have gap : 0<p-x := kp.trans_lt idx
    have xp2 : x≤p := by omega
    have endD : x+1+k≤p := by have := Nat.sub_add_cancel xp2; omega
    change x+1+k≤p ∧ i+(x+1+k)<n ∧ (r-quota)%x<x ∧ quota+(x+1+k-x-1)*x+(r-quota)%x=r
    have identity : k*x+(r-quota)%x=r-quota := Nat.div_add_mod' _ _
    exact ⟨endD,by omega,Nat.mod_lt _ xp,by rw [show x+1+k-x-1=k by simp [Nat.add_assoc],Nat.add_assoc,identity,Nat.add_comm,Nat.sub_add_cancel (le_of_not_gt early)]⟩

/-- File the original tick by its cumulative ordinal in its own starting row.
The first bank has x times floor(x/13) lanes per row. Beyond it, division gives an
already released distance and layer. -/
theorem fixed_row_address {j p i t : ℕ} (ph : p≤16^j) (positive : 0<p)
    (valid : i+p<board j) (job : t<tickAt (board j) p) (fit : upper j p) :
    let x:=root j
    let quota:=x*(x/13)
    let r:=tickSum (board j) (p-1)+t
    r<quota ∨
      let d:=x+1+(r-quota)/x
      let layer:=(r-quota)%x
      d≤p ∧ i+d<board j ∧ layer<x ∧ quota+(d-x-1)*x+layer=r := by
  let x:=root j
  let quota:=x*(x/13)
  let r:=tickSum (board j) (p-1)+t
  have xp:=root_pos j
  have step : tickSum (board j) p=tickSum (board j) (p-1)+tickAt (board j) p := by
    obtain ⟨a,rfl⟩:=Nat.exists_eq_succ_of_ne_zero positive.ne'
    unfold tickSum;rw [sum_Icc_succ_top (by omega : 1≤a+1)];simp
  have size:=row_upper ph fit
  rw [step] at size
  have live : r<x*(p-x)+quota := by dsimp [r,quota,x];omega
  exact grid_address (x:=x) (r:=r) (quota:=quota) xp live valid

/-- If the sign is chosen separately after each individual cut, the ordered thresholds
pass for every nonnegative input value. -/
theorem per_cut_choice (j m q : ℕ) :
    q*(root j)^(upperTime j m)≤(root j+1)^(upperTime j m) ∨
    (root j+1)^(lowerTime j m)≤q*(root j)^(lowerTime j m) := by
  by_cases hi : clock (root j) q≤upperTime j m
  · exact Or.inl ((integer_test (root_pos j)).mp hi)
  · right
    have lt : lowerTime j m≤upperTime j m := Nat.mul_le_mul_left _ (by omega)
    have gone : ¬q*(root j)^(lowerTime j m)≤(root j+1)^(lowerTime j m) :=
      fun h => hi (((integer_test (root_pos j)).mpr h).trans lt)
    exact (lt_of_not_ge gone).le

#print axioms PALRH.ProductBridge.fixed_row_address
#print axioms PALRH.ProductBridge.per_cut_choice

#print axioms PALRH.ProductBridge.timely_of_product
#print axioms PALRH.ProductBridge.rh_of_upper_product
#print axioms PALRH.ProductBridge.rh_of_lower_product
end PALRH.ProductBridge
