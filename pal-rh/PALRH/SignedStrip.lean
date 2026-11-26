import PALRH.PowerRecovery
import PALRH.ReturnedTaper

open Finset
open scoped BigOperators

noncomputable section
namespace PALRH.SignedStrip
open ShapeStrip ShapeObservation PrefixReturn ReturnedHorizon LinearPrimeIntegral QuarticBoards

def score (j m : ℕ) : ℝ :=
  (prefixJobs (board j) m+smallReturn (board j) m:ℕ)-(root j:ℝ)*plainArea (board j) m

private theorem shift_head (v : ℕ → ℝ) (m : ℕ) :
    (∑ i ∈ range m,v (i+1))=∑ d ∈ Icc 1 m,v d := by
  induction m with
  | zero => simp
  | succ m ih => rw [sum_range_succ,sum_Icc_succ_top (by omega : 1≤m+1),ih]

private theorem indexed (n m : ℕ) (v : ℕ → ℝ) (s : ℝ) :
    (∑ i ∈ range m,((n:ℝ)-i-1)*(s*v (i+1)))=s*weighted n v m := by
  unfold weighted
  rw [←shift_head,mul_sum]
  apply sum_congr rfl;intro i _;push_cast;ring

private theorem shorter (m : ℕ) (v : ℕ → ℝ) (s : ℝ) :
    (∑ i ∈ range m,((m:ℝ)-i)*(s*v (i+1)))=s*∑ i ∈ range (m+1),plainPrefix v i := by
  have end0 : weighted (m+1) v (m+1)=weighted (m+1) v m := by
    unfold weighted;rw [sum_Icc_succ_top (by omega : 1≤m+1)];simp
  have all:=prefix_identity (m+1) v (m+1)
  rw [end0,sub_self,zero_mul,zero_add] at all
  rw [←all,←indexed];push_cast
  apply sum_congr rfl;intro i _;ring

private def primeTerm (d : ℕ) : ℝ := if d.Prime then Real.log d else 0

private theorem prime_total (N : ℕ) : primeWalk N=∑ i ∈ range N,Chebyshev.theta i := by
  have f (i : ℕ) : plainPrefix primeTerm i=Chebyshev.theta i := by
    simp only [plainPrefix,primeTerm,Chebyshev.theta,Nat.floor_natCast,
      ←Finset.Icc_add_one_left_eq_Ioc,Nat.zero_add,Finset.sum_filter]
  have equal : primeWalk N=weighted N primeTerm N := by
    unfold primeWalk weighted primeTerm
    apply sum_congr rfl;intro i _;split_ifs <;> simp
  rw [equal,prefix_identity,sub_self,zero_mul,zero_add]
  exact sum_congr rfl (fun _ _ => f _)

private theorem ramp_total (N : ℕ) : 2*(∑ i ∈ range N,(i:ℝ))=(N:ℝ)^2-N := by
  induction N with
  | zero => simp
  | succ N ih => rw [sum_range_succ];push_cast;nlinarith only [ih]

/-- Price the signed prime area at any shorter head without ever subtracting a
prefix inequality. The decreasing triangular reweighting has positive coefficients. -/
theorem short_area {s : ℝ} (unit : |s|=1) {j : ℕ}
    (tests : ∀ i≤16^j, s*score j i≤(board j:ℝ)^2)
    {m : ℕ} (mh : m≤16^j) :
    s*(primeWalk (m+1)-((m+1:ℕ):ℝ)^2/2)≤7*(root j:ℝ)*(m+1) := by
  let n:=board j
  let x:=root j
  let v:=ReturnedReading.increment n
  have pos : 0<x := by dsimp [x,root];positivity
  have xr : 0<(x:ℝ) := by exact_mod_cast pos
  have square : (n:ℝ)=(x:ℝ)^2 := by dsimp [n,x,board];push_cast;rfl
  have nx : n.sqrt=x := Nat.sqrt_eq' _
  have np : 0<n := Nat.pow_pos pos
  have mi : 1≤(16:ℕ)^j := Nat.pow_pos (by decide)
  have cover:=covers j
  change 4*16^j≤n at cover
  have limit : m+1<n := by omega
  have n2 : (2:ℝ)≤n := by exact_mod_cast (by omega : 2≤n)
  have all (i : ℕ) (ih : i≤m) :
      (∑ k ∈ range i,((n:ℝ)-k-1)*(s*v (k+1)))≤(n:ℝ)^2 := by
    rw [indexed,ReturnedReading.weight n i (by omega),nx]
    exact tests i (ih.trans mh)
  have cheap:=ReturnedTaper.shorter_taper n m limit (fun k => s*v (k+1)) all
  rw [shorter] at cheap
  have flat : (m:ℝ)/((n:ℝ)-1)*(n:ℝ)^2≤2*m*n := by
    rw [div_mul_eq_mul_div];apply (div_le_iff₀ (by linarith)).mpr
    nlinarith only [mul_nonneg (show 0≤(m:ℝ)*(n:ℝ) by positivity) (show 0≤(n:ℝ)-2 by linarith)]
  have target:=cheap.trans flat
  have each (i : ℕ) (hi : i∈range (m+1)) :
      s*((x:ℝ)*(Chebyshev.theta i-i))≤s*plainPrefix v i+4*n := by
    have im:=mem_range.mp hi
    have cal:=prefix_calibration n i np (by omega)
    rw [nx] at cal
    have small : (x:ℝ)*(min i x:ℕ)≤n := by
      rw [square,pow_two]
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast min_le_right i x) xr.le
    have error : |(x:ℝ)*(Chebyshev.theta i-i)-plainPrefix v i|≤4*n := by
      rw [ReturnedReading.plain,nx]
      obtain ⟨l,r⟩:=abs_sub_le_iff.mp cal
      apply abs_le.mpr
      constructor <;> nlinarith only [l,r,small,mul_nonneg xr.le (Nat.cast_nonneg (α:=ℝ) (min i x)),Nat.cast_nonneg (α:=ℝ) n]
    have price : s*((x:ℝ)*(Chebyshev.theta i-i)-plainPrefix v i)≤4*n := by
      apply (le_abs_self _).trans;rw [abs_mul,unit,one_mul];exact error
    linarith only [price]
  have sum_price:=sum_le_sum each
  simp only [←Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_sub_distrib,
    Finset.sum_const,Finset.card_range,nsmul_eq_mul] at sum_price
  rw [←prime_total] at sum_price
  have h0:=ramp_total (m+1)
  have sig : -1≤s := by simpa only [unit] using neg_abs_le s
  apply le_of_mul_le_mul_left (a:=(x:ℝ)) _ xr
  rw [square] at sum_price target
  push_cast at sum_price h0 ⊢
  have sr:=mul_le_mul_of_nonneg_right sig (show 0≤(x:ℝ)*((m:ℝ)+1) by positivity)
  have eq:=congrArg (fun z : ℝ => s*(x:ℝ)*z) h0
  have xbig : 1≤(x:ℝ) := by exact_mod_cast pos
  nlinarith only [sum_price,target,eq,sr,
    mul_nonneg (show 0≤(m:ℝ)+1 by positivity) (mul_nonneg xr.le (sub_nonneg.mpr xbig)),
    sq_nonneg (x:ℝ)]


private theorem integer_price {s : ℝ} (unit : |s|=1)
    (tests : ∀ j m : ℕ, m≤16^j → s*score j m≤(board j:ℝ)^2)
    {b : ℝ} (bh : 1/2<b) :
    ∃ C : ℝ, 0≤C ∧ ∀ N : ℕ, 0<N → s*error N≤(C*(N:ℝ)^b)*N := by
  obtain ⟨D,dn,rootPrice⟩:=ShapeStrip.root_price b bh
  obtain ⟨A,reps⟩:=Chebyshev.psi_sub_theta_le_mul_sqrt
  let q:ℝ:=(16:ℝ)^b
  have qp : 0<q := Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨28*D*q+max 0 A,by positivity,?_⟩
  intro N np
  let j:=Nat.log 16 N+1
  have Nr : 0<(N:ℝ) := by exact_mod_cast np
  have one : 1≤(N:ℝ) := by exact_mod_cast np
  have cover : N≤16^j := (Nat.lt_pow_succ_log_self (by decide) N).le
  have near : 16^j≤16*N := by
    dsimp [j];rw [pow_succ,mul_comm];exact Nat.mul_le_mul_left 16 (Nat.pow_log_le_self 16 np.ne')
  have grow : q^j≤q*(N:ℝ)^b := by
    dsimp [q];rw [Real.rpow_pow_comm (by norm_num),←Real.mul_rpow (by norm_num) Nr.le]
    exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast near) (by linarith only [bh])
  have rootCost : (root j:ℝ)≤4*D*q*(N:ℝ)^b := by
    have paid:= (rootPrice j).trans (mul_le_mul_of_nonneg_left grow dn)
    unfold root;push_cast;rw [pow_succ (4:ℝ) j]
    change _≤D*(q*(N:ℝ)^b) at paid
    nlinarith only [paid]
  have small:=short_area unit (tests j) (m:=N-1) ((Nat.sub_le _ _).trans cover)
  have succ : N-1+1=N := by omega
  rw [succ] at small
  have equal : ((N-1:ℕ):ℝ)+1=N := by exact_mod_cast succ
  rw [equal] at small
  have sq : Real.sqrt (N:ℝ)≤(N:ℝ)^b := by
    rw [Real.sqrt_eq_rpow];exact Real.rpow_le_rpow_of_exponent_le one bh.le
  obtain ⟨lo,hi⟩:=PrimeBoard.repeated N
  have price : s*(fullWalk N-primeWalk N)≤(max 0 A)*(N:ℝ)^b*N := by
    have f : s*(fullWalk N-primeWalk N)≤fullWalk N-primeWalk N := by
      apply le_trans (le_abs_self _);rw [abs_mul,unit,one_mul,abs_of_nonneg lo]
    have pp:=mul_le_mul_of_nonneg_left (reps (N:ℝ)) Nr.le
    have order:=mul_le_mul (le_max_right 0 A) sq (Real.sqrt_nonneg _) (le_max_left _ _)
    nlinarith only [f,hi,pp,mul_le_mul_of_nonneg_left order Nr.le]
  unfold error
  nlinarith only [small,price,mul_le_mul_of_nonneg_right rootCost Nr.le]

theorem value_integer {N : ℕ} (np : 0<N) : PrimeDivisorPrimitive.value N=error N/(N:ℝ) := by
  have nr : 0<(N:ℝ) := by exact_mod_cast np
  have q : (∑ d ∈ Icc 1 N, ArithmeticFunction.vonMangoldt d*(1-(d:ℝ)/N))=fullWalk N/(N:ℝ) := by
    rw [fullWalk,Finset.sum_div];apply sum_congr rfl;intro d _;field_simp
  rw [PrimeDivisorPrimitive.value,if_pos (by exact_mod_cast np),Nat.floor_natCast,q,error]
  field_simp

theorem signal_mono {t u : ℝ} (large : 1≤t) (tu : t≤u) :
    PrimeDivisorPrimitive.value t+t/2≤PrimeDivisorPrimitive.value u+u/2 := by
  have tp:=zero_lt_one.trans_le large
  have up:=tp.trans_le tu
  simp only [PrimeDivisorPrimitive.value,if_pos large,if_pos (large.trans tu),sub_add_cancel]
  calc
    _ ≤ ∑ d ∈ Icc 1 ⌊t⌋₊, ArithmeticFunction.vonMangoldt d*(1-(d:ℝ)/u) := by
      apply sum_le_sum;intro d _
      exact mul_le_mul_of_nonneg_left (sub_le_sub_left (div_le_div_of_nonneg_left (Nat.cast_nonneg _) tp tu) _) ArithmeticFunction.vonMangoldt_nonneg
    _ ≤ _ := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro a ha;exact mem_Icc.mpr ⟨(mem_Icc.mp ha).1,(mem_Icc.mp ha).2.trans (Nat.floor_mono tu)⟩
      · intro a ha _
        have yes:=(Nat.le_floor_iff up.le).mp (mem_Icc.mp ha).2
        exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (sub_nonneg.mpr ((div_le_one up).mpr yes))

/-- Either orientation of the physical prefix test alone reaches the stock RH statement. -/
theorem one_orientation (s : ℝ) (choice : s=1 ∨ s= -1)
    (tests : ∀ j m : ℕ, m≤16^j → s*score j m≤(board j:ℝ)^2) : RiemannHypothesis := by
  apply PowerRecovery.rh_of_signed_value s choice
  intro b bh _
  have unit : |s|=1 := by rcases choice with h|h <;> simp [h]
  obtain ⟨C,cn,heads⟩:=integer_price unit tests bh
  have bp : 0<b := by linarith only [bh]
  have two : 1≤(2:ℝ)^b := Real.one_le_rpow (by norm_num) bp.le
  refine ⟨C*(2:ℝ)^b+1,by positivity,?_⟩
  intro t large
  let N:=⌊t⌋₊
  have np : 0<N := Nat.floor_pos.mpr large
  have nr : 1≤(N:ℝ) := by exact_mod_cast np
  have before : (N:ℝ)≤t := Nat.floor_le (zero_le_one.trans large)
  have after : t<(N:ℝ)+1 := Nat.lt_floor_add_one _
  have atHead (k : ℕ) (kp : 0<k) : s*PrimeDivisorPrimitive.value k≤C*(k:ℝ)^b := by
    rw [value_integer kp,←mul_div_assoc]
    exact (div_le_iff₀ (by exact_mod_cast kp)).mpr (heads k kp)
  have tpay : 1≤t^b := Real.one_le_rpow large bp.le
  have high : ((N:ℝ)+1)^b≤(2:ℝ)^b*t^b := by
    rw [←Real.mul_rpow (by norm_num) (zero_le_one.trans large)]
    exact Real.rpow_le_rpow (by positivity) (by linarith) bp.le
  rcases choice with positive|negative
  · have hi:=atHead (N+1) (Nat.succ_pos _)
    have monotone:=signal_mono large after.le
    rw [positive,one_mul] at hi ⊢
    push_cast at hi
    nlinarith only [hi,monotone,before,tpay,mul_le_mul_of_nonneg_left high cn]
  · have lo:=atHead N np
    have monotone:=signal_mono nr before
    have low : (N:ℝ)^b≤(2:ℝ)^b*t^b :=
      (Real.rpow_le_rpow (Nat.cast_nonneg _) before bp.le).trans
        (le_mul_of_one_le_left (Real.rpow_nonneg (zero_le_one.trans large) _) two)
    rw [negative,neg_one_mul] at lo ⊢
    nlinarith only [lo,monotone,after,tpay,mul_le_mul_of_nonneg_left low cn]

def surplus (j m : ℕ) := (prefixJobs (board j) m+smallReturn (board j) m)-
  (root j*plainArea (board j) m)
def shortage (j m : ℕ) := (root j*plainArea (board j) m)-
  (prefixJobs (board j) m+smallReturn (board j) m)

/-- The fixed pocket pays only for excess arrivals. -/
theorem rh_of_upper_pocket (budget : ∀ j m : ℕ, m≤16^j → 13*surplus j m≤(board j)^2) :
    RiemannHypothesis := by
  apply one_orientation 1 (Or.inl rfl)
  intro j m mh
  have h:=budget j m mh;unfold surplus at h
  have b : prefixJobs (board j) m+smallReturn (board j) m≤root j*plainArea (board j) m+(board j)^2 := by omega
  have realB : ((prefixJobs (board j) m+smallReturn (board j) m:ℕ):ℝ)≤
      (root j:ℝ)*plainArea (board j) m+(board j:ℝ)^2 := by exact_mod_cast b
  rw [one_mul,score];linarith only [realB]

/-- Keeping just the other sign of error gives a separate one-premise implication. -/
theorem rh_of_lower_pocket (budget : ∀ j m : ℕ, m≤16^j → 13*shortage j m≤(board j)^2) :
    RiemannHypothesis := by
  apply one_orientation (-1) (Or.inr rfl)
  intro j m mh
  have h:=budget j m mh;unfold shortage at h
  have b : root j*plainArea (board j) m≤prefixJobs (board j) m+smallReturn (board j) m+(board j)^2 := by omega
  have realB : (root j:ℝ)*plainArea (board j) m≤
      ((prefixJobs (board j) m+smallReturn (board j) m:ℕ):ℝ)+(board j:ℝ)^2 := by exact_mod_cast b
  rw [neg_one_mul,score];linarith only [realB]


def arrival (n d : ℕ) := (n-d)*tickAt n d
def released (n m : ℕ) := n^2/13+
  ∑ d ∈ Icc 1 m, if n.sqrt<d then n.sqrt*(n-d) else 0

def timely (j : ℕ) : Prop :=
  let n:=board j
  ∃ put : ℕ → ℕ → ℕ, (∀ p≤16^j, ∀ t<arrival n p, put p t<released n p) ∧
    (∀ p≤16^j, ∀ q≤16^j, ∀ t<arrival n p, ∀ u<arrival n q,
      put p t=put q u → p=q ∧ t=u)

private theorem arrival_sum (n m : ℕ) : ∑ d ∈ range (m+1),arrival n d=prefixJobs n m := by
  induction m with
  | zero => simp [arrival,prefixJobs,tickAt]
  | succ m ih =>
    rw [sum_range_succ,ih]
    unfold prefixJobs;rw [sum_Icc_succ_top (by omega : 1≤m+1)];rfl

private theorem released_mono (n : ℕ) : Monotone (released n) := by
  apply monotone_nat_of_le_succ
  intro m;unfold released;rw [sum_Icc_succ_top (by omega : 1≤m+1)];omega

theorem allocation_split (n m : ℕ) : released n m+smallReturn n m=n^2/13+n.sqrt*plainArea n m := by
  have e : (Icc 1 m).filter (fun d => d≤n.sqrt)=Icc 1 (min m n.sqrt) := by
    ext d;simp only [mem_Icc,mem_filter,le_min_iff];tauto
  unfold released smallReturn plainArea
  rw [Finset.mul_sum,←e,Finset.sum_filter,Finset.mul_sum,Nat.add_assoc,←sum_add_distrib]
  congr 1
  apply sum_congr rfl
  intro d _
  by_cases h : n.sqrt<d <;> simp [h,show d≤n.sqrt↔¬n.sqrt<d by omega]

theorem timely_iff (j : ℕ) : timely j ↔ ∀ m≤16^j, 13*surplus j m≤(board j)^2 := by
  let n:=board j
  let N:ℕ:=16^j+1
  have nx : n.sqrt=root j := Nat.sqrt_eq' _
  have kr:=ReturnedTaper.prefix_placement N (arrival n) (released n) (released_mono n)
  have shape (m : ℕ) :
      (∑ i ∈ range (m+1),arrival n i)≤released n m ↔ 13*surplus j m≤n^2 := by
    rw [arrival_sum]
    have counted:=allocation_split n m
    rw [nx] at counted
    unfold surplus
    change prefixJobs n m≤released n m ↔ 13*((prefixJobs n m+smallReturn n m)-root j*plainArea n m)≤n^2
    omega
  change (∃ put : ℕ → ℕ → ℕ, (∀ p≤16^j, ∀ t<arrival n p, put p t<released n p) ∧
    (∀ p≤16^j, ∀ q≤16^j, ∀ t<arrival n p, ∀ u<arrival n q, put p t=put q u → p=q ∧ t=u)) ↔ _
  simp only [N,Nat.lt_succ_iff] at kr
  rw [←kr];exact forall_congr' (fun m => forall_congr' (fun _ => shape m))

/-- This form takes actual placements of the arriving records as its sole hypothesis. -/
theorem rh_of_shared_placement (maps : ∀ j : ℕ, timely j) : RiemannHypothesis :=
  rh_of_upper_pocket (fun j => (timely_iff j).mp (maps j))

#print axioms PALRH.SignedStrip.timely_iff
#print axioms PALRH.SignedStrip.rh_of_shared_placement

#print axioms PALRH.SignedStrip.rh_of_upper_pocket
#print axioms PALRH.SignedStrip.rh_of_lower_pocket

#print axioms PALRH.SignedStrip.short_area
end PALRH.SignedStrip
