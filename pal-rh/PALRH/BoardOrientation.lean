import PALRH.ProductBridge

open Finset Set
open scoped BigOperators

noncomputable section
namespace PALRH.BoardOrientation
open ShapeObservation ReturnedHorizon LogPrimitive PrimeDivisorPrimitive PositivePrimitive

private theorem within_board :
    ∃ A : ℝ, 0≤A ∧ ∀ j : ℕ, ∀ s : ℝ, s=1 ∨ s= -1 →
      (∀ m≤16^j, s*SignedStrip.score j m≤(board j:ℝ)^2) →
      ∀ t : ℝ, 1≤t → t≤(16:ℝ)^j → s*value t≤A*(root j:ℝ) := by
  obtain ⟨C,reps⟩:=Chebyshev.psi_sub_theta_le_mul_sqrt
  let D:=max 0 C
  have dn : 0≤D := le_max_left _ _
  refine ⟨8+D,by positivity,?_⟩
  intro j s choice samples t one within
  let x:=root j
  have xp : 0<x := by dsimp [x,root];positivity
  have xr : 1≤(x:ℝ) := by exact_mod_cast xp
  have mag : |s|=1 := by rcases choice with h|h <;> simp [h]
  have bound (k : ℕ) (kp : 0<k) (seen : k≤16^j+1) : s*value k≤(7+D)*x := by
    have kr : 0<(k:ℝ) := by exact_mod_cast kp
    have index : k-1≤16^j := by omega
    have used:=SignedStrip.short_area mag samples index
    have eqK : k-1+1=k := by omega
    rw [eqK,show ((k-1:ℕ):ℝ)+1=k by exact_mod_cast eqK] at used
    have small : Real.sqrt (k:ℝ)≤x := by
      apply Real.sqrt_le_iff.mpr
      refine ⟨by positivity,?_⟩
      have cover:=covers j
      have big : 1≤(16:ℕ)^j := Nat.pow_pos (by decide)
      exact_mod_cast (by change k≤board j;omega : k≤x^2)
    obtain ⟨lo,hi⟩:=PrimeBoard.repeated k
    have oriented : s*(LinearPrimeIntegral.fullWalk k-LinearPrimeIntegral.primeWalk k)≤
        (k:ℝ)*D*x := by
      have first : s*(LinearPrimeIntegral.fullWalk k-LinearPrimeIntegral.primeWalk k)≤
          LinearPrimeIntegral.fullWalk k-LinearPrimeIntegral.primeWalk k := by
        apply (le_abs_self _).trans;rw [abs_mul,mag,one_mul,abs_of_nonneg lo]
      have up:=mul_le_mul_of_nonneg_left (reps (k:ℝ)) kr.le
      have tiny:=mul_le_mul (le_max_right 0 C) small (Real.sqrt_nonneg _) dn
      nlinarith only [first,hi,up,mul_le_mul_of_nonneg_left tiny kr.le]
    rw [SignedStrip.value_integer kp,←mul_div_assoc]
    apply (div_le_iff₀ kr).mpr
    unfold QuarticBoards.error
    nlinarith only [used,oriented]
  let k:=⌊t⌋₊
  have kp : 0<k := Nat.floor_pos.mpr one
  have kr : 1≤(k:ℝ) := by exact_mod_cast kp
  have low : (k:ℝ)≤t := Nat.floor_le (zero_le_one.trans one)
  have hi : t<(k:ℝ)+1 := Nat.lt_floor_add_one _
  have ke : k≤16^j := by exact_mod_cast low.trans within
  rcases choice with plus|minus
  · have est:=bound (k+1) (Nat.succ_pos _) (by omega)
    have mon:=SignedStrip.signal_mono one hi.le
    rw [plus,one_mul] at est ⊢
    push_cast at est
    change value t≤(8+D)*(x:ℝ)
    nlinarith only [est,mon,low,xr]
  · have est:=bound k kp (by omega)
    have mon:=SignedStrip.signal_mono kr low
    rw [minus,neg_one_mul] at est ⊢
    change -value t≤(8+D)*(x:ℝ)
    nlinarith only [est,mon,hi,xr]

private theorem primitive_on_board (j : ℕ) (s : ℝ) (choice : s=1 ∨ s= -1) {A : ℝ}
    (an : 0≤A) (valueBound : ∀ t : ℝ, 1≤t → t≤(16:ℝ)^j → s*value t≤A*(root j:ℝ))
    {b : ℝ} (bp : 0<b) {y : ℝ} (yp : 0≤y) (inside : y≤(16:ℝ)^j) :
    |primitive y|≤(((A/b+24)/(1-(1/2:ℝ)^b))*(root j:ℝ))*y^b := by
  let X:ℝ:=root j
  let T:ℝ:=(16:ℝ)^j
  let w:=fun t : ℝ => t^b
  let f:=fun t : ℝ => s*primitive t
  let q:ℝ:=(1/2:ℝ)^b
  have xr : 0≤X := Nat.cast_nonneg _
  have qn : 0≤q := Real.rpow_nonneg (by norm_num) _
  have ql : q<1 := Real.rpow_lt_one (by norm_num) (by norm_num) bp
  have wn (t : ℝ) (tn : 0≤t) : 0≤w t := Real.rpow_nonneg tn _
  have mon : MonotoneOn w (Ici 0) := fun _ ha _ _ ab => Real.rpow_le_rpow ha ab bp.le
  have half (t : ℝ) (one : 1≤t) : w (t/2)≤q*w t := by
    dsimp [w,q]
    rw [show t/2=(1/2)*t by ring,Real.mul_rpow (by norm_num) (zero_le_one.trans one)]
  have inc (t v : ℝ) (vn : 0≤v) (vt : v≤t) (tt : t≤T) :
      f t-f v≤(A*X/b)*(w t-w v) := by
    apply PowerRecovery.local_increment bp (mul_nonneg an xr) (T:=T) _ vn vt tt
    intro u one within
    exact (valueBound u one within).trans (le_mul_of_one_le_right (mul_nonneg an xr) (Real.one_le_rpow one bp.le))
  have early (t : ℝ) (tn : 0≤t) (tiny : t<1) : f t=0 := by
    dsimp [f];rw [PrimitiveRecovery.primitive_early tn tiny,mul_zero]
  have reading (t : ℝ) (one : 1≤t) (tt : t≤T) : ∃ N : ℕ, 0<N ∧ -(24*X*w t)≤alternating f N t := by
    let N:=⌊t⌋₊+1
    refine ⟨N,Nat.succ_pos _,?_⟩
    have enough : ⌊t⌋₊≤2*N := by dsimp [N];omega
    have tn:=zero_le_one.trans one
    have sq : Real.sqrt t≤X := by
      apply Real.sqrt_le_iff.mpr;refine ⟨xr,tt.trans ?_⟩
      have g:=covers j
      have h : 16^j≤board j := by omega
      dsimp [T,X];exact_mod_cast h
    have s1 : 1≤w t := Real.one_le_rpow one bp.le
    have valid : Real.sqrt t≤X*w t := sq.trans (le_mul_of_one_le_right xr s1)
    have eq : alternating f N t=s*alternating primitive N t := by
      unfold alternating f;rw [mul_sum];apply sum_congr rfl;intro _ _;ring
    rw [eq]
    rcases choice with plus|minus
    · rw [plus,one_mul];linarith only [PrimitiveRecovery.observed_primitive tn enough,valid]
    · rw [minus,neg_one_mul];linarith only [PrimitiveRecovery.observed_primitive_upper tn enough,valid]
  have cost:=PowerRecovery.local_scale (div_nonneg (mul_nonneg an xr) bp.le) (mul_nonneg (by norm_num : 0≤(24:ℝ)) xr)
    qn ql wn mon (Real.zero_rpow bp.ne') half early inc reading yp inside
  dsimp [f,w,q] at cost
  have mag : |s|=1 := by rcases choice with h|h <;> simp [h]
  rw [abs_mul,mag,one_mul] at cost
  convert cost using 1;dsimp [X];ring


/-- The whole observed prefix of each board may choose its own sign. The proof recovers
both signs of the *same* primitive before leaving that board. -/
theorem choose_by_board (tests : ∀ j : ℕ, ∃ s : ℝ, (s=1 ∨ s= -1) ∧
    ∀ m≤16^j, s*SignedStrip.score j m≤(board j:ℝ)^2) : RiemannHypothesis := by
  obtain ⟨A,an,arithmetic⟩:=within_board
  apply PrimitiveMellin.rh_of_primitive_powers
  intro b bh _
  let d:ℝ:=(b-1/2)/2
  let c:ℝ:=1/2+d
  have dp : 0<d := by dsimp [d];linarith only [bh]
  have ch : 1/2<c := by dsimp [c];linarith only [dp]
  have cp : 0<c := by linarith only [ch]
  have bc : c+d=b := by dsimp [c,d];ring
  let K:ℝ:=(A/d+24)/(1-(1/2:ℝ)^d)
  have small : (1/2:ℝ)^d<1 := Real.rpow_lt_one (by norm_num) (by norm_num) dp
  have kn : 0≤K := by dsimp [K];positivity
  obtain ⟨D,dn,weight⟩:=ShapeStrip.root_price c ch
  refine ⟨K*(4*D*(32:ℝ)^c),by positivity,?_⟩
  intro t ht
  let y:=1/t
  have one : 1≤y := (one_le_div ht.1).mpr ht.2
  have yp:=zero_lt_one.trans_le one
  let N:=⌊y⌋₊+1
  have np : 0<N := Nat.succ_pos _
  let j:=Nat.log 16 N+1
  have cover : N≤16^j := (Nat.lt_pow_succ_log_self (by decide) N).le
  have near : 16^j≤16*N := by
    dsimp [j];rw [pow_succ,mul_comm];exact Nat.mul_le_mul_left 16 (Nat.pow_log_le_self 16 np.ne')
  have lower : y≤(N:ℝ) := by simpa [N] using (Nat.lt_floor_add_one y).le
  have upper : (N:ℝ)≤2*y := by dsimp [N];push_cast;linarith only [Nat.floor_le yp.le,one]
  have br : y≤(16:ℝ)^j := lower.trans (by exact_mod_cast cover)
  have limit : (16:ℝ)^j≤32*y := by
    have q : (16:ℝ)^j≤16*(N:ℝ) := by exact_mod_cast near
    linarith only [q,upper]
  have grow : ((16:ℝ)^c)^j≤(32:ℝ)^c*y^c := by
    rw [Real.rpow_pow_comm (by norm_num),←Real.mul_rpow (by norm_num) yp.le]
    exact Real.rpow_le_rpow (by positivity) limit cp.le
  have size : (root j:ℝ)≤(4*D*(32:ℝ)^c)*y^c := by
    have lim:= (weight j).trans (mul_le_mul_of_nonneg_left grow dn)
    unfold root;push_cast;rw [pow_succ (4:ℝ) j];nlinarith only [lim]
  obtain ⟨s,orientation,obs⟩:=tests j
  have localPay:=primitive_on_board j s orientation an (arithmetic j s orientation obs) dp yp.le br
  rw [OneSidedBoard.reciprocal_read ht,Complex.norm_real,Real.norm_eq_abs]
  have realPrice : |primitive y|≤K*(4*D*(32:ℝ)^c)*y^b := by
    calc
      _ ≤ (K*(root j:ℝ))*y^d := localPay
      _ ≤ (K*((4*D*(32:ℝ)^c)*y^c))*y^d :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left size kn) (Real.rpow_nonneg yp.le _)
      _ = (K*(4*D*(32:ℝ)^c))*(y^c*y^d) := by ring
      _ = _ := by rw [←Real.rpow_add yp c d,bc]
  simpa only [y,one_div,Real.inv_rpow ht.1.le,Real.rpow_neg ht.1.le] using realPrice

theorem rh_of_product_direction (direction : ∀ j : ℕ,
    (∀ m≤16^j, ProductBridge.upper j m) ∨ (∀ m≤16^j, ProductBridge.lower j m)) :
    RiemannHypothesis := by
  apply choose_by_board
  intro j
  rcases direction j with plus|minus
  · refine ⟨1,Or.inl rfl,?_⟩
    intro m mh
    have h:=ProductBridge.upper_score plus mh
    nlinarith only [h,sq_nonneg ((board j):ℝ)]
  · refine ⟨-1,Or.inr rfl,?_⟩
    intro m mh
    have h:=ProductBridge.lower_score minus mh
    nlinarith only [h,sq_nonneg ((board j):ℝ)]

#print axioms PALRH.BoardOrientation.choose_by_board
#print axioms PALRH.BoardOrientation.rh_of_product_direction

end PALRH.BoardOrientation
