import Mathlib.Analysis.Real.Sqrt
import PALRH.RectangleBalance
import Mathlib.Tactic

open Finset
open scoped BigOperators Classical

noncomputable section
namespace PALRH.CellRemainder

def delta (n : ℕ) : ℝ :=
  1 / (2*Real.sqrt n*(Real.sqrt n+Real.sqrt (n-1:ℕ))^2)

private theorem delta_nonneg (n : ℕ) : 0 ≤ delta n := by
  unfold delta
  positivity

@[simp] private theorem first_delta : delta 1 = 1/2 := by norm_num [delta]

private theorem next_price {n : ℕ} (np : 0<n) :
    delta (n+1) ≤ (1/4)*(1/Real.sqrt (n:ℝ) - 1/Real.sqrt ((n:ℝ)+1)) := by
  let a := Real.sqrt ((n:ℝ)+1)
  let b := Real.sqrt (n:ℝ)
  have ap : 0<a := by dsimp [a]; positivity
  have bp : 0<b := Real.sqrt_pos_of_pos (by exact_mod_cast np)
  have plus : 0<a+b := add_pos ap bp
  have ba : b≤a := Real.sqrt_le_sqrt (by linarith)
  have sq : a^2-b^2=1 := by
    dsimp [a,b]
    rw [Real.sq_sqrt (by positivity),Real.sq_sqrt (by positivity)]
    ring
  have diff : 1/b-1/a=1/(a*b*(a+b)) := by
    field_simp
    nlinarith only [sq]
  simp only [delta,Nat.cast_add,Nat.cast_one,Nat.add_sub_cancel]
  change 1/(2*a*(a+b)^2) ≤ (1/4)*(1/b-1/a)
  rw [diff]
  have den : 0 < 4*(a*b*(a+b)) := by positivity
  rw [one_div_mul_one_div]
  apply one_div_le_one_div_of_le den
  nlinarith only [mul_nonneg (mul_nonneg ap.le plus.le) (sub_nonneg.mpr ba)]

private theorem tail_price (m : ℕ) :
    (∑ r ∈ Icc 2 (m+1), delta r) ≤ (1/4)*(1-1/Real.sqrt ((m+1:ℕ):ℝ)) := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [sum_Icc_succ_top (by omega : 2≤m+1+1)]
    have cost:=next_price (by omega : 0<m+1)
    push_cast at cost ih ⊢
    linarith only [cost,ih]

theorem tail_quarter (n : ℕ) : (∑ r ∈ Icc 2 n, delta r) ≤ 1/4 := by
  cases n with
  | zero => norm_num
  | succ m =>
    have s:=tail_price m
    have h : 0≤1/Real.sqrt ((m+1:ℕ):ℝ) := by positivity
    linarith only [s,h]

/-- The incremental weights of the integer staircase acting on a running count. -/
def reading (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ r ∈ Icc 1 n, delta r*f (n/r)

/-- Recover every input within the same finite head. The inverse costs at most four. -/
theorem inverse_bound (f : ℕ → ℝ) (at_zero : f 0=0) {X : ℕ} {C : ℝ} (cn : 0≤C)
    (bill : ∀ n : ℕ, n≤X → |reading f n|≤C) : ∀ n : ℕ, n≤X → |f n|≤4*C := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro nx
    by_cases p : n=0
    · subst n
      simpa [at_zero] using (show 0≤4*C by positivity)
    have np : 0<n := Nat.pos_of_ne_zero p
    let rest := ∑ r ∈ Icc 2 n, delta r*f (n/r)
    have lim : |rest|≤C := by
      calc
        _ ≤ ∑ r ∈ Icc 2 n, |delta r*f (n/r)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ r ∈ Icc 2 n, delta r*(4*C) := by
          apply Finset.sum_le_sum
          intro r hr
          have rp : 1<r := (Finset.mem_Icc.mp hr).1
          rw [abs_mul,abs_of_nonneg (delta_nonneg r)]
          exact mul_le_mul_of_nonneg_left (ih (n/r) (Nat.div_lt_self np rp)
            ((Nat.div_le_self n r).trans nx)) (delta_nonneg r)
        _ ≤ (1/4)*(4*C) := by
          rw [←Finset.sum_mul]
          exact mul_le_mul_of_nonneg_right (tail_quarter n) (by positivity)
        _ = C := by ring
    have part : Icc 1 n = insert 1 (Icc 2 n) := by
      ext k
      simp only [mem_Icc,mem_insert]
      omega
    have split : reading f n = (1/2)*f n+rest := by
      rw [reading,part,Finset.sum_insert (by simp : 1∉Icc 2 n),first_delta,Nat.div_one]
    have a := abs_sub (reading f n) rest
    rw [split,add_sub_cancel_right,abs_mul,abs_of_pos (by norm_num : 0<(1/2:ℝ))] at a
    have b:=bill n nx
    rw [split] at b
    linarith only [a,b,lim]

def mu (d : ℕ) : ℝ := ArithmeticFunction.moebius d

private theorem unit_rectangle {N : ℕ} (np : 0<N) (w : ℕ → ℝ) :
    (∑ d ∈ Icc 1 N, ∑ r ∈ Icc 1 (N/d), mu d*w (d*r)) = w 1 := by
  have old:=RectangleBalance.collect_weights N (fun _ => 1) mu (fun k => (k:ℝ)*w k)
  have source (n : ℕ) : (∑ d ∈ n.divisors, 1*mu (n/d))=if n=1 then 1 else 0 := by
    simp only [one_mul,Nat.sum_div_divisors]
    have eq:=DFunLike.congr_fun ArithmeticFunction.moebius_mul_coe_zeta n
    rw [ArithmeticFunction.coe_mul_zeta_apply,ArithmeticFunction.one_apply] at eq
    unfold mu
    by_cases b : n=1 <;> simp only [b,if_true,if_false] at eq ⊢ <;> exact_mod_cast eq
  simp_rw [source] at old
  calc
    _ = ∑ d ∈ Icc 1 N, (mu d/(d:ℝ))* ∑ r ∈ Icc 1 (N/d),
        (1:ℝ)/r*(((d*r:ℕ):ℝ)*w (d*r)) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      have dr : (d:ℝ)≠0 := by exact_mod_cast (show 0<d from (Finset.mem_Icc.mp hd).1).ne'
      have rr : (r:ℝ)≠0 := by exact_mod_cast (show 0<r from (Finset.mem_Icc.mp hr).1).ne'
      rw [Nat.cast_mul]
      field_simp
    _ = _ := old
    _ = w 1 := by
      rw [Finset.sum_eq_single 1]
      · simp
      · intro n _ hn
        simp [hn]
      · intro h
        exact False.elim (h (Finset.mem_Icc.mpr ⟨le_rfl,np⟩))

/-- Möbius division with the within-cell falling weight collapses to one explicit number. -/
theorem falling_reading {N : ℕ} (np : 0<N) :
    (∑ d ∈ Icc 1 N, (mu d/Real.sqrt d)*∑ r ∈ Icc 1 (N/d),
      (1/Real.sqrt ((N:ℝ)/d)-1/(2*Real.sqrt r))) = 1/Real.sqrt N-1/2 := by
  let w := fun k : ℕ => 1/Real.sqrt N-1/(2*Real.sqrt k)
  have h:=unit_rectangle np w
  apply Eq.trans _ (h.trans (by simp [w]))
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  have dn : 0<(d:ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hd).1
  have rn : 0<(r:ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hr).1
  have nn : 0<(N:ℝ) := by exact_mod_cast np
  dsimp [w]
  rw [Real.sqrt_div nn.le,Nat.cast_mul,Real.sqrt_mul dn.le]
  have a:=Real.sqrt_pos_of_pos dn
  have b:=Real.sqrt_pos_of_pos rn
  have c:=Real.sqrt_pos_of_pos nn
  field_simp

def staircase (n : ℕ) : ℝ :=
  Real.sqrt n - (1/2)*∑ r ∈ Icc 1 n, 1/Real.sqrt (r:ℝ)

private theorem stair_step (n : ℕ) : staircase (n+1)-staircase n=delta (n+1) := by
  let a := Real.sqrt ((n:ℝ)+1)
  let b := Real.sqrt (n:ℝ)
  have ap : 0<a := by dsimp [a]; positivity
  have bp : 0≤b := Real.sqrt_nonneg _
  have plus := add_pos_of_pos_of_nonneg ap bp
  have diff : a-b=1/(a+b) := by
    apply (eq_div_iff plus.ne').mpr
    have x:=Real.sq_sqrt (by positivity : 0≤(n:ℝ)+1)
    have y:=Real.sq_sqrt (by positivity : 0≤(n:ℝ))
    dsimp [a,b]
    nlinarith only [x,y]
  unfold staircase delta
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n+1)]
  simp only [Nat.cast_add,Nat.cast_one,Nat.add_sub_cancel]
  have step : a-b-1/(2*a) = 1/(2*a*(a+b)^2) := by
    calc
      _ = (a-b)/(2*a*(a+b)) := by
        conv_lhs => rw [diff]
        field_simp
        ring
      _ = _ := by rw [diff]; field_simp
  change a-1/2*(_+1/a)-(b-1/2*_)=1/(2*a*(a+b)^2)
  rw [←step]
  field_simp
  ring

theorem sum_steps (n : ℕ) : (∑ r ∈ Icc 1 n, delta r)=staircase n := by
  induction n with
  | zero => simp [staircase]
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1≤n+1),ih,←stair_step]
    ring

private theorem rectangular_sum (N : ℕ) (f g : ℕ → ℝ) :
    (∑ d ∈ Icc 1 N, f d * ∑ r ∈ Icc 1 (N/d), g r) =
      ∑ r ∈ Icc 1 N, g r * ∑ d ∈ Icc 1 (N/r), f d := by
  let I := Icc 1 N
  have cut (r : ℕ) (hr : r∈I) : I.filter (fun d => d*r≤N) = Icc 1 (N/r) := by
    ext d
    have rp : 0<r := (mem_Icc.mp hr).1
    simp only [I,mem_filter,mem_Icc,←Nat.le_div_iff_mul_le rp]
    have h:=Nat.div_le_self N r
    omega
  have expand (a b : ℕ → ℝ) :
      (∑ r ∈ I, a r*∑ d ∈ Icc 1 (N/r), b d) =
        ∑ r ∈ I, ∑ d ∈ I, if d*r≤N then a r*b d else 0 := by
    apply Finset.sum_congr rfl
    intro r hr
    rw [Finset.mul_sum,←cut r hr,Finset.sum_filter]
  rw [expand f g,expand g f,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro d _
  rw [Nat.mul_comm r d,mul_comm (f d) (g r)]

def weightedMu (n : ℕ) : ℝ := ∑ d ∈ Icc 1 n, mu d / Real.sqrt d

/-- On the same integer quotients the staircase reading has a stable inverse. -/
theorem staircase_reading (N : ℕ) :
    (∑ d ∈ Icc 1 N, (mu d/Real.sqrt d)*staircase (N/d)) = reading weightedMu N := by
  simp_rw [←sum_steps]
  exact rectangular_sum N (fun d => mu d/Real.sqrt d) delta

private theorem rationalize {u v w : ℝ} (up : 0<u) (vp : 0<v) (wp : 0<w) :
    w/v-w^2/u = ((u^2-v^2*w^2)/v^2)/(u*(1+u/(v*w))) := by
  have pos : 0 < v*w+u := by positivity
  field_simp
  ring

/-- The difference at one occupied division is the original integer remainder. -/
theorem division_residue {N d : ℕ} (dp : 0<d) (active : d≤N) :
    Real.sqrt (N/d:ℕ)/Real.sqrt d-((N/d:ℕ):ℝ)/Real.sqrt N =
      (((N%d:ℕ):ℝ)/d)/(Real.sqrt N*(1+Real.sqrt ((N:ℝ)/((d:ℝ)*((N/d:ℕ):ℝ))))) := by
  have np : 0<(N:ℝ) := by exact_mod_cast dp.trans_le active
  have dr : 0<(d:ℝ) := by exact_mod_cast dp
  have qr : 0<((N/d:ℕ):ℝ) := by exact_mod_cast Nat.div_pos active dp
  have prod : (N%d:ℕ)+(d:ℕ)*(N/d)=N := Nat.mod_add_div N d
  have rem : (N:ℝ)-(d:ℝ)*((N/d:ℕ):ℝ)=((N%d:ℕ):ℝ) := by
    have e : ((N%d:ℕ):ℝ)+(d:ℝ)*((N/d:ℕ):ℝ)=N := by exact_mod_cast prod
    linarith only [e]
  have h:=rationalize (Real.sqrt_pos_of_pos np) (Real.sqrt_pos_of_pos dr) (Real.sqrt_pos_of_pos qr)
  rw [Real.sq_sqrt np.le,Real.sq_sqrt dr.le,Real.sq_sqrt qr.le,rem] at h
  rw [Real.sqrt_div np.le,Real.sqrt_mul dr.le]
  exact h

theorem residue_capacity {N d : ℕ} (dp : 0<d) (active : d≤N) :
    Real.sqrt (N/d:ℕ)/Real.sqrt d-((N/d:ℕ):ℝ)/Real.sqrt N ≤ 1/(2*Real.sqrt N) := by
  have np : 0<(N:ℝ) := by exact_mod_cast dp.trans_le active
  have dr : 0<(d:ℝ) := by exact_mod_cast dp
  have qr : 0<((N/d:ℕ):ℝ) := by exact_mod_cast Nat.div_pos active dp
  have root:=Real.sqrt_pos_of_pos np
  have frac : ((N%d:ℕ):ℝ)/d ≤ 1 := (div_le_one dr).mpr (by exact_mod_cast (Nat.mod_lt N dp).le)
  have base : 1≤(N:ℝ)/((d:ℝ)*((N/d:ℕ):ℝ)) :=
    (one_le_div (mul_pos dr qr)).mpr (by exact_mod_cast Nat.mul_div_le N d)
  have high:=Real.sqrt_le_sqrt base
  rw [Real.sqrt_one] at high
  rw [division_residue dp active]
  calc
    _ ≤ 1/(Real.sqrt N*(1+Real.sqrt ((N:ℝ)/((d:ℝ)*((N/d:ℕ):ℝ))))) :=
      div_le_div_of_nonneg_right frac (by positivity)
    _ ≤ _ := one_div_le_one_div_of_le (by positivity) (by nlinarith [mul_nonneg root.le (sub_nonneg.mpr high)])

def cell (N d : ℕ) : ℝ :=
  Real.sqrt (N/d:ℕ)/Real.sqrt d - ((N/d:ℕ):ℝ)/Real.sqrt N

/-- Difference of the two complete readings, on the original signed labels. -/
theorem difference {N : ℕ} (np : 0<N) :
    reading weightedMu N-(1/Real.sqrt N-1/2) = ∑ d ∈ Icc 1 N, mu d*cell N d := by
  rw [←staircase_reading,←falling_reading np,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  have dp : 0<d := (Finset.mem_Icc.mp hd).1
  have dr : 0<(d:ℝ) := by exact_mod_cast dp
  have nr : 0<(N:ℝ) := by exact_mod_cast np
  have cnt : (Icc 1 (N/d)).card=N/d := by simp
  have half (r : ℕ) : 1/(2*Real.sqrt (r:ℝ))=(1/2)*(1/Real.sqrt (r:ℝ)) := by ring
  simp_rw [half]
  rw [Finset.sum_sub_distrib,Finset.sum_const,cnt,nsmul_eq_mul,←Finset.mul_sum]
  unfold staircase cell
  rw [Real.sqrt_div nr.le]
  have a:=Real.sqrt_pos_of_pos dr
  have b:=Real.sqrt_pos_of_pos nr
  field_simp
  ring

/-- The late, unnormalized division-remainder sum at a square head. -/
def squareOutput (j : ℕ) : ℝ :=
  ∑ d ∈ Ioc j (j^2), mu d*((((j^2%d:ℕ):ℝ)/d) /
    (1+Real.sqrt (((j^2:ℕ):ℝ)/((d:ℝ)*((j^2/d:ℕ):ℝ)))))

theorem square_cost {j : ℕ} (jp : 0<j) :
    |reading weightedMu (j^2)-(1/(j:ℝ)-1/2)-squareOutput j/j| ≤ 1/2 := by
  let N:=j^2
  have jn : j≤N := by dsimp [N];simpa using Nat.pow_le_pow_right jp (by decide : 1≤2)
  have np : 0<N := pow_pos jp _
  have jr : 0<(j:ℝ) := by exact_mod_cast jp
  have root : Real.sqrt (N:ℝ)=j := by simp [N,Real.sqrt_sq (show 0≤(j:ℝ) by positivity)]
  have head := difference np
  rw [root] at head
  have split : Icc 1 N=Icc 1 j ∪ Ioc j N := by
    ext d
    simp only [mem_Icc,mem_union,mem_Ioc]
    omega
  have dis : Disjoint (Icc 1 j) (Ioc j N) := Finset.disjoint_left.mpr (fun _ a b =>
    (not_lt_of_ge (mem_Icc.mp a).2) (mem_Ioc.mp b).1)
  rw [split,Finset.sum_union dis] at head
  have last : (∑ d ∈ Ioc j N, mu d*cell N d)=squareOutput j/j := by
    unfold squareOutput
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro d hd
    have dp : 0<d := jp.trans (mem_Ioc.mp hd).1
    rw [cell,division_residue dp (mem_Ioc.mp hd).2,root]
    dsimp only [N]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  rw [last] at head
  change |reading weightedMu N-(1/(j:ℝ)-1/2)-squareOutput j/j| ≤ 1/2
  rw [head,add_sub_cancel_right]
  calc
    _ ≤ ∑ d ∈ Icc 1 j, |mu d*cell N d| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ Icc 1 j, 1/(2*(j:ℝ)) := by
      apply Finset.sum_le_sum
      intro d hd
      have dp : 0<d := (mem_Icc.mp hd).1
      have active:= (mem_Icc.mp hd).2.trans jn
      have pos : 0≤cell N d := by rw [cell,division_residue dp active];positivity
      have cap : cell N d ≤ 1/(2*(j:ℝ)) := by
        calc
          _ ≤ 1/(2*Real.sqrt N) := residue_capacity dp active
          _ = _ := by rw [root]
      have mark : |mu d|≤1 := by unfold mu; exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n:=d)
      rw [abs_mul,abs_of_nonneg pos]
      exact (mul_le_mul_of_nonneg_right mark pos).trans (by simpa only [one_mul] using cap)
    _ = 1/2 := by simp; field_simp

#print axioms PALRH.CellRemainder.difference
#print axioms PALRH.CellRemainder.square_cost
#print axioms PALRH.CellRemainder.division_residue
#print axioms PALRH.CellRemainder.residue_capacity
#print axioms PALRH.CellRemainder.staircase_reading
#print axioms PALRH.CellRemainder.falling_reading
#print axioms PALRH.CellRemainder.tail_quarter
#print axioms PALRH.CellRemainder.inverse_bound
end PALRH.CellRemainder
