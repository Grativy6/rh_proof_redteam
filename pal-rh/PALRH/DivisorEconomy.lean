import PALRH.DivisorBracket
import Mathlib.Analysis.Complex.ExponentialBounds

open Finset
open scoped BigOperators
noncomputable section
namespace PALRH.DivisorEconomy
open DivisorBracket LinearPrimeIntegral

def height (n m : ℕ) : ℝ := (n-m:ℕ)
def signal (n m : ℕ) : ℝ := height n m * Real.log m
def grid (n j : ℕ) : ℝ := (j:ℝ)*∑ m ∈ Icc 1 (n/j), height n (j*m)*Real.log m
def price (c : ℕ → ℤ) (n : ℕ) : ℝ := ∑ j ∈ slots, (c j:ℝ)*grid n j
def coefficient (c : ℕ → ℤ) : ℝ := ∑ j ∈ slots, (c j:ℝ)*Real.log j

private theorem sampling (f : ℕ → ℝ) (j n : ℕ) :
    (∑ m ∈ Icc 1 (n/j), f (j*m)) =
    (∑ v ∈ Icc 1 n, (v/j:ℕ)*(f v-f (v+1))) + (n/j:ℕ)*f (n+1) := by
  induction n with
  | zero => simp
  | succ n old =>
    rw [sum_Icc_succ_top (by omega : 1 ≤ n+1)]
    by_cases dv : j ∣ n+1
    · have next := Nat.succ_div_of_dvd dv
      have eq := Nat.mul_div_cancel' dv
      rw [next] at eq ⊢
      rw [sum_Icc_succ_top (Nat.succ_le_succ (Nat.zero_le (n/j))),eq,old]
      simp only [Nat.cast_succ]
      ring
    · rw [Nat.succ_div_of_not_dvd dv,old]
      ring

private theorem grid_difference (f : ℕ → ℝ) {n j : ℕ} (ends : f (n+1)=0) :
    (j:ℝ)*(∑ m ∈ Icc 1 (n/j), f (j*m)) - ∑ v ∈ Icc 1 n,f v =
      ∑ v ∈ Icc 1 n, -(v%j:ℕ)*(f v-f (v+1)) := by
  have part := sampling f j n
  have unit := sampling f 1 n
  simp only [Nat.div_one,one_mul,ends,mul_zero,add_zero] at unit
  rw [part,ends,mul_zero,add_zero,unit,mul_sum,←sum_sub_distrib]
  apply sum_congr rfl
  intro v _
  have div : ((v%j:ℕ):ℝ)+(j:ℝ)*(v/j:ℕ)=v := by exact_mod_cast Nat.mod_add_div v j
  linear_combination (f v-f (v+1))*div

private theorem log_telescope (n : ℕ) :
    (∑ m ∈ Icc 1 n, (Real.log ((m:ℝ)+1)-Real.log m))=Real.log ((n:ℝ)+1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_Icc_succ_top (by omega : 1≤n+1),ih]; push_cast; ring

private theorem variation {n m : ℕ} (mp : 0<m) (mn : m≤n) :
    |signal n m-signal n (m+1)| ≤
      (n:ℝ)*(Real.log ((m:ℝ)+1)-Real.log m)+Real.log ((n:ℝ)+1) := by
  have mr : 0<(m:ℝ) := by exact_mod_cast mp
  have lt1 : 0 ≤ Real.log (m:ℝ) := Real.log_nonneg (by exact_mod_cast mp)
  have lt2 := Real.log_le_log mr (show (m:ℝ)≤(n:ℝ)+1 by exact_mod_cast (show m≤n+1 by omega))
  have inc : 0 ≤ Real.log ((m:ℝ)+1)-Real.log m :=
    sub_nonneg.mpr (Real.log_le_log mr (by linarith))
  have hd := Nat.sub_le_sub_left (Nat.le_succ m) n
  have cost : 0 ≤ height n m - height n (m+1) := sub_nonneg.mpr (by unfold height; exact_mod_cast hd)
  have one : height n m - height n (m+1) ≤ 1 := by
    unfold height
    exact sub_le_iff_le_add.mpr (by exact_mod_cast (show n-m≤1+(n-(m+1)) by omega))
  have high : height n (m+1) ≤ n := by unfold height; exact_mod_cast Nat.sub_le n (m+1)
  have low : 0≤height n (m+1) := Nat.cast_nonneg _
  have up := mul_le_mul_of_nonneg_right one lt1
  have down := mul_le_mul_of_nonneg_right high inc
  have clean := mul_nonneg cost lt1
  have pos := mul_nonneg low inc
  have cap := mul_nonneg (Nat.cast_nonneg (α:=ℝ) n) inc
  unfold signal
  simp only [Nat.cast_succ]
  rw [abs_le]
  constructor <;> nlinarith only [up,down,clean,pos,cap,lt1,lt2]

private theorem sampling_error (n : ℕ) {j : ℕ} (jp : 0<j) :
    |(j:ℝ)*(∑ m ∈ Icc 1 (n/j),signal n (j*m)) - ∑ m ∈ Icc 1 n,signal n m| ≤
      2*j*n*Real.log ((n:ℝ)+1) := by
  rw [grid_difference (signal n) (by simp [signal,height])]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ m ∈ Icc 1 n,(j:ℝ)*((n:ℝ)*(Real.log ((m:ℝ)+1)-Real.log m)+Real.log ((n:ℝ)+1)) := by
      apply sum_le_sum
      intro m hm
      rw [abs_mul,abs_neg,abs_of_nonneg (Nat.cast_nonneg _)]
      exact mul_le_mul (by exact_mod_cast (Nat.mod_lt m jp).le)
        (variation (mem_Icc.mp hm).1 (mem_Icc.mp hm).2) (abs_nonneg _) (Nat.cast_nonneg _)
    _ = _ := by
      rw [←mul_sum,sum_add_distrib,←mul_sum,log_telescope]
      simp [Nat.card_Icc]
      ring

private theorem mass_exact (n j : ℕ) :
    2*(j:ℝ)*(∑ m ∈ Icc 1 (n/j),height n (j*m)) =
       (n:ℝ)^2-(j:ℝ)*n+(n%j:ℕ)*((j:ℝ)-(n%j:ℕ)) := by
  by_cases jz : j=0
  · subst j; simp; ring
  have jp := Nat.pos_of_ne_zero jz
  have elem (m : ℕ) (hm : m ∈ Icc 1 (n/j)) : height n (j*m)=(n:ℝ)-j*m := by
    have prod := (Nat.le_div_iff_mul_le jp).mp (mem_Icc.mp hm).2
    unfold height
    rw [Nat.cast_sub (by simpa [Nat.mul_comm] using prod),Nat.cast_mul]
  have recSum (L : ℕ) :
      2*(∑ m ∈ Icc 1 L, ((n:ℝ)-(j:ℝ)*m))=2*n*L-(j:ℝ)*L*(L+1) := by
    induction L with
    | zero => simp
    | succ k ih =>
      rw [sum_Icc_succ_top (by omega : 1≤k+1),mul_add,ih]; push_cast; ring
  rw [sum_congr rfl elem, mul_assoc]
  have total := recSum (n/j)
  have split : ((n%j:ℕ):ℝ)+(j:ℝ)*(n/j:ℕ)=n := by exact_mod_cast Nat.mod_add_div n j
  rw [show ((n%j:ℕ):ℝ)=(n:ℝ)-j*(n/j:ℕ) from eq_sub_of_add_eq split]
  linear_combination (j:ℝ)*total

private theorem grid_bound (n : ℕ) {j : ℕ} (hp : 0<j) (small : j≤n+1) :
    |grid n j - ∑ m ∈ Icc 1 n, signal n m + Real.log j*(n:ℝ)^2/2| ≤
      3*j*n*Real.log ((n:ℝ)+1) := by
  have pos : 0 < (j:ℝ) := by exact_mod_cast hp
  have ln0 : 0 ≤ Real.log (j:ℝ) := Real.log_nonneg (by exact_mod_cast hp)
  have ln1 := Real.log_le_log pos (by exact_mod_cast small : (j:ℝ) ≤ (n:ℝ)+1)
  have rn : 0 ≤ ((n%j:ℕ):ℝ) := Nat.cast_nonneg _
  have rj : ((n%j:ℕ):ℝ) ≤ j := by exact_mod_cast (Nat.mod_lt n hp).le
  have rm : ((n%j:ℕ):ℝ) ≤ n := by exact_mod_cast Nat.mod_le n j
  have smallpart := mul_le_mul rm (sub_le_self (j:ℝ) rn) (sub_nonneg.mpr rj) (Nat.cast_nonneg n)
  have mt := mass_exact n j
  have F : 0 ≤ (n:ℝ)^2/2 - j*(∑ m ∈ Icc 1 (n/j), height n (j*m)) := by nlinarith only [mt,smallpart]
  have G : (n:ℝ)^2/2-j*(∑ m ∈ Icc 1 (n/j),height n (j*m)) ≤ (j:ℝ)*n := by
    nlinarith only [mt,mul_nonneg rn (sub_nonneg.mpr rj),mul_nonneg pos.le (Nat.cast_nonneg n)]
  have price := mul_le_mul G ln1 ln0 (mul_nonneg pos.le (Nat.cast_nonneg n))
  have identity : (j:ℝ)*(∑ m ∈ Icc 1 (n/j),signal n (j*m)) =
      grid n j + (Real.log j)*((j:ℝ)*∑ m ∈ Icc 1 (n/j), height n (j*m)) := by
    unfold grid signal
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply sum_congr rfl
    intro m hm
    have mp : (0:ℝ)<m := by exact_mod_cast (mem_Icc.mp hm).1
    rw [Nat.cast_mul,Real.log_mul pos.ne' mp.ne']
    ring
  have fromGrid:=sampling_error n hp
  rw [identity, abs_le] at fromGrid
  rw [abs_le]
  constructor <;> nlinarith only [fromGrid.1,fromGrid.2,price,mul_nonneg ln0 F,
    mul_nonneg (mul_nonneg pos.le (Nat.cast_nonneg (α:=ℝ) n)) (ln0.trans ln1)]

def priceError (c : ℕ → ℤ) : ℝ := ∑ j ∈ slots, 3*j*|(c j:ℝ)|

theorem mixture_price (c : ℕ → ℤ) (zero : (∑ j ∈ slots,c j)=0) {n : ℕ} (large : 16≤n) :
    |price c n + coefficient c * (n:ℝ)^2/2| ≤ priceError c * n * Real.log ((n:ℝ)+1) := by
  have zeroR : (∑ j ∈ slots,(c j:ℝ))=0 := by exact_mod_cast zero
  let S:=∑ m ∈ Icc 1 n,signal n m
  have together : price c n + coefficient c*(n:ℝ)^2/2 =
    ∑ j ∈ slots,(c j:ℝ)*(grid n j-S+Real.log j*(n:ℝ)^2/2) := by
    have per (j : ℕ) : (c j:ℝ)*(grid n j-S+Real.log j*(n:ℝ)^2/2) =
        (c j:ℝ)*grid n j-(c j:ℝ)*S+((c j:ℝ)*Real.log j)*((n:ℝ)^2/2) := by ring
    simp_rw [per]
    rw [sum_add_distrib, sum_sub_distrib, ←sum_mul, zeroR, zero_mul, sub_zero, ←sum_mul]
    unfold price coefficient
    ring
  rw [together]
  apply (abs_sum_le_sum_abs _ _).trans
  unfold priceError
  rw [sum_mul,sum_mul]
  apply sum_le_sum
  intro j hj
  rw [abs_mul]
  have h:=mul_le_mul_of_nonneg_left
    (grid_bound n (mem_Icc.mp hj).1 (by have:= (mem_Icc.mp hj).2;omega)) (abs_nonneg (c j:ℝ))
  change _ ≤ _ at h
  dsimp [S]
  convert h using 1; ring

private theorem one_grid (n j : ℕ) :
    (∑ d ∈ Icc 1 n, ArithmeticFunction.vonMangoldt d*(cell n d j:ℝ)) = grid n j := by
  let t := n/j
  have base := FactorialReturn.products t (fun d => ArithmeticFunction.vonMangoldt d)
    (fun _ => 1) (fun m => height n (j*m))
  simp only [one_mul] at base
  have src (m : ℕ) : (∑ d ∈ m.divisors, ArithmeticFunction.vonMangoldt (m/d))=Real.log m := by
    rw [Nat.sum_div_divisors m, ArithmeticFunction.vonMangoldt_sum]
  simp_rw [src] at base
  have cell_eq (d : ℕ) : (cell n d j:ℝ) =
      (j:ℝ)*∑ m ∈ Icc 1 (t/d), height n (j*(d*m)) := by
    unfold cell
    push_cast
    rw [show n/(d*j)=t/d by dsimp [t];rw [Nat.div_div_eq_div_mul,Nat.mul_comm d j]]
    congr 1
    apply sum_congr rfl
    intro m hm
    have pos : 0 < d*j := by
      by_contra! bad
      have zero : d*j=0 := by omega
      have no : t/d=0 := by dsimp [t];rw [Nat.div_div_eq_div_mul,Nat.mul_comm j d,zero,Nat.div_zero]
      rw [no] at hm
      simp at hm
    have cap : j*(d*m) ≤ n := by
      have h := (mem_Icc.mp hm).2
      dsimp [t] at h
      rw [Nat.div_div_eq_div_mul,Nat.mul_comm j d] at h
      have g := (Nat.le_div_iff_mul_le pos).mp h
      simpa [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using g
    unfold height
    rw [Nat.cast_sub cap]
    push_cast
    ring
  simp_rw [cell_eq]
  calc
    _ = (j:ℝ)* ∑ d ∈ Icc 1 n, ArithmeticFunction.vonMangoldt d *
                      ∑ m ∈ Icc 1 (t/d), height n (j*(d*m)) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro d _
      ring
    _ = (j:ℝ)* ∑ d ∈ Icc 1 t, ArithmeticFunction.vonMangoldt d *
                      ∑ m ∈ Icc 1 (t/d), height n (j*(d*m)) := by
      congr 1
      symm
      apply sum_subset (fun d hd => mem_Icc.mpr ⟨(mem_Icc.mp hd).1,(mem_Icc.mp hd).2.trans (Nat.div_le_self _ _)⟩)
      intro d hd out
      have late : t<d := by
        by_contra! h
        exact out (mem_Icc.mpr ⟨(mem_Icc.mp hd).1,h⟩)
      simp [Nat.div_eq_of_lt late]
    _ = grid n j := by
      rw [base]
      unfold grid
      congr 1
      apply sum_congr rfl
      intro m _
      ring

/-- A signed relation on the ordinary multiple addresses encloses the full
prime-power area after attaching its genuine prime-power weights. -/
theorem transfer (c : ℕ → ℤ) (s : ℤ) (zero : (∑ j ∈ slots,c j)=0)
    (addresses : ∀ k : ℕ, 0<k → 2*s*((k:ℤ)-1) ≤ reading c k) (n : ℕ) :
    (s:ℝ)*fullWalk n ≤ price c n := by
  unfold fullWalk price
  rw [mul_sum]
  calc
    _ ≤ ∑ d ∈ Icc 1 n, ∑ j ∈ slots, (c j:ℝ)*(ArithmeticFunction.vonMangoldt d*(cell n d j:ℝ)) := by
      apply sum_le_sum
      intro d hd
      have h := enclose_label c s zero addresses (mem_Icc.mp hd).1 (mem_Icc.mp hd).2
      have r : (s:ℝ)*((n:ℝ)-d) ≤ ∑ j ∈ slots,(c j:ℝ)*(cell n d j:ℝ) := by exact_mod_cast h
      have bound := mul_le_mul_of_nonneg_left r (ArithmeticFunction.vonMangoldt_nonneg (n:=d))
      rw [mul_sum] at bound
      calc
        _ = ArithmeticFunction.vonMangoldt d*((s:ℝ)*((n:ℝ)-d)) := by ring
        _ ≤ _ := bound
        _ = _ := by apply sum_congr rfl; intro j _; ring
    _ = _ := by rw [sum_comm];apply sum_congr rfl;intro j _;rw [←mul_sum,one_grid]

theorem upper_all (n : ℕ) : 102*fullWalk n ≤ price upper n := by
  apply transfer upper 102 upper_data.1
  exact fun _ h => upper_address h

theorem lower_all (n : ℕ) : (-198)*fullWalk n ≤ price lower n := by
  have result := transfer lower (-198) lower_data.1 (fun k hk => by linarith only [lower_address hk]) n
  norm_num at result
  linarith only [result]

#print axioms PALRH.DivisorEconomy.upper_all
#print axioms PALRH.DivisorEconomy.lower_all
#print axioms PALRH.DivisorEconomy.mixture_price

end PALRH.DivisorEconomy
