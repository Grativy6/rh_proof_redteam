import PALRH.CubicWindow

open Finset Set
open scoped BigOperators Classical
noncomputable section
namespace PALRH.CubicQuadrature

open RectangleBalance TaperedNewton

def slope (b : ℕ → ℝ) (n : ℕ) := (n:ℝ)*(n+1)*(b n-b (n+1))/2
def cost (b : ℕ → ℝ) (n : ℕ) := slope b (n-1)-slope b n
def tick (d n : ℕ) := taper (2*(d:ℝ)/n)

private theorem by_parts (f g : ℕ → ℝ) (T : ℕ) :
    (∑ n ∈ Finset.Icc 1 T, (g (n-1)-g n)*f n)=
      g 0*f 1-g T*f (T+1)+∑ n ∈ Finset.Icc 1 T, g n*(f (n+1)-f n) := by
  induction T with
  | zero => simp
  | succ T old =>
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (f:=fun n => g n*(f (n+1)-f n)) (by omega),old]
    simp only [Nat.add_sub_cancel]
    ring

theorem tick_increment {d n : ℕ} (np : 0<n) :
    tick d (n+1)-tick d n=
      if d≤n ∧ n<2*d then 2*(d:ℝ)/((n:ℝ)*(n+1)) else 0 := by
  have nr : 0<(n:ℝ) := by exact_mod_cast np
  have zero {j : ℕ} (jp : 0<j) (small : j≤d) : tick d j=0 := by
    have dr : (j:ℝ)≤d := by exact_mod_cast small
    have h : 2≤2*(d:ℝ)/j := (le_div_iff₀ (by exact_mod_cast jp)).mpr (by linarith)
    rw [tick,taper,min_eq_right (by linarith),max_eq_left (by linarith)]
  have one {j : ℕ} (jp : 0<j) (big : 2*d≤j) : tick d j=1 := by
    have h : 2*(d:ℝ)/j≤1 := (div_le_one (by exact_mod_cast jp)).mpr (by exact_mod_cast big)
    rw [tick,taper,min_eq_left (by linarith),max_eq_right zero_le_one]
  have ramp {j : ℕ} (jp : 0<j) (left : d≤j) (right : j≤2*d) : tick d j=2-2*(d:ℝ)/j := by
    have jr : 0<(j:ℝ) := by exact_mod_cast jp
    have low : 1≤2*(d:ℝ)/j := (one_le_div jr).mpr (by exact_mod_cast right)
    have high : 2*(d:ℝ)/j≤2 := (div_le_iff₀ jr).mpr (by linarith [show (d:ℝ)≤j by exact_mod_cast left])
    rw [tick,taper,min_eq_right (by linarith),max_eq_right (by linarith)]
  by_cases left : d≤n
  · by_cases right : n<2*d
    · rw [if_pos ⟨left,right⟩,ramp (by omega) (by omega) (by omega),ramp np left right.le]
      push_cast
      field_simp
      ring
    · rw [if_neg (by omega),one (by omega) (by omega),one np (by omega)];ring
  · rw [if_neg (by omega),zero (by omega) (by omega),zero np (by omega)];ring

private theorem cut_sum (b : ℕ → ℝ) (d T : ℕ) (dp : 0<d) :
    (∑ n ∈ Finset.Icc 1 T, if d≤n ∧ n<2*d then b n-b (n+1) else 0)=
      b d-b (max d (min (T+1) (2*d))) := by
  induction T with
  | zero => simp [show 1≤d by omega,show 1≤2*d by omega]
  | succ T old =>
    rw [Finset.sum_Icc_succ_top (by omega),old]
    by_cases a : d≤T+1
    · by_cases h : T+1<2*d
      · rw [if_pos ⟨a,h⟩,min_eq_left h.le,max_eq_right a,min_eq_left (by omega),max_eq_right (by omega)]
        ring
      · rw [if_neg (by omega),min_eq_right (by omega),min_eq_right (by omega)];ring
    · rw [if_neg (by omega),min_eq_left (by omega),max_eq_left (by omega),min_eq_left (by omega),max_eq_left (by omega)]
      ring

theorem atom_read (b : ℕ → ℝ) {T d : ℕ} (dp : 0<d) (inside : d≤T)
    (stop : ∀ i : ℕ, T ≤ i → b i=0) :
    (∑ n ∈ Finset.Icc 1 T, cost b n*tick d n)=d*(b d-b (2*d)) := by
  unfold cost
  rw [by_parts]
  have last : slope b T=0 := by simp [slope,stop T le_rfl,stop (T+1) (by omega)]
  rw [last]
  simp only [slope,Nat.cast_zero,zero_mul,zero_div,sub_zero,zero_add]
  have each (n : ℕ) (hn : n∈Finset.Icc 1 T) :
      ((n:ℝ)*(n+1)*(b n-b (n+1))/2)*(tick d (n+1)-tick d n)=
      (d:ℝ)*(if d≤n ∧ n<2*d then b n-b (n+1) else 0) := by
    have np : 0<n := (Finset.mem_Icc.mp hn).1
    have nr : 0<(n:ℝ) := by exact_mod_cast np
    rw [tick_increment np]
    by_cases keep : d≤n ∧ n<2*d
    · simp only [if_pos keep]
      field_simp
    · simp [keep]
  rw [Finset.sum_congr rfl each,←Finset.mul_sum,cut_sum b d T dp]
  by_cases cap : 2*d≤T+1
  · rw [min_eq_right cap,max_eq_right (by omega)]
  · rw [min_eq_left (by omega),max_eq_right (by omega),stop (T+1) (by omega),stop (2*d) (by omega)]

/-- A source profile on a reciprocal grid measures a signed sum of the actual half-rows. -/
theorem actual_rows (b : ℕ → ℝ) {T : ℕ} (stop : ∀ i : ℕ, T ≤ i → b i=0) :
    (∑ n ∈ Finset.Icc 1 T, cost b n*edge ((n:ℝ)/2))=
      ∑ d ∈ Finset.Icc 1 T, (marks d:ℝ)*(b d-b (2*d)) := by
  let I:=Finset.Icc 1 T
  have edge_eq (n : ℕ) (hn : n∈I) :
      edge ((n:ℝ)/2)=∑ d ∈ I, (marks d:ℝ)/d*tick d n := by
    have np : 0<(n:ℝ) := by exact_mod_cast (show 0<n from (Finset.mem_Icc.mp hn).1)
    have h := edge_pad_positive (X:=(T:ℝ)/2) (by positivity : 0<(n:ℝ)/2)
      (div_le_div_of_nonneg_right (by exact_mod_cast (Finset.mem_Icc.mp hn).2 : (n:ℝ)≤T) (by norm_num))
    rw [show 2*((T:ℝ)/2)=T by ring,Nat.floor_natCast] at h
    rw [h]
    apply Finset.sum_congr rfl
    intro d _
    rw [tick,show (d:ℝ)/((n:ℝ)/2)=2*d/n by ring]
  have separate (n : ℕ) (hn : n∈I) : cost b n*edge ((n:ℝ)/2)=
      ∑ d ∈ I, (marks d:ℝ)/d*(cost b n*tick d n) := by
    rw [edge_eq n hn,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    ring
  rw [Finset.sum_congr rfl separate,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  have dp : 0<d := (Finset.mem_Icc.mp hd).1
  rw [←Finset.mul_sum,atom_read b dp (Finset.mem_Icc.mp hd).2 stop]
  have dr : 0<(d:ℝ) := by exact_mod_cast dp
  field_simp

#print axioms PALRH.CubicQuadrature.tick_increment
#print axioms PALRH.CubicQuadrature.atom_read
#print axioms PALRH.CubicQuadrature.actual_rows

private theorem evens (w : ℕ → ℝ) (T : ℕ) :
    (∑ j ∈ Finset.Icc 1 T, CubicWindow.oddTag j*w j)+
      (∑ j ∈ Finset.Icc 1 (T/2), w (2*j))=∑ j ∈ Finset.Icc 1 T, w j := by
  induction T with
  | zero => simp
  | succ T old =>
    rw [Finset.sum_Icc_succ_top (by omega),
      Finset.sum_Icc_succ_top (f:=w) (by omega)]
    by_cases even : 2∣T+1
    · have no : ¬Odd (T+1) := by rw [Nat.odd_iff];omega
      have half : (T+1)/2=T/2+1 := by omega
      rw [half,Finset.sum_Icc_succ_top (by omega),show 2*(T/2+1)=T+1 by omega,CubicWindow.oddTag,if_neg no]
      linarith
    · have yes : Odd (T+1) := by rw [Nat.odd_iff];omega
      rw [show (T+1)/2=T/2 by omega,CubicWindow.oddTag,if_pos yes]
      linarith

def profile (T : ℕ) (w : ℕ → ℝ) (d : ℕ) := ∑ j ∈ Finset.Icc 1 T, w (j*d)

private theorem profile_stop {w : ℕ → ℝ} {T i : ℕ} (stop : ∀ j : ℕ, T ≤ j → w j=0) (hi : T ≤ i) :
    profile T w i=0 := by
  apply Finset.sum_eq_zero
  intro j hj
  exact stop _ (hi.trans (Nat.le_mul_of_pos_left i (Finset.mem_Icc.mp hj).1))

private theorem profile_diff {w : ℕ → ℝ} {T d : ℕ} (stop : ∀ j : ℕ, T ≤ j → w j=0) (dp : 0<d) :
    profile T w d-profile T w (2*d) = ∑ j ∈ Finset.Icc 1 T, CubicWindow.oddTag j*w (j*d) := by
  have cut : profile T w (2*d) = ∑ j ∈ Finset.Icc 1 (T/2), w (j*(2*d)) := by
    symm
    apply Finset.sum_subset (fun j hj => Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hj).1,((Finset.mem_Icc.mp hj).2).trans (Nat.div_le_self _ _)⟩)
    intro j hj absent
    have outside : T/2<j := by
      by_contra! back;exact absent (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hj).1,back⟩)
    have hit : T≤(2*j)*d := (by omega : T≤2*j).trans (Nat.le_mul_of_pos_right _ dp)
    exact stop _ (by simpa [Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using hit)
  have p := evens (fun j => w (j*d)) T
  simp only [Nat.mul_assoc,show ∀ j : ℕ, 2*(j*d)=j*(2*d) from fun j => by ring] at p
  rw [cut,profile]
  linarith

/-- The full reciprocal-grid average is supported entirely on the powers of three. -/
theorem full_grid {w : ℕ → ℝ} {T : ℕ} (stop : ∀ j : ℕ, T ≤ j → w j=0) :
    (∑ n ∈ Finset.Icc 1 T, cost (profile T w) n*edge ((n:ℝ)/2))=
      ∑ n ∈ Finset.Icc 1 T, if ∃ b : ℕ, n=3^b then w n else 0 := by
  rw [actual_rows (profile T w) (fun _ hi => profile_stop stop hi)]
  let I:=Finset.Icc 1 T
  have inner (d : ℕ) (hd : d∈I) :
      (marks d:ℝ)*(profile T w d-profile T w (2*d))=
      ∑ j ∈ I, CubicWindow.oddTag j*((marks d:ℝ)*w (j*d)) := by
    rw [profile_diff stop (Finset.mem_Icc.mp hd).1,Finset.mul_sum]
    apply Finset.sum_congr rfl;intro j _;ring
  rw [Finset.sum_congr rfl inner,Finset.sum_comm,←CubicWindow.three_feed T w]
  apply Finset.sum_congr rfl
  intro j hj
  have jp : 0<j := (Finset.mem_Icc.mp hj).1
  let J:=Finset.Icc 1 (T/j)
  have trim : (∑ d ∈ I, CubicWindow.oddTag j*((marks d:ℝ)*w (j*d)))=
      ∑ d ∈ J, CubicWindow.oddTag j*((marks d:ℝ)*w (j*d)) := by
    symm
    apply Finset.sum_subset (fun d hd => Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hd).1,((Finset.mem_Icc.mp hd).2).trans (Nat.div_le_self _ _)⟩)
    intro d hd absent
    have big : T/j<d := by
      by_contra! back;exact absent (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1,back⟩)
    have hit := (Nat.div_lt_iff_lt_mul jp).mp big
    rw [stop _ (by simpa [Nat.mul_comm] using hit.le)]
    ring
  rw [trim,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have jr : 0<(j:ℝ) := by positivity
  have dr : 0<(d:ℝ) := by exact_mod_cast (show 0<d from (Finset.mem_Icc.mp hd).1)
  push_cast
  field_simp

/-- Omitting the first ordinary label changes the identical half-row average by the
single difference at d and twice d. -/
theorem omitted_grid {w : ℕ → ℝ} {T : ℕ} (stop : ∀ j : ℕ, T ≤ j → w j=0) :
    (∑ n ∈ Finset.Icc 1 T, cost (fun j => profile T w j-w j) n*edge ((n:ℝ)/2))=
      (∑ n ∈ Finset.Icc 1 T, if ∃ b : ℕ, n=3^b then w n else 0)-
        ∑ d ∈ Finset.Icc 1 T, (marks d:ℝ)*(w d-w (2*d)) := by
  rw [←full_grid stop,actual_rows (profile T w) (fun _ hi => profile_stop stop hi),
    actual_rows (fun j => profile T w j-w j) (fun j hj => by rw [profile_stop stop hj,stop j hj,sub_zero]),
    ←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl;intro d _;ring

#print axioms PALRH.CubicQuadrature.full_grid
#print axioms PALRH.CubicQuadrature.omitted_grid

end PALRH.CubicQuadrature
