import PALRH.OneTick

open Finset
open scoped BigOperators
noncomputable section
namespace PALRH.OneTick

/-- Keep the difference between two nearby quotient clocks after the parent fit has been transported. -/
def contrast (p h : ℕ) (f : ℕ → ℚ) := dilate p f - dilate (p+h) f

theorem contrast_mem {p : ℕ} (hp : 2≤p) (h : ℕ) {f : ℕ → ℚ} (hf : f ∈ fits) :
    contrast p h f ∈ fits := fits.sub_mem (dilate_mem hp hf) (dilate_mem (by omega) hf)

/-- Both clocks on the same physical row. At most one old event separates their readings in this range. -/
theorem close_clocks {p h t r : ℕ} (hp : 0<p) (ht : 0<t) (scale : h*t≤p) (inside : r<p) :
    (p*t+r)/p=t ∧ (p*t+r)/(p+h) = if r<h*t then t-1 else t := by
  constructor
  · rw [add_comm, Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt inside, zero_add]
  have hpq : 0<p+h := by omega
  cases t with
  | zero => omega
  | succ t =>
    split_ifs with hit
    · simp only [Nat.add_one_sub_one]
      apply Nat.le_antisymm
      · have hh : (p*(t+1)+r)/(p+h) < t+1 := (Nat.div_lt_iff_lt_mul hpq).mpr (by nlinarith)
        omega
      · apply (Nat.le_div_iff_mul_le hpq).mpr
        nlinarith
    · apply Nat.le_antisymm
      · have hh : (p*(t+1)+r)/(p+h) < (t+1)+1 :=
          (Nat.div_lt_iff_lt_mul hpq).mpr (by nlinarith)
        omega
      · apply (Nat.le_div_iff_mul_le hpq).mpr
        have := le_of_not_gt hit
        nlinarith

theorem contrast_value {p h t r : ℕ} (hp : 0<p) (ht : 0<t) (scale : h*t≤p) (inside : r<p)
    (f : ℕ → ℚ) :
    contrast p h f (p*t+r) = if r<h*t then f t - f (t-1) else 0 := by
  obtain ⟨a,b⟩ := close_clocks hp ht scale inside
  unfold contrast dilate
  simp only [Pi.sub_apply,a,b]
  split_ifs <;> simp

/-- Sum the actual row lengths in one returning comparison band. -/
theorem contrast_band_mass {p h t : ℕ} (hp : 0<p) (ht : 0<t) :
    ∑ r ∈ Finset.range (h*t), rowWeight (p*t-1+r) =
      (h:ℝ)/((p:ℝ)*(p+h)*t) := by
  rw [rowWeight_block]
  have hpos := Nat.mul_pos hp ht
  have ha : p*t-1+1 = p*t := by omega
  have hb : p*t-1+h*t+1 = (p+h)*t := by
    rw [show p*t-1+h*t+1 = (p*t-1+1)+h*t by omega,ha,add_mul]
  have a : ((p*t-1:ℕ):ℝ)+1=(p:ℝ)*t := by exact_mod_cast ha
  have b : ((p*t-1+h*t:ℕ):ℝ)+1=((p:ℝ)+h)*t := by exact_mod_cast hb
  rw [a,b]
  field_simp
  ring

theorem contrast_band_energy {p h t : ℕ} (hp : 0<p) (ht : 0<t) (scale : h*t≤p) (f : ℕ → ℚ) :
    ∑ r ∈ Finset.range (h*t), rowWeight (p*t-1+r) * (contrast p h f (p*t+r) : ℝ)^2 =
      (h:ℝ)/((p:ℝ)*(p+h)*t) * ((f t - f (t-1) : ℚ):ℝ)^2 := by
  calc
    _ = ∑ r ∈ Finset.range (h*t), rowWeight (p*t-1+r) * ((f t-f (t-1) : ℚ):ℝ)^2 := by
      apply Finset.sum_congr rfl
      intro r hr
      have h := Finset.mem_range.mp hr
      rw [contrast_value hp ht scale (h.trans_le scale), if_pos h]
    _ = _ := by rw [← Finset.sum_mul,contrast_band_mass hp ht]

private def mark (d k : ℕ) : ℚ := if d ∣ k then 1 else 0

private theorem mark_count {d L : ℕ} (hd : 0<d) (period : d ∣ L) :
    (∑ t ∈ Finset.range L, mark d (t+1)) = (L:ℚ)/d := by
  have h := Finset.sum_range_sub (turn d) L
  have hj (i : ℕ) : turn d (i+1)-turn d i = 1/(d:ℚ)-mark d (i+1) := turn_step hd i
  simp_rw [hj] at h
  rw [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_range] at h
  simp only [turn,Nat.mod_eq_zero_of_dvd period, Nat.zero_mod, Nat.cast_zero,zero_div, sub_self,
    nsmul_eq_mul, mul_one_div] at h
  linarith

/-- The ordinary period mean of the two recovered signed edge readings. -/
theorem edge_gram_period {a b L : ℕ} (ha : 0<a) (hb : 0<b)
    (pa : a ∣ L) (pb : b ∣ L) :
    (∑ t ∈ Finset.range L, (turn a (t+1)-turn a t)*(turn b (t+1)-turn b t)) =
      (L:ℚ)*(1/(a.lcm b : ℕ) - 1/((a:ℚ)*b)) := by
  let c := a.lcm b
  have hc : 0<c := Nat.lcm_pos ha hb
  have pc : c ∣ L := Nat.lcm_dvd pa pb
  have ab (k : ℕ) : mark a k * mark b k = mark c k := by
    simp only [mark,c,Nat.lcm_dvd_iff]
    by_cases a' : a ∣ k <;> by_cases b' : b ∣ k <;> simp [a',b']
  have step (t : ℕ) : (turn a (t+1)-turn a t)*(turn b (t+1)-turn b t) =
      1/((a:ℚ)*b) - (1/(b:ℚ))*mark a (t+1) - (1/(a:ℚ))*mark b (t+1) + mark c (t+1) := by
    rw [turn_step ha,turn_step hb, ← ab]
    change (1/(a:ℚ)-mark a (t+1))*(1/(b:ℚ)-mark b (t+1)) = _
    ring
  simp_rw [step]
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.sum_sub_distrib,
    Finset.sum_const,Finset.card_range,←Finset.mul_sum,←Finset.mul_sum,
    mark_count ha pa,mark_count hb pb,mark_count hc pc]
  simp only [nsmul_eq_mul,c]
  ring

/-- The uninspected rows have a uniform allowance. The head contains every return band
through old row T, including the zero-read parts between them. -/
theorem contrast_full_bounds {p h T : ℕ} (hp : 0<p) (scale : h*T≤p)
    (f : ℕ → ℚ) {C : ℝ} (bounded_f : ∀ k, ‖(f k : ℝ)‖≤C) :
    let g := contrast p h f
    let head := ∑ i ∈ Finset.range T, (h:ℝ)/((p:ℝ)*(p+h)*((i:ℝ)+1)) *
      ((f (i+1)-f i : ℚ):ℝ)^2
    head ≤ cost g ∧ cost g ≤ head+(2*C)^2/((p:ℝ)*((T:ℝ)+1)) := by
  let g := contrast p h f
  let a := fun n : ℕ => rowWeight n*(g (n+1):ℝ)^2
  let term := fun i : ℕ => (h:ℝ)/((p:ℝ)*(p+h)*((i:ℝ)+1))*((f (i+1)-f i:ℚ):ℝ)^2
  have fullBlock (t : ℕ) (ht : 0<t) (hs : h*t≤p) :
      ∑ i ∈ Finset.range p, rowWeight (p*t-1+i)*(g (p*t+i):ℝ)^2 =
        (h:ℝ)/((p:ℝ)*(p+h)*t)*((f t-f (t-1):ℚ):ℝ)^2 := by
    rw [← contrast_band_energy hp ht hs f]
    symm
    apply Finset.sum_subset (Finset.range_mono hs)
    intro r hr hx
    have inside := Finset.mem_range.mp hr
    have outside : ¬ r < h*t := fun q => hx (Finset.mem_range.mpr q)
    simp [contrast_value hp ht hs inside f, outside]
  have pre (t : ℕ) (hs : h*t≤p) :
      (∑ i ∈ Finset.range (p*(t+1)-1), a i) = ∑ i ∈ Finset.range t, term i := by
    induction t with
    | zero =>
      simp only [zero_add,mul_one,Finset.range_zero,Finset.sum_empty]
      apply Finset.sum_eq_zero
      intro i hi
      have lt := Finset.mem_range.mp hi
      have h1 : (i+1)/p=0 := Nat.div_eq_of_lt (by omega)
      have h2 : (i+1)/(p+h)=0 := Nat.div_eq_of_lt (by omega)
      simp [a,g,contrast,dilate,h1,h2]
    | succ t ih =>
      have hprev : h*t≤p := (Nat.mul_le_mul_left h (Nat.le_succ t)).trans hs
      have hpos := Nat.mul_pos hp (show 0<t+1 by omega)
      have eq : p*(t+1+1)-1=(p*(t+1)-1)+p := by rw [Nat.mul_succ]; omega
      rw [eq,Finset.sum_range_add,ih hprev,Finset.sum_range_succ]
      congr 1
      calc
        _ = ∑ r ∈ Finset.range p, rowWeight (p*(t+1)-1+r)*(g (p*(t+1)+r):ℝ)^2 := by
          apply Finset.sum_congr rfl
          intro r _
          simp only [a,show p*(t+1)-1+r+1=p*(t+1)+r by omega]
        _ = _ := by simpa [term] using fullBlock (t+1) (by omega) hs
  have gb (k : ℕ) : ‖(g k:ℝ)‖ ≤ 2*C := by
    simp only [g,contrast,dilate,Pi.sub_apply,Rat.cast_sub]
    linarith [norm_sub_le (f (k/p):ℝ) (f (k/(p+h)):ℝ),bounded_f (k/p),bounded_f (k/(p+h))]
  have nonneg (k : ℕ) : 0 ≤ a k := mul_nonneg (by unfold rowWeight; positivity) (sq_nonneg _)
  have cap (k : ℕ) : a k ≤ rowWeight k*(2*C)^2 := by
    apply mul_le_mul_of_nonneg_left _ (by unfold rowWeight; positivity)
    rw [←sq_abs (g (k+1):ℝ)]
    exact pow_le_pow_left₀ (abs_nonneg _) (gb _) _
  have summable : Summable a := Summable.of_nonneg_of_le nonneg cap (rowWeight_hasSum.summable.mul_right _)
  let cut := p*(T+1)-1
  have cutEq : cut+1=p*(T+1) := by dsimp [cut]; have := Nat.mul_pos hp (show 0<T+1 by omega); omega
  change (∑ i ∈ Finset.range T, term i) ≤ ∑' i, a i ∧ (∑' i, a i) ≤ _
  constructor
  · rw [← pre T scale]
    exact summable.sum_le_tsum _ (fun n _ => nonneg n)
  · rw [← summable.sum_add_tsum_nat_add cut, pre T scale]
    apply add_le_add (le_refl _)
    have tail := ((summable_nat_add_iff cut).mpr summable).tsum_le_tsum (fun n => cap (n+cut))
      (((summable_nat_add_iff cut).mpr rowWeight_hasSum.summable).mul_right ((2*C)^2))
    rw [tsum_mul_right,rowWeight_tail] at tail
    have cc : (cut:ℝ)+1=(p:ℝ)*((T:ℝ)+1) := by exact_mod_cast cutEq
    rw [cc] at tail
    simpa only [div_eq_mul_inv,one_mul,mul_comm] using tail

/-- Different coprime old channels have zero mean signed edge overlap. -/
theorem coprime_edge_mean_zero {a b L : ℕ} (ha : 0<a) (hb : 0<b)
    (pa : a ∣ L) (pb : b ∣ L) (hc : a.Coprime b) :
    (∑ t ∈ Finset.range L, (turn a (t+1)-turn a t)*(turn b (t+1)-turn b t)) = 0 := by
  rw [edge_gram_period ha hb pa pb, hc.lcm_eq_mul]
  push_cast
  ring

private theorem mark_harmonic {d : ℕ} (hd : 0<d) (T : ℕ) :
    (∑ t ∈ Finset.range T, mark d (t+1) / ((t:ℚ)+1)) = harmonic (T/d)/d := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.sum_range_succ,ih]
    by_cases hit : d ∣ T+1
    · have eq := Nat.div_mul_cancel hit
      rw [Nat.succ_div_of_dvd hit] at eq ⊢
      rw [harmonic_succ, add_div]
      have ce : ((T/d:ℕ):ℚ)+1 ≠ 0 := by positivity
      have de : (d:ℚ) ≠ 0 := by positivity
      have prod : (((T/d:ℕ):ℚ)+1)*d = (T:ℚ)+1 := by exact_mod_cast eq
      simp only [mark, if_pos hit, Nat.cast_add, Nat.cast_one]
      rw [← prod]
      field_simp
    · simp [mark,hit,Nat.succ_div_of_not_dvd hit]

/-- Exact cost of the recovered edge overlap in harmonic units, at every finite horizon. -/
theorem edge_harmonic {a b : ℕ} (ha : 0<a) (hb : 0<b) (T : ℕ) :
    (∑ t ∈ Finset.range T, (turn a (t+1)-turn a t)*(turn b (t+1)-turn b t) / ((t:ℚ)+1)) =
    (harmonic T - harmonic (T/a) - harmonic (T/b))/((a:ℚ)*b) +
      harmonic (T/(a.lcm b))/(a.lcm b : ℕ) := by
  let c := a.lcm b
  have hc : 0<c := Nat.lcm_pos ha hb
  have ab (k : ℕ) : mark a k * mark b k = mark c k := by
    simp only [mark,c,Nat.lcm_dvd_iff]
    by_cases a' : a ∣ k <;> by_cases b' : b ∣ k <;> simp [a',b']
  have term (t : ℕ) :
      (turn a (t+1)-turn a t)*(turn b (t+1)-turn b t)/((t:ℚ)+1) =
      (1/((a:ℚ)*b))*((↑(t+1 : ℕ):ℚ)⁻¹) -
        (1/(b:ℚ))*(mark a (t+1)/((t:ℚ)+1)) -
        (1/(a:ℚ))*(mark b (t+1)/((t:ℚ)+1)) + mark c (t+1)/((t:ℚ)+1) := by
    rw [turn_step ha,turn_step hb, ←ab]
    change (1/(a:ℚ)-mark a (t+1))*(1/(b:ℚ)-mark b (t+1)) / _ = _
    push_cast
    ring
  simp_rw [term]
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.sum_sub_distrib,
    ←Finset.mul_sum,←Finset.mul_sum,←Finset.mul_sum, mark_harmonic ha,
    mark_harmonic hb,mark_harmonic hc]
  change (1/((a:ℚ)*b))*harmonic T-1/b*(harmonic (T/a)/a)-1/a*(harmonic (T/b)/b)+_ = _
  dsimp only [c]
  ring

#print axioms PALRH.OneTick.edge_harmonic
#print axioms PALRH.OneTick.contrast_full_bounds
end PALRH.OneTick
