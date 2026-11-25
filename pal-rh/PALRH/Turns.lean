import Mathlib.Tactic

namespace PALRH

/-- The oriented fractional turn at row k and modulus d. -/
def turn (d k : ℕ) : ℚ := (k % d : ℕ) / (d : ℚ)

/-- Subtract a third-turn from a half-turn and restore the turn to [0,1). -/
theorem sixth_turn (k : ℕ) :
    turn 6 k = turn 2 k - turn 3 k + if turn 2 k < turn 3 k then 1 else 0 := by
  let r := k % 6
  have hr : r < 6 := Nat.mod_lt k (by decide)
  have h2 : k % 2 = r % 2 := (Nat.mod_mod_of_dvd k (by decide : 2 ∣ 6)).symm
  have h3 : k % 3 = r % 3 := (Nat.mod_mod_of_dvd k (by decide : 3 ∣ 6)).symm
  unfold turn
  rw [h2, h3]
  change (r : ℚ) / 6 = _
  interval_cases r <;> norm_num

def fourReadings (f : ℕ → ℚ) : ℚ := -2 * f 1 + f 3 + f 5 - f 6

theorem fourReadings_turn {d : ℕ} (hd : 2 ≤ d) :
    fourReadings (turn d) = if d = 6 then 1 else 0 := by
  by_cases h : d ≤ 6
  · interval_cases d <;> norm_num [fourReadings, turn]
  · have h' : 6 < d := by omega
    simp only [fourReadings, turn, Nat.mod_eq_of_lt (by omega : 1 < d),
      Nat.mod_eq_of_lt (by omega : 3 < d), Nat.mod_eq_of_lt (by omega : 5 < d),
      Nat.mod_eq_of_lt h', if_neg (by omega : d ≠ 6)]
    push_cast
    ring

theorem fourReadings_target : fourReadings (fun _ => 1) = -1 := by norm_num [fourReadings]

end PALRH
