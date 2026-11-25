import PALRH

theorem oddReopening (N : ℕ) (c : Fin N → ℚ)
    (hit : 1 - ∑ i, c i * (((2 % (i.val+2) : ℕ) : ℚ) / (i.val+2 : ℕ)) = 0) :
    ∃ j : ℕ, (1:ℚ)/2 ≤ |1 - ∑ i, c i * (((((2*j+1) % (i.val+2)) : ℕ) : ℚ) / (i.val+2 : ℕ))| := PALRH.odd_displacement c hit
