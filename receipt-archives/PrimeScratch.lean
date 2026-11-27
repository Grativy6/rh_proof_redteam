namespace PrimeScratch

/-- The position with place value 16 in the binary expansion. -/
def scratch (n : Nat) : Nat := n / 16 % 2

def lowFour (n : Nat) : Nat := n % 16

theorem equalLowFour : lowFour 17 = lowFour 257 := by decide

theorem markedPrimes : scratch 17 = 1 ∧ scratch 257 = 0 := by decide

theorem noCommonReader (read : Nat → Nat) :
    ¬ (read (lowFour 17) = scratch 17 ∧ read (lowFour 257) = scratch 257) := by
  intro h
  have one : read 1 = 1 := h.1
  have zero : read 1 = 0 := h.2
  exact (by decide : (1 : Nat) ≠ 0) (one.symm.trans zero)

end PrimeScratch

def main (args : List String) : IO Unit := do
  for arg in args do
    match arg.toNat? with
    | none => throw (IO.userError "Expected a natural number in decimal.")
    | some n =>
      let low := PrimeScratch.lowFour n
      IO.println s!"n={n} low4={low} scratch={PrimeScratch.scratch n} from4={PrimeScratch.scratch low} from5={PrimeScratch.scratch (n % 32)}"
