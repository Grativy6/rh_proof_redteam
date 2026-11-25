/-
Ordinary mathematical regression driver for Lean 4.36.0's exported-data checks.
This calls the shipped comparison and axiom functions; it is not a replacement
for `lake comparator` and provides no source-build or process-isolation guarantee.
Only use it with the reviewed mathematical fixtures in this directory.
-/
import Lake.Check.Compare
import Lake.Check.Axioms
import Lean.Data.Json.FromToJson

open Lean Lake.Check

structure FixtureConfig where
  theorem_names : Array String
  permitted_axioms : Array String
  definition_names : Option (Array String) := none
  deriving FromJson

-- Pinned to Lake/CLI/Check.lean's primitiveTargets in Lean 4.36.0.
def primitiveTargets : Array Name := #[
  ``Nat.add, ``Nat.sub, ``Nat.mul, ``Nat.pow, ``Nat.gcd, ``Nat.div,
  ``Nat.mod, ``Nat.beq, ``Nat.ble, ``Nat.land, ``Nat.lor, ``Nat.xor,
  ``Nat.shiftLeft, ``Nat.shiftRight, ``String.ofList, ``Char.ofNat,
  ``List, ``eagerReduce, ``Nat, ``String, ``String.mk, ``Char,
  ``optParam, ``autoParam, ``semiOutParam, ``outParam
]

def main (args : List String) : IO UInt32 := do
  let [configPath, challengePath, solutionPath] := args
    | IO.eprintln "usage: lean --run CompareExports.lean CONFIG CHALLENGE.ndjson SOLUTION.ndjson"
      return 2
  let configJson ← IO.ofExcept <| Json.parse (← IO.FS.readFile configPath)
  let cfg : FixtureConfig ← IO.ofExcept <| fromJson? configJson
  let challenge ← LeanExport.parseStream <| .ofHandle (← IO.FS.Handle.mk challengePath .read)
  let solution ← LeanExport.parseStream <| .ofHandle (← IO.FS.Handle.mk solutionPath .read)
  let theorems := cfg.theorem_names.map String.toName
  let axioms := cfg.permitted_axioms.map String.toName
  let definitions := (cfg.definition_names.getD #[]).map String.toName
  match compareAt challenge solution (theorems ++ axioms) definitions primitiveTargets with
  | .error message =>
    IO.println s!"stage=comparison; rejected: {message}"
    return 1
  | .ok _ => pure ()
  match checkAxioms solution theorems definitions axioms with
  | .error message =>
    IO.println s!"stage=axioms; rejected: {message}"
    return 1
  | .ok _ =>
    IO.println "stage=complete; comparison and axiom checks passed; no kernel or sandbox claim"
    return 0
