import Lean

/- Decode the axiom table written by Lean 4.33.1, without importing the
   target module. The input must be a trusted .olean of this version.
   The table's entries have the erased EnvExtensionEntry type. Their schema
   is fixed by Lean/Util/CollectAxioms.lean at the tag below. -/

open Lean

unsafe def main (args : List String) : IO UInt32 := do
  let [path] := args | throw (IO.userError "Expected one compiled module path.")
  unless Lean.versionString == "4.33.1" do
    throw (IO.userError s!"Expected Lean 4.33.1, found {Lean.versionString}")
  let (moduleData, _region) ← readModuleData path
  let tag := "_private.Lean.Util.CollectAxioms.0.Lean.exportedAxiomsExt"
  let some (_, entries) := moduleData.entries.find? (fun e => e.1.toString == tag)
    | throw (IO.userError "Missing versioned CollectAxioms extension")
  let table : Array (Name × Array Name) := entries.map (fun x => unsafeCast x)
  for declaration in moduleData.constants do
    match declaration with
    | .thmInfo th =>
      if th.name.isInternal then continue
      let some (_, axs) := table.find? (fun entry => entry.1 == th.name)
        | throw (IO.userError s!"Missing receipt for {th.name}")
      let row := Json.mkObj [("name", toJson th.name.toString),
        ("axioms", toJson (axs.map Name.toString)), ("typeExpr", toJson (toString th.type)),
        ("bodyConstants", toJson (th.value.getUsedConstants.map Name.toString))]
      IO.println row.compress
    | _ => pure ()
  return 0
