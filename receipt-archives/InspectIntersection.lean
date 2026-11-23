import Lean

/-!
Read elaborated constants from the unmodified release's compiled module files.
This is a term inspection, not a kernel replay. Supply the olean root followed by
module names. The audit script chooses modules from the published dependency graph.
-/

open Lean

structure Field where
  name : Name
  owner : Name
  index : Nat
  arity : Nat
  afterRecord : Nat
deriving Inhabited

def watchedNames : List String := [
  "Formalism.BasicNotions.DV.Geo.inter",
  "Formalism.BasicNotions.DV.Geo.H0",
  "Formalism.L2.Geo.AlgPkg.degA",
  "Formalism.L2.Geo.AlgPkg.degA_ofW",
  "Formalism.L2.Geo.AlgPkg.degA_twist"
]

partial def countForalls : Expr → Nat
  | .forallE _ _ b _ => countForalls b + 1
  | .mdata _ b => countForalls b
  | _ => 0

partial def projectionInfo (e : Expr) (n : Nat := 0) : Option (Name × Nat × Nat) :=
  match e with
  | .lam _ _ b _ => projectionInfo b (n + 1)
  | .mdata _ b => projectionInfo b n
  | .proj owner i _ => some (owner, i, n)
  | _ => none

structure Hit where
  field : String
  encoding : String
  supplied : Nat
  form : String
deriving BEq, ToJson

structure Scan where
  seen : Std.HashSet (Expr × Bool) := {}
  hits : Array Hit := #[]

def tupleForm (e : Expr) : String :=
  match e.consumeMData with
  | .lam _ _ body _ => if body.hasLooseBVar 0 then "slot-dependent-lambda" else "constant-tuple"
  | _ => "other-tuple"

partial def scanExpr (fs : Array Field) (e : Expr) (underRank : Bool := false) : StateM Scan Unit := do
  if (← get).seen.contains (e, underRank) then return
  modify fun s => { s with seen := s.seen.insert (e, underRank) }
  let head := e.getAppFn
  let args := e.getAppArgs
  let nestedRank := underRank || head.isConstOf `Module.finrank || head.isConstOf `Module.rank
  for f in fs do
    let site : Option (String × Nat) := match head with
      | .const n _ => if n == f.name then some ("named", f.arity) else none
      | .proj n i _ => if n == f.owner && i == f.index then some ("projection", f.afterRecord) else none
      | _ => none
    if let some (encoding, arity) := site then
      let form := if args.size < arity then "partial"
        else if f.name.toString == "Formalism.BasicNotions.DV.Geo.inter" then
          tupleForm args[arity - 1]!
        else if f.name.toString == "Formalism.BasicNotions.DV.Geo.H0" && underRank then "under-rank"
        else "applied"
      let h : Hit := ⟨f.name.toString, encoding, args.size, form⟩
      modify fun s => if s.hits.contains h then s else {s with hits := s.hits.push h}
  match head with
  | .forallE _ t b _ | .lam _ t b _ => scanExpr fs t nestedRank; scanExpr fs b nestedRank
  | .letE _ t v b _ => scanExpr fs t nestedRank; scanExpr fs v nestedRank; scanExpr fs b nestedRank
  | .mdata _ b | .proj _ _ b => scanExpr fs b nestedRank
  | _ => pure ()
  for a in args do scanExpr fs a nestedRank

def emitHits (fs : Array Field) (moduleLabel : String) (ci : ConstantInfo) (phase : String)
    (e : Expr) : IO Unit := do
  let (_, st) := (scanExpr fs e).run {}
  unless st.hits.isEmpty do
    IO.println (Json.mkObj [("module", toJson moduleLabel), ("decl", toJson ci.name.toString),
      ("phase", toJson phase), ("hits", toJson st.hits)]).compress

def readParts (path : System.FilePath) : IO (Array (ModuleData × CompactedRegion)) := do
  let mut files := #[path]
  let server := OLeanLevel.server.adjustFileName path
  let priv := OLeanLevel.private.adjustFileName path
  if ← server.pathExists then
    files := files.push server
    if ← priv.pathExists then files := files.push priv
  return ← readModuleDataParts files

def main (args : List String) : IO Unit := do
  let base :: modules := args | throw (IO.userError "Expected an olean directory and module names")
  let pathFor := fun (mod : String) => System.FilePath.mk base / (mod.replace "." "/" ++ ".olean")
  let mut fields : Array Field := #[]
  for mod in ["Formalism.LocalRingCardinality.DataDIV", "Formalism.LocalToGlobal.LatticeGeometry.ArVolEqOfNef"] do
    let parts ← readParts (pathFor mod)
    let some (data, _) := parts.back? | throw (IO.userError "Missing module data")
    for ci in data.constants do
      if watchedNames.contains ci.name.toString then
        let some value := ci.value? true | throw (IO.userError s!"No projector body: {ci.name}")
        let some (owner, index, recArgs) := projectionInfo value | throw (IO.userError s!"Unexpected projector: {ci.name}")
        let arity := countForalls ci.type
        -- Reparse names while their module is alive. Only the descriptors cross reads.
        fields := fields.push ⟨ci.name.toString.toName, owner.toString.toName, index, arity, arity - recArgs⟩
  unless fields.size == watchedNames.length do throw (IO.userError "Calibration incomplete")
  for f in fields do
    IO.println (Json.mkObj [("calibration", toJson f.name.toString), ("owner", toJson f.owner.toString),
      ("index", toJson f.index), ("arity", toJson f.arity), ("afterRecord", toJson f.afterRecord)]).compress
  for mod in modules do
    let parts ← readParts (pathFor mod)
    let some (data, _) := parts.back? | throw (IO.userError "Missing module data")
    for ci in data.constants do
      emitHits fields mod ci "type" ci.type
      if let some v := ci.value? true then emitHits fields mod ci "value" v
    IO.println (Json.mkObj [("scanned", toJson mod), ("declarations", toJson data.constants.size)]).compress
