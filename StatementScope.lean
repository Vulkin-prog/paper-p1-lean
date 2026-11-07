module
import PaperP1
import Lean.Meta
import Lean.Util.FoldConsts

/-! Read the compiled types for the numbered-statement scope review. -/
set_option pp.fullNames true
open Lean Elab Command Meta in
run_cmd do
  let raw ← IO.FS.readFile "docs/numbered-scope-declarations.json"
  let .ok names := Json.parse raw >>= Json.getArr? | throwError "Invalid scope inventory"
  let mut rows : Array Json := #[]
  for entry in names do
    let .ok text := entry.getStr? | throwError "Invalid declaration name"
    let info ← getConstInfo text.toName
    let typeText ← liftTermElabM do return (← ppExpr info.type).pretty
    let proposition ← liftTermElabM do isProp info.type
    let binders ← liftTermElabM do
      forallTelescope info.type fun xs _ => xs.mapM fun x => do
        let decl ← x.fvarId!.getDecl
        let ty ← ppExpr decl.type
        let prop ← isProp decl.type
        return Json.mkObj [("name",toJson decl.userName.toString),
          ("type",toJson ty.pretty),("is_proposition",toJson prop),
          ("instance_implicit",toJson decl.binderInfo.isInstImplicit)]
    rows := rows.push (Json.mkObj [("name",toJson text),
      ("is_proposition",toJson proposition),("type",toJson typeText),
      ("binders",Json.arr binders),
      ("type_constants",toJson (info.type.getUsedConstants.map Name.toString))])
  let some output ← IO.getEnv "P1_SCOPE_OUTPUT"
    | throwError "Set P1_SCOPE_OUTPUT to an output path for the compiled signature report"
  IO.FS.writeFile output (Json.arr rows).pretty
  logInfo m!"Exported compiled scope types for {rows.size} declarations"
