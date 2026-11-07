#!/usr/bin/env python3
"""Export actual compiled Lean types and axiom reports for a manuscript inventory.

The temporary diagnostic module adds no theorem to the formal development.
Run this after building the pinned project; it does not download dependencies.
"""

from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
PERMITTED = {"propext", "Classical.choice", "Quot.sound"}
LEAN = r'''module
import PaperP1
import Lean.Meta
import Lean.Elab.Print
import Lean.Util.FoldConsts
import Lean.OriginalConstKind

set_option pp.fullNames true
open Lean Elab Command Meta in
run_cmd do
  let some input ← IO.getEnv "P1_SCOPE_INPUT" | throwError "Missing scope input"
  let raw ← IO.FS.readFile input
  let .ok names := Json.parse raw >>= Json.getArr? | throwError "Invalid scope inventory"
  let mut rows : Array Json := #[]
  for entry in names do
    let .ok text := entry.getStr? | throwError "Invalid declaration name"
    let info ← getConstInfo text.toName
    let typeText ← liftTermElabM do return (← ppExpr info.type).pretty
    let proposition ← liftTermElabM do isProp info.type
    let exportedKind := match info with
      | .thmInfo _ => "theorem"
      | .defnInfo _ => "definition"
      | .axiomInfo _ => "axiom_signature"
      | .opaqueInfo _ => "opaque"
      | _ => "other"
    -- The module system exports theorem signatures without their proof bodies.
    -- Read the original declaration kind instead of treating those as axioms.
    let kind := match getOriginalConstKind? (← getEnv) text.toName with
      | some .thm => "theorem"
      | some .defn => "definition"
      | some .axiom => "axiom"
      | some .opaque => "opaque"
      | _ => "other"
    if proposition then
      elabCommand (← `(command| #print axioms $(mkIdent text.toName)))
    let binders ← liftTermElabM do
      forallTelescope info.type fun xs _ => xs.mapM fun x => do
        let decl ← x.fvarId!.getDecl
        let ty ← ppExpr decl.type
        let prop ← isProp decl.type
        return Json.mkObj [("name",toJson decl.userName.toString),
          ("type",toJson ty.pretty),("is_proposition",toJson prop),
          ("instance_implicit",toJson decl.binderInfo.isInstImplicit)]
    rows := rows.push (Json.mkObj [("name",toJson text),("kind",toJson kind),
      ("exported_kind",toJson exportedKind),
      ("is_proposition",toJson proposition),("type",toJson typeText),
      ("binders",Json.arr binders),
      ("type_constants",toJson (info.type.getUsedConstants.map Name.toString))])
  let some output ← IO.getEnv "P1_SCOPE_OUTPUT" | throwError "Missing scope output"
  IO.FS.writeFile output (Json.arr rows).pretty
  logInfo m!"Exported compiled scope types for {rows.size} declarations"
'''


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--names", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    args = parser.parse_args()
    names_path = args.names.resolve()
    names = json.loads(names_path.read_text())
    if (not isinstance(names, list) or not names or any(not isinstance(n, str) for n in names)
            or len(set(names)) != len(names)):
        raise ValueError("Scope inventory must contain distinct declaration-name strings")
    output = args.output_dir.resolve()
    output.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ)
    env.update(P1_SCOPE_INPUT=str(names_path), P1_SCOPE_OUTPUT=str(output / "compiled-types.json"))
    subprocess.run([sys.executable, str(ROOT / "scripts/check_disk.py")], check=True)
    try:
        with tempfile.TemporaryDirectory(prefix="lean-scope-", dir=output) as temporary:
            module = Path(temporary) / "ManuscriptScope.lean"
            module.write_text(LEAN)
            with (output / "compiled-types.log").open("w") as log:
                result = subprocess.run(["lake", "env", "lean", str(module)],
                                        cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT)
            (output / "compiled-types.exit").write_text(str(result.returncode) + "\n")
    finally:
        subprocess.run([sys.executable, str(ROOT / "scripts/check_disk.py")], check=True)
    if result.returncode:
        print("\n".join((output / "compiled-types.log").read_text().splitlines()[-25:]))
        raise SystemExit(result.returncode)
    rows = json.loads((output / "compiled-types.json").read_text())
    if [row["name"] for row in rows] != names:
        raise ValueError("Compiled output differs from the requested declaration inventory")
    pattern = re.compile(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)")
    matches = pattern.findall((output / "compiled-types.log").read_text())
    axioms = {name: [a.strip() for a in raw.split(",") if a.strip()] for name, raw in matches}
    propositions = {row["name"] for row in rows if row["is_proposition"]}
    if len(matches) != len(axioms) or set(axioms) != propositions:
        raise ValueError("Axiom report does not cover every compiled proposition once")
    if any(not set(values) <= PERMITTED for values in axioms.values()):
        raise ValueError("A proposition uses an unpermitted axiom")
    validation = {"actual_exit_code": result.returncode, "compiled_types": len(rows),
                  "propositions_audited": len(propositions), "permitted_axioms": sorted(PERMITTED),
                  "all_propositions_standard_axioms_only": True,
                  "inventory_sha256": sha(names_path),
                  "diagnostic_module_sha256": hashlib.sha256(LEAN.encode()).hexdigest(),
                  "compiled_types_sha256": sha(output / "compiled-types.json"),
                  "log_sha256": sha(output / "compiled-types.log")}
    (output / "compiled-types-validation.json").write_text(json.dumps(validation, indent=2) + "\n")
    print(f"Exported {len(rows)} actual compiled types; {len(propositions)} proposition axiom checks passed.")


if __name__ == "__main__":
    main()
