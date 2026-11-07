#!/usr/bin/env python3
"""Check explicit P1 registration selections and the statement-only hole boundary.

This checks preparation files; Comparator and the full Palomar workflow provide
the actual statement comparison and mechanical qualification.
"""

from pathlib import Path
import json
import re
import tomllib

import yaml

from update_audit import lean_code
from registry_plan import all_entries, load_plan

ROOT = Path(__file__).resolve().parents[1]
ALLOWED_KEYS = {"challenge_module", "solution_module", "theorem_names",
                "definition_names", "permitted_axioms", "enable_nanoda"}
REQUIRED_KEYS = {"challenge_module", "solution_module", "theorem_names", "permitted_axioms"}
AXIOMS = {"propext", "Quot.sound", "Classical.choice"}
IMPORT = re.compile(r"^(?:public )?import (\S+)\s*$", re.M)
DECLARATION = re.compile(r"^theorem ([A-Za-z0-9_.']+)(?=\s|\[|\{)", re.M)


def source_path(module):
    if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", module):
        raise ValueError(f"Expected a root candidate module: {module}")
    return ROOT / (module + ".lean")


def declarations(code):
    names = DECLARATION.findall(code)
    if not names or len(names) != len(set(names)):
        raise ValueError("Empty or repeated candidate declaration")
    if all(name.startswith("_root_.") for name in names):
        return {name.removeprefix("_root_.") for name in names}
    namespaces = re.findall(r"^namespace (\S+)\s*$", code, re.M)
    if len(namespaces) != 1 or any("." in name for name in names):
        raise ValueError("Use one namespace or explicit root-qualified declaration names")
    return {namespaces[0] + "." + name for name in names}


def main():
    lake = tomllib.loads((ROOT / "lakefile.toml").read_text())
    libraries = {row["name"]: row for row in lake["lean_lib"]}
    if "-DwarningAsError=true" not in lake.get("moreLeanArgs", []):
        raise ValueError("Substantive proof warnings must remain errors")
    entries = all_entries()
    if not entries:
        raise ValueError("No candidate configurations")
    totals = {}
    challenge_modules = set()
    for entry in entries:
        path = entry["configuration"]
        cfg = json.loads(path.read_text())
        if not REQUIRED_KEYS <= cfg.keys() <= ALLOWED_KEYS:
            raise ValueError(f"Unexpected Comparator keys: {path}")
        if set(cfg["permitted_axioms"]) != AXIOMS or cfg.get("definition_names", []):
            raise ValueError("Only the three standard axioms and theorem selections are used")
        selected = set(cfg["theorem_names"])
        if not selected or len(selected) != len(cfg["theorem_names"]):
            raise ValueError("Empty or duplicate selected declarations")
        challenge_module, solution_module = cfg["challenge_module"], cfg["solution_module"]
        if challenge_module == solution_module:
            raise ValueError("Challenge and Solution must be distinct")
        challenge_modules.add(challenge_module)
        challenge_path, solution_path = source_path(challenge_module), source_path(solution_module)
        challenge, solution = challenge_path.read_text(), solution_path.read_text()
        if len(challenge.encode()) > 100 * 1024 or len(challenge.splitlines()) > 1000:
            raise ValueError("Challenge exceeds Palomar's statement-file limits")
        ccode, scode = lean_code(challenge), lean_code(solution)
        if re.search(r"^alias\b", ccode, re.M):
            raise ValueError("Challenge statements must be explicit theorem declarations")
        if declarations(ccode) != selected or not selected <= declarations(scode):
            raise ValueError(f"Declaration selection mismatch: {path}")
        if len(re.findall(r"\bsorry\b", ccode)) != len(selected):
            raise ValueError("Every deliberate statement hole must be selected")
        if len(re.findall(r":=\s+by\s+sorry\b", ccode)) != len(selected):
            raise ValueError("Challenge holes must be explicit theorem proof holes")
        forbidden = r"\b(?:axiom|admit|native_decide|sorryAx|Lean\.ofReduceBool)\b"
        if re.search(forbidden, ccode) or re.search(forbidden + r"|\bsorry\b", scode):
            raise ValueError("Forbidden proof placeholder or axiom construct")
        imports = IMPORT.findall(ccode)
        if not imports or any(not module.startswith("Mathlib.") for module in imports):
            raise ValueError("Standalone Challenges must import only Mathlib")
        if challenge_module not in libraries or solution_module not in libraries:
            raise ValueError("Candidate Lake libraries are missing")
        if libraries[challenge_module].get("moreLeanArgs") != ["-DwarningAsError=false"]:
            raise ValueError("Only the standalone Challenge permits its explicit statement warnings")
        if "-DwarningAsError=false" in libraries[solution_module].get("moreLeanArgs", []):
            raise ValueError("Solution warnings must remain errors")
        metadata_path = entry["metadata"]
        metadata = yaml.safe_load(metadata_path.read_text())
        project = metadata["project"]
        for key in ["name", "description", "authors", "license", "responsible_maintainers"]:
            if not project.get(key):
                raise ValueError(f"Missing metadata field: project.{key}")
        if project["license"] != "Apache-2.0" or not metadata.get("sources"):
            raise ValueError("Missing source provenance or inconsistent repository licence")
        if metadata["status"]["sorry_count"] != 0 or metadata["status"]["sorry_in_definitions"] != 0:
            raise ValueError("Solution metadata must disclose complete proofs")
        count, total = totals.get(entry["kind"], (0, 0))
        totals[entry["kind"]] = (count + 1, total + len(selected))
        print(f"{entry['kind']} {path.relative_to(ROOT)}: {len(selected)} explicit statement holes, complete Solution, Mathlib-only Challenge.")
    proof_sources = list((ROOT / "PaperP1").rglob("*.lean")) + list(ROOT.glob("SolutionP1*.lean")) + [ROOT / "Audit.lean"]
    for path in proof_sources:
        imports = IMPORT.findall(lean_code(path.read_text()))
        if challenge_modules.intersection(imports):
            raise ValueError(f"A substantive proof imports a Challenge: {path}")
    for name, library in libraries.items():
        if "-DwarningAsError=false" in library.get("moreLeanArgs", []) and name not in challenge_modules:
            raise ValueError(f"Unexpected warning exception: {name}")
    plan = load_plan()
    if plan is not None:
        count, total = totals["registration"]
        print(f"Prepared {count} planned registrations and {total} selected declarations.")
        count, total = totals["component"]
        print(f"Preserved {count} separately verified components and their {total} original selections.")
        print("Submission policy: one complete registration cycle at a time.")
    else:
        count, total = totals["component"]
        print(f"Prepared {count} component families and {total} selected declarations.")
    print("Scope: preparation checks; no Comparator or Palomar verification is inferred.")


if __name__ == "__main__":
    main()
