#!/usr/bin/env python3
"""Read the six-registration plan and its separately preserved component checks."""

from pathlib import Path, PurePosixPath
import json
import re
import hashlib
import yaml

ROOT = Path(__file__).resolve().parents[1]
PLAN = ROOT / "palomar/REGISTRATION_PLAN.json"
AUTHOR = {"name": "Brice Pouly", "github": "Vulkin-prog", "orcid": "0009-0008-8491-2467"}


def safe_relative(value):
    path = PurePosixPath(value)
    if path.is_absolute() or ".." in path.parts or not path.parts:
        raise ValueError(f"Unsafe registration-plan path: {value}")
    return ROOT / str(path)


def load_plan():
    if not PLAN.exists():
        return None
    plan = json.loads(PLAN.read_text())
    if plan.get("author") != AUTHOR:
        raise ValueError("The registration plan must preserve the verified structured author record")
    bundles = plan["bundles"]
    if plan["target_registration_count"] != 6 or len(bundles) != 6:
        raise ValueError("The authorized target is exactly six registrations")
    policy = plan["submission_policy"]
    if (policy["maximum_active_submissions"] != 1
            or policy["dispatch_one_bundle_only"] is not True
            or policy["complete_or_close_entire_cycle_before_next"] is not True):
        raise ValueError("Registration cycles must be strictly serial")
    if policy["cycle_includes"] != ["full_workflow", "intake", "mechanical_verification",
                                    "editorial_review", "human_decision",
                                    "registration_or_documented_closure"]:
        raise ValueError("Every complete cycle must include mechanical and human editorial stages")
    slugs, originals, selected, components = [], [], [], []
    for index, bundle in enumerate(bundles, 1):
        slug = bundle["slug"]
        if bundle["order"] != index or not re.fullmatch("[a-z][a-z0-9_]*", slug):
            raise ValueError("Invalid registration order or slug")
        slugs.append(slug)
        cfgpath = safe_relative(bundle["configuration"])
        metadata = safe_relative(bundle["metadata"])
        if cfgpath.parent != ROOT / "comparator/registrations":
            raise ValueError("Active registration configurations must use their own directory")
        if metadata != ROOT / "palomar/v2" / slug / "formalization.yaml":
            raise ValueError("Unexpected active registration metadata location")
        document = yaml.safe_load(metadata.read_text())
        project = document["project"]
        if (project.get("authors") != [AUTHOR]
                or project.get("responsible_maintainers") != [AUTHOR]
                or "author_identifiers" in project):
            raise ValueError(f"Missing structured name/GitHub/ORCID association: {slug}")
        own_sources = [row for row in document["sources"]
                       if row.get("id") == "https://github.com/Vulkin-prog/paper-p1-lean"]
        if not own_sources or any(row.get("authors") != [AUTHOR] for row in own_sources):
            raise ValueError(f"The paper source must retain its structured author and ORCID: {slug}")
        cfg = json.loads(cfgpath.read_text())
        mapping = bundle["declaration_mapping"]
        names = [row["declaration"] for row in mapping]
        if (cfg["theorem_names"] != names or len(names) != bundle["selected_count"]
                or cfg["challenge_module"] != bundle["challenge_module"]
                or cfg["solution_module"] != bundle["solution_module"]):
            raise ValueError(f"Registration configuration differs from its exact mapping: {slug}")
        selected.extend(names)
        originals.extend(row["original_declaration"] for row in mapping)
        declared_components = set()
        by_component = {}
        component_names = []
        for component in bundle["components"]:
            family = component["family"]
            declared_components.add(family)
            components.append(family)
            old = json.loads(safe_relative(component["configuration"]).read_text())
            if old["theorem_names"] != component["declarations"]:
                raise ValueError(f"Original component selection changed: {family}")
            for kind in ["challenge", "solution"]:
                module = component[kind + "_module"]
                if (old[kind + "_module"] != module
                        or not re.fullmatch("[A-Za-z_][A-Za-z0-9_']*", module)
                        or hashlib.sha256((ROOT / (module + ".lean")).read_bytes()).hexdigest()
                        != component[kind + "_sha256"]):
                    raise ValueError(f"Original component source changed: {family}, {kind}")
            by_component[family] = set(component["declarations"])
            component_names.extend(component["declarations"])
        if (set(component_names) != {row["original_declaration"] for row in mapping}
                or declared_components != {row["component"] for row in mapping}):
            raise ValueError(f"A registration loses or invents a component declaration: {slug}")
        if any(row["original_declaration"] not in by_component[row["component"]]
               for row in mapping):
            raise ValueError(f"Incorrect declaration-to-component correspondence: {slug}")
    if len(slugs) != len(set(slugs)) or len(components) != len(set(components)):
        raise ValueError("Repeated registration or component")
    if (len(components) != 17 or len(originals) != 68 or len(set(originals)) != 68
            or len(selected) != 68 or len(set(selected)) != 68):
        raise ValueError("The six registrations must preserve all 68 selections bijectively")
    expected = {p.stem.removeprefix("p1_") for p in (ROOT / "comparator").glob("p1_*.json")}
    if set(components) != expected:
        raise ValueError("The registration plan does not preserve every verified component")
    return plan


def component_entries():
    return [{"kind": "component", "slug": path.stem.removeprefix("p1_"),
             "configuration": path,
             "metadata": ROOT / "palomar/v1" / path.stem.removeprefix("p1_") / "formalization.yaml"}
            for path in sorted((ROOT / "comparator").glob("p1_*.json"))]


def registration_entries():
    plan = load_plan()
    if plan is None:
        return component_entries()
    return [{"kind": "registration", "slug": row["slug"],
             "configuration": safe_relative(row["configuration"]),
             "metadata": safe_relative(row["metadata"])} for row in plan["bundles"]]


def all_entries():
    components = component_entries()
    return components if not PLAN.exists() else components + registration_entries()


def receipt_paths():
    return sorted((ROOT / "palomar/v1").glob("*/qualification.json")) + (
        sorted((ROOT / "palomar/v2").glob("*/qualification.json")) if PLAN.exists() else [])
