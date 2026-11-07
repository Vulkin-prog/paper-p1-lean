#!/usr/bin/env python3
"""Check the output of Lean's #print axioms for the selected declarations."""

from pathlib import Path
import re
import sys

from update_audit import discover_names, inventory_content, render

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
ROOT = Path(__file__).resolve().parents[1]
names = discover_names()
if (ROOT / "Audit.lean").read_text() != render(names):
    raise SystemExit("The audit command does not match its generated source inventory")
if (ROOT / "docs/axiom-audit-declarations.json").read_text() != inventory_content(names):
    raise SystemExit("The audit inventory does not match the project theorem sources")
EXPECTED = set(names)
if not EXPECTED:
    raise SystemExit("The axiom-audit selection is empty")

text = Path(sys.argv[1]).read_text()
found = set()
pattern = re.compile(
    r"^'(.+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)$",
    re.M,
)
for match in pattern.finditer(text):
    name, axioms = match.groups()
    found.add(name)
    actual = {a.strip() for a in (axioms or "").split(",") if a.strip()}
    if actual - ALLOWED:
        raise SystemExit(f"Unexpected axioms for {name}: {actual - ALLOWED}")
if found != EXPECTED:
    raise SystemExit(f"Audit selection mismatch: missing={EXPECTED - found}, extra={found - EXPECTED}")
print(f"Axiom check passed for {len(found)} declarations.")
