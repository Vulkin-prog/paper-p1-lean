#!/usr/bin/env python3
"""Check the output of Lean's #print axioms for the selected declarations."""

from pathlib import Path
import re
import sys

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
EXPECTED = {
    "PaperP1.Algebra.centeredCoefficient_empty",
    "PaperP1.Algebra.centeredCoefficient_singleton",
    "PaperP1.Algebra.centeredCoefficient_singleton_eq_zero",
    "PaperP1.Algebra.centeredCoefficient_pair",
    "PaperP1.Algebra.centeredCoefficient_pair_eq_covariance",
}

text = Path(sys.argv[1]).read_text()
found = set()
pattern = re.compile(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)")
for match in pattern.finditer(text):
    name, axioms = match.groups()
    found.add(name)
    actual = {a.strip() for a in (axioms or "").split(",") if a.strip()}
    if actual - ALLOWED:
        raise SystemExit(f"Unexpected axioms for {name}: {actual - ALLOWED}")
if found != EXPECTED:
    raise SystemExit(f"Audit selection mismatch: missing={EXPECTED - found}, extra={found - EXPECTED}")
print(f"Axiom check passed for {len(found)} auxiliary declarations.")
