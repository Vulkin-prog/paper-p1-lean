# Initialization verification — 31 October 2026

The local checks below passed before the initial source push:

| Check | Observed result |
|---|---|
| Compiler | Lean 4.36.0-rc2, commit `b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a` |
| Mathlib | `9d581dfff2e41de989072ea63abf3daf69311520` (tag `v4.36.0-rc2`) |
| Dependency resolution | Successful; all revisions recorded in `lake-manifest.json` |
| Source integrity | 138 original manifest entries verified; provenance covers 140 original imported files |
| Statement inventory | All 167 source blocks match the supplied statement baseline and coverage ledger |
| Build | `lake build` passed with warnings treated as errors |
| Axiom audit | All five auxiliary lemmas use only `propext`, `Classical.choice`, `Quot.sound` |
| Disk location | Repository on the Ubuntu root partition |
| Disk reserve after dependencies/build | Approximately 22.51 GiB available |

The [raw initial axiom output](INITIAL_AXIOM_AUDIT.txt) is preserved. Regenerate
the check with `lake env lean Audit.lean` and validate the output using
`python3 scripts/check_axioms.py PATH_TO_OUTPUT`.

The initial cache download selected only the imports needed for the centering
module. The Mathlib power-set sum helper was built locally from the locked
source. The GitHub workflow selects that helper explicitly for clean checkouts.

These checks establish the source identities, dependency pins and five checked
auxiliary declarations. They do not prove any of the 167 numbered manuscript
statements, the stochastic interpretation of the transform, or the asymptotic
theorems. None of the original manuscript build or diagnostic scripts was run.

The GitHub Actions result for the pushed commit is recorded by GitHub's workflow
history; this local report alone does not assert a successful remote run.
