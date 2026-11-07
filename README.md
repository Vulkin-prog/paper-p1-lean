# P1 — Lean formalization

*Sharp Poisson approximation and second-order correction for long multiplicative
runs*, and its technical companion, by [Brice Pouly](https://orcid.org/0009-0008-8491-2467).

Current checkpoint P1-MATH-0985: all **167 revised numbered statements** have
checked proofs, using **Lean v4.36.0-rc2**, with no unformalized mathematical
input. This comprises all 73 main-article and all 94 revised companion results.
The separate version 1.7 manuscript draft integrates the two necessary statement
corrections and the internally proved logarithmic smooth-window census.

| Manuscript | PDF | Editable source |
|---|---|---|
| Article, version 1.7 draft | [PDF](manuscripts/paper-p1/v1.7/pdf/P1_V1_7_Main_Article_2026-11-07_EN.pdf) | [TeX](manuscripts/paper-p1/v1.7/sources/main.tex) |
| Technical companion, version 1.7 draft | [PDF](manuscripts/paper-p1/v1.7/pdf/P1_V1_7_Technical_Companion_2026-11-07_EN.pdf) | [TeX](manuscripts/paper-p1/v1.7/sources/companion.tex) |
| Preserved original version 1.6 | [Original package](manuscripts/paper-p1/v1.6/) | [Provenance](manuscripts/paper-p1/v1.6/PROVENANCE.json) |

These are working manuscript versions. No publication DOI or Palomar registration
identifier is asserted.

## Mathematical scope and corrections

The development proves the optimal quadratic Poisson–Charlier approximation,
its exact-mean and nominal-mean comparisons, the residue-dependent Poisson
scale, weighted arithmetic profiles, fixed and growing moment estimates,
information-sensitive conditioning, and deterministic and randomized
private-forcing obstructions. Exact heterogeneous marginals, affine
incompatibility, repeated indices and quantifier order are retained.

The version 1.6 baseline remains **165 proved, 0 conditional and 2 in_progress**.
Its two remaining literal statements are false as printed: companion T1.10
needs an alignment radius matching the old enclosing interval, and T5.1 needs
the trivial exponent cap for its universal exact comparison. Their original
bytes and checked counterexamples are preserved. Their corrected replacements
are proved and integrated in version 1.7. T19.17 is proved with both original
coefficients and without an external smooth-number premise.

The ledger records **983 confirmed mathematical improvements and two statement-scope corrections**.
Proof substitutions, exact parameter ranges and the scope of stronger
unasserted analytic or geometric results are documented in the source revision.

| Review material | Record |
|---|---|
| Revised 167-statement correspondence | [Revised ledger](docs/manuscript-results-v1.7.json) |
| Original statement identities and proof correspondence | [Baseline alignment](docs/MANUSCRIPT_ALIGNMENT.md), [baseline ledger](docs/manuscript-results.json) |
| Source corrections and revised PDF checks | [Revision report](docs/MANUSCRIPT_REVISION_V1_7.md), [validation record](docs/manuscript-v1.7-validation.json) |
| Every mathematical correction and improvement | [Change ledger](docs/mathematical-changes.json), [narrative record](docs/MATHEMATICAL_CHANGELOG.md) |
| Current proof status and input scope | [Status](docs/FORMALIZATION_STATUS.md), [inputs](docs/LITERATURE_INPUTS.md) |
| Exact Paper C ports and licence attribution | [Reuse record](docs/PAPER_C_REUSE.md) |
| Earlier project progress | [Preserved checkpoint history](docs/README_CHECKPOINT_HISTORY.md) |

## Build and verification

The committed toolchain is `leanprover/lean4:v4.36.0-rc2`. Mathlib is pinned to
`9d581dfff2e41de989072ea63abf3daf69311520`, whose compiler version matches it.
Use the committed lockfile and the selective cache helper in scripts; all work
and temporary caches are kept on the Ubuntu partition with disk guards.

```sh
python3 scripts/check_disk.py
python3 scripts/check_revised_sources.py --require-proved
python3 scripts/update_audit.py --check
lake build
lake env lean Audit.lean > axiom-audit.txt
python3 scripts/check_axioms.py axiom-audit.txt
python3 scripts/check_disk.py
```

The audit discovers every substantive theorem and Solution wrapper from source,
then invokes Lean's own axiom report for each declaration. Only `propext`,
`Classical.choice` and `Quot.sound` are permitted. Proofs contain no placeholders.
Standalone registry Challenges have only the deliberate selected statement
holes and are never imported by the proof development or its audit.

The latest complete project replay for the first five candidate families passed
**18,547 build jobs** and **19,341 theorem axiom checks**. Each mathematical
checkpoint and registry replay records its own exact source commit and scope.

## Palomar preparation

Five selected families have passed local statement comparison and both Lean and
NanoDa, with bubblewrap isolation enabled:

| Family | Selected declarations | Local evidence |
|---|---:|---|
| Ordinary smooth integers in logarithmic intervals | 3 | [Receipt](palomar/v1/smooth_windows/qualification.json) |
| Prescribed squarefree kernels of shifted split products | 4 | [Receipt](palomar/v1/quadratic_kernels/qualification.json) |
| Asymmetric parity-space profiles | 3 | [Receipt](palomar/v1/asymmetric_profiles/qualification.json) |
| Optimal quadratic Poisson–Charlier approximation | 4 | [Receipt](palomar/v1/quadratic_approximation/qualification.json) |
| Exact Poisson scales and quantized mean bias | 5 | [Receipt](palomar/v1/poisson_scales/qualification.json) |

The [candidate interfaces](palomar/v1/README.md) link each standalone Mathlib-only
Challenge, complete Solution, Comparator configuration, metadata and preserved
logs. Selected declaration counts describe registration candidates, separately
from the complete 167-result manuscript correspondence. Further families and
the complete pinned reusable Palomar workflow remain in preparation. No registry
submission, editorial decision or permanent registration is claimed.

For an individual local comparison, the pinned toolchain supplies all checkers:

```sh
lake env lake comparator --config comparator/p1_smooth_windows.json
```

## Licence and assistance

The Lean development uses [Apache-2.0](LICENSE). Ported Paper C material retains
its exact source attribution and was rebuilt with the new compiler. Manuscript
provenance and authorship remain in the manuscript packages. Agent assistance
and review are disclosed in the manuscript and candidate metadata; they do not
constitute independent human peer review.
