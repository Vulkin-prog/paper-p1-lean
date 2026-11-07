# P1 — Lean formalization

*Sharp Poisson approximation and second-order correction for long multiplicative
runs*, and its technical companion, by [Brice Pouly](https://orcid.org/0009-0008-8491-2467).

Current checkpoint P1-MATH-0996: all **167 revised numbered statements** have
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

The ledger records **994 confirmed mathematical improvements and two statement-scope corrections**.
Proof substitutions, exact parameter ranges and the scope of stronger
unasserted analytic or geometric results are documented in the source revision.

| Review material | Record |
|---|---|
| Revised 167-statement correspondence | [Revised ledger](docs/manuscript-results-v1.7.json) |
| Original statement identities and proof correspondence | [Baseline alignment](docs/MANUSCRIPT_ALIGNMENT.md), [baseline ledger](docs/manuscript-results.json) |
| Source corrections and revised PDF checks | [Revision report](docs/MANUSCRIPT_REVISION_V1_7.md), [validation record](docs/manuscript-v1.7-validation.json) |
| Every mathematical correction and improvement | [Change ledger](docs/mathematical-changes.json), [narrative record](docs/MATHEMATICAL_CHANGELOG.md) |
| Current proof status and input scope | [Status](docs/FORMALIZATION_STATUS.md), [inputs](docs/LITERATURE_INPUTS.md) |
| Printed statements, compiled types and explicit hypotheses | [Scope index](docs/NUMBERED_SCOPE_REVIEW.md) |
| Exact Paper C ports and licence attribution | [Reuse record](docs/PAPER_C_REUSE.md) |
| Earlier project progress | [Preserved checkpoint history](docs/README_CHECKPOINT_HISTORY.md) |

The [one-sided prime-cylinder strengthening](docs/ONE_SIDED_PRIME_CYLINDER.md)
proves the sharper finite start count N/q-N/q^2-3 and corresponding positive
and total exponential-moment lower bounds. Its full replay passed; the [source-bound evidence](docs/validation/checkpoint-0986/validation.json) preserves all three checks. No numbered statement changes.

The [supported prime-cylinder refinement](docs/SUPPORTED_PRIME_CYLINDER.md) reduces the probability charge to primeCount(2*q*floor(N/q)). Its complete replay passed; the [source-bound logs](docs/validation/checkpoint-0987/validation.json) preserve all three checks. The refinement is integrated in the revised companion appendix.

The [exact valuation refinement](docs/VALUATION_PRIME_CYLINDER.md) retains all positive multipliers with even q-adic valuation, including additional forced starts. Its complete replay passed; [the source-bound logs](docs/validation/checkpoint-0988/validation.json) preserve all three checks. The refinement is integrated in the revised companion appendix.

The [finite-depth valuation bounds](docs/VALUATION_LAYER_BOUNDS.md) give the explicit budget N/(q+1)*(1-q^(-2*k))-3*k for every finite depth. Its complete replay passed; [the source-bound logs](docs/validation/checkpoint-0989/validation.json) preserve all three checks. The refinement is integrated in the revised companion appendix.

The [effective retained-start density](docs/VALUATION_DENSITY_BOUNDS.md) chooses a complete logarithmic layer depth, proves a two-sided finite count and identifies its leading density 1/(q+1), with an error tending to zero uniformly over primes q<=N. Its complete replay passed; [the source-bound logs](docs/validation/checkpoint-0990/validation.json) preserve all three checks. The refinement is integrated in the revised companion appendix.

The [rank-charged forcing event](docs/RANK_CHARGED_PRIME_CYLINDER.md) replaces a full prime assignment by the actual compatible affine fiber. Both full moments inherit the effective-rank cost; the five-start example N=18,q=3 proves a factor-two gain. Its complete replay passed; [the source-bound logs](docs/validation/checkpoint-0991/validation.json) preserve all three checks. The refinement is integrated in the revised companion appendix.

The [independent positional realization](docs/INDEPENDENT_POSITIONAL_REALIZATION.md) constructs the literal single/pair Poisson arrivals and proves their exact target law. Every independent realization, including the concrete product law, has the original convergent weighted grid comparison. Its complete replay passed; [the source-bound logs](docs/validation/checkpoint-0992/validation.json) preserve all three checks. The clarification is integrated in the revised companion appendix.

The [exact reference covariance](docs/POSITIONAL_ARRIVAL_COVARIANCE.md) identifies the complete pair covariance matrix and the arbitrary finite-packet formula for every independent realization, including the concrete product law. Its complete replay passed; [the source-bound logs](docs/validation/checkpoint-0994/validation.json) preserve all three checks. The clarification is integrated in the revised companion appendix.

The [exact reference independence criterion](docs/POSITIONAL_ARRIVAL_INDEPENDENCE.md) proves that two reference coordinates are independent exactly when their shared arrival intensity vanishes. For pairs, the positive-rate retained edges give precisely the dependence graph, including natural counts and zero-rate cases. Its complete replay passed; [the source-bound logs](docs/validation/checkpoint-0995/validation.json) preserve all three checks. The clarification is integrated in the revised companion appendix.

The [full reference block independence](docs/POSITIONAL_BLOCK_INDEPENDENCE.md) proves independence of complete finite coordinate vectors exactly when every cross covariance vanishes. For pairs it establishes the full dependency-graph property of positive-rate retained edges and measurable block-event factorization. Its complete replay passed; [the source-bound logs](docs/validation/checkpoint-0996/validation.json) preserve all three checks. The clarification is integrated in the revised companion appendix.

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

The latest complete project replay with all sixteen candidate families passed
**18,597 build jobs** and **19,709 theorem axiom checks**. Each mathematical
checkpoint and registry replay records its own exact source commit and scope.
The [evidence checker](scripts/check_registry_evidence.py) validates every
preserved receipt against its historical inventory and current proof imports.

## Palomar preparation

Sixteen selected families have passed local statement comparison and both Lean and
NanoDa, with bubblewrap isolation enabled:

| Family | Selected declarations | Local evidence |
|---|---:|---|
| Ordinary smooth integers in logarithmic intervals | 3 | [Receipt](palomar/v1/smooth_windows/qualification.json) |
| Prescribed squarefree kernels of shifted split products | 4 | [Receipt](palomar/v1/quadratic_kernels/qualification.json) |
| Asymmetric parity-space profiles | 3 | [Receipt](palomar/v1/asymmetric_profiles/qualification.json) |
| Optimal quadratic Poisson–Charlier approximation | 4 | [Receipt](palomar/v1/quadratic_approximation/qualification.json) |
| Exact Poisson scales and quantized mean bias | 5 | [Receipt](palomar/v1/poisson_scales/qualification.json) |
| Universal arithmetic anchor obstructions | 4 | [Receipt](palomar/v1/private_obstruction/qualification.json) |
| Actual conditioning and colored replica target sums | 4 | [Receipt](palomar/v1/conditioning/qualification.json) |
| Actual factorial cumulants and the optimal third-cumulant power | 5 | [Receipt](palomar/v1/factorial_cumulants/qualification.json) |
| Fixed-order moment obstruction to a polynomial approximation rate | 5 | [Receipt](palomar/v1/moment_obstruction/qualification.json) |
| Exact expansions for dependent indicator counts | 4 | [Receipt](palomar/v1/dependent_expansion/qualification.json) |
| Degree-uniform integer points on integral curves | 3 | [Receipt](palomar/v1/integral_curve_count/qualification.json) |
| Exact finite affine spectra and canonical factorization | 4 | [Receipt](palomar/v1/affine_spectra/qualification.json) |
| Actual exponential-moment divergence for multiplicative starts | 4 | [Receipt](palomar/v1/exponential_divergence/qualification.json) |
| Uniform local arithmetic rigidity and relative-sign independence | 5 | [Receipt](palomar/v1/local_rigidity/qualification.json) |
| Effective valuation cylinders and affine-rank moment bounds | 4 | [Receipt](palomar/v1/prime_cylinders/qualification.json) |
| Convergent original-grid positional Poisson field | 3 | [Receipt](palomar/v1/positional_field/qualification.json) |

All 64 selected declarations also passed supplementary replays with verified
con-ron, Lean and NanoDa. The [source-bound reports](palomar/v1/supplementary/README.md)
preserve the actual logs, binary identities and positive/ill-typed controls.

The finite-affine family also passed [all six available local checkers](palomar/v1/supplementary/affine-spectra-six-kernels.json). Two larger representative families passed the additional optional checkers as well; each report identifies its exact source.

The exponential-moment family has four literal-model statements with explicit integrability, prime thresholds, a nontrivial odd-prime liminf and simultaneous divergence at nominal mean one. Its [standalone six-checker report](palomar/v1/supplementary/exponential-divergence-draft-checks.json) retains its exact earlier proof base; root qualification and the con-ron replay have their own immutable source.

The local-rigidity family now has its source-bound root qualification and con-ron replay. Its separately scoped [standalone six-checker report](palomar/v1/supplementary/local-rigidity-draft-checks.json) preserves all five statements, 13 audited theorem/bridge declarations and the earlier proof base.

The finite valuation-cylinder family has four literal-model statements, its frozen-root Lean/NanoDa qualification and a verified con-ron replay. Its separately scoped [standalone six-checker report](palomar/v1/supplementary/prime-cylinders-draft-checks.json) preserves thirteen direct theorem/bridge audits and the exact earlier proof base.

The [candidate interfaces](palomar/v1/README.md) link each standalone Mathlib-only
Challenge, complete Solution, Comparator configuration, metadata and preserved
logs. Selected declaration counts describe registration candidates, separately
from the complete 167-result manuscript correspondence. The exact-pinned
[complete reusable workflow](.github/workflows/palomar-preflight.yml) is ready
for the original seven families, and an [additional caller](.github/workflows/palomar-preflight-additional.yml)
selects the additional families. Both run one family at a time. Their personal
authorization declaration must be confirmed before dispatch. No registry
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


The positional-field family selects three original-model statements: uniform
single-rate positivity, the convergent weighted grid comparison for every
independent Poisson realization, and its canonical product realization. Its
[frozen-root qualification](palomar/v1/positional_field/qualification.json)
and verified con-ron replay passed. The separately scoped
[standalone six-checker report](palomar/v1/supplementary/positional-field-draft-checks.json)
preserves twelve direct proof audits and the exact earlier proof base. The
original two workflow callers are preserved; a separate caller selects this
family. The original exponent 4/5 and all 167 numbered statements are unchanged.


The [exact reference-arrival marginals](docs/POSITIONAL_ARRIVAL_MARGINALS.md)
identify each site with Poisson(p_x), for arbitrary finite packets and every
independent realization, without an ambient configuration countability input.
Every factorial test is integrable with expectation p_x^j. The original
arithmetic approximation retains its exponent and fixed-degree scope. Its complete replay passed; [the source-bound logs](docs/validation/checkpoint-0993/validation.json) preserve all three checks. The clarification is integrated in the revised companion appendix.


A seventeenth [Poisson-reference candidate](palomar/v1/poisson_reference/formalization.yaml)
packages four exact statements for the explicit finite product reference law:
Poisson marginals and all integrable factorial tests; the complete pair
covariance matrix; natural-count pair independence; and genuine full-block
independence exactly when no positive-rate edge crosses between disjoint
blocks. Its eight exact bridges and four selected proofs passed the direct
axiom audit and all six local checkers on immutable standalone exports.
Frozen-root qualification is pending. This packages checkpoints 993--996
and adds no mathematical-change entry. The two earlier workflow callers
remain unchanged; the third positional caller selects the two reference
families. The pending human-relationship question for the original fifteen
configurations at source 0a9d3e68a8af39b6ea1ce725027f72ca5f10e8c4 retains
its exact scope. No complete Palomar workflow or registration is claimed.
