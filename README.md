# P1 — Lean formalization

*Sharp Poisson approximation and second-order correction for long multiplicative
runs*, and its technical companion, by [Brice Pouly](https://orcid.org/0009-0008-8491-2467).

Current checkpoint P1-MATH-1005: all **167 revised numbered statements** have
checked proofs, using **Lean v4.36.0-rc2**, with no unformalized mathematical
input. This comprises all 73 main-article and all 94 revised companion results.
The separate version 1.8 working draft integrates the two necessary statement
corrections, selected stronger estimates and the internally proved logarithmic
smooth-window census. Versions 1.6 and 1.7 remain preserved.
The [optional finite-rank certificate](docs/EXACT_RANK_EXAMPLE.md) proves
rank exactly 10, two forcing samples and mass 2^-10 at N=18,q=3. It
preserves the already delivered v1.8 sources and PDFs.
The [fixed-cutoff tail interface](docs/FIXED_CUTOFF_INDEPENDENT_TAIL.md)
also makes the size cutoff precede epsilon in article15.8, for both
original families and an arbitrary fixed bounded-width block.
The [complete proof and clause index](docs/MANUSCRIPT_ENDPOINTS_V1_8.md)
locates all 167 results through 261 actual compiled theorem interfaces.
It records printed premises, inherited context and the new exact
[replica/homogeneous interfaces](docs/REPLICA_AND_HOMOGENEOUS_INTERFACES.md).
The [concrete irregular-window examples](docs/IRREGULAR_WINDOW_EXAMPLES.md)
certify why the two kernel meanings and the two event masses must remain distinct.
A [common fixed-arity envelope](docs/FIXED_ARITY_HOMOGENEOUS_ENVELOPE.md)
now exposes the actual homogeneous bounds and a shared short proof for four weights.
An [independent simplification review](docs/editorial-proposals/2026-11-07/simplification/README.md)
records 13 proposals. The first eight are applied in a separate marked preview:
120 source lines removed, all 167 numbered blocks retained, and one PDF page saved.
A [second structural pass](docs/editorial-proposals/2026-11-07/structural-simplification/README.md)
applies three more proposals, yielding 64 article pages and 102 companion pages:
three fewer pages than frozen v1.8, with all 167 numbered blocks and 552 labels
preserved from the first condensed stage. Both prior previews remain available.
The [third proof-simplification pass](docs/editorial-proposals/2026-11-07/proof-simplification/README.md)
applies the two remaining proposals together with two inherited-scope precisions.
That third marked review copy has 64 article pages and 101 companion pages,
four fewer than frozen v1.8. All 167 result identities and numbers are retained.
The [integration index](docs/editorial-proposals/2026-11-07/integration-status.json)
distinguishes all thirteen applied proposals from the preserved proof-development ledger.
The [editorial integrity gate](docs/validation/editorial-preview-integrity/README.md)
checks the exact reviewed patch chain, delivered artifacts and complete result
bundles in CI, with 29 in-memory controls.

The [sharp positive Palm bridge](docs/SHARP_GOOD_EDGE_PALM.md) exposes
the normalized powers 7/10 and 37/60 in the two retained channels. Its complete
pinned replay and independent four-body/type review passed. A common seed
proof is now used in the separate unified preview below; all earlier
manuscript copies and the six registry scopes remain preserved.

The [preserved strengthened review copy](docs/editorial-proposals/2026-11-07/scientific-strengthening/README.md)
also exposes existing sharper bounds in T9.1, T1.14 and T4.4, with an explicit
positive homogeneous one-target argument and a separate logarithmic-exponent note.
It retains all thirteen simplifications and remains 64/101 pages. Fifteen
existing proposition types were actually extracted; an exact independent diff
review and twelve integrity controls accompany the copy. No new theorem or
ledger entry is counted, and all earlier sources/PDFs/reports remain preserved.



The [latest unified review copy](docs/editorial-proposals/2026-11-07/common-seed-simplification/README.md)
uses one common positive seed argument in four proofs. It removes another 51
physical source lines and strengthens T1.12, while preserving all 167 result
identities, 548 labels, the earlier 13 simplifications and five scientific
dispositions. It remains 64/101 pages. Twenty-one existing propositions were
actually extracted and independently read. The exact diff, visual review,
result map and eight integrity controls are included; no new theorem is counted.

The separate review instance has now directly compared all 167 numbered-result
labels across its frozen source snapshots; the [complete review index](docs/MANUSCRIPT_ENDPOINTS_V1_8.md)
records every clause and inherited premise.

| Manuscript | PDF | Editable source |
|---|---|---|
| Article, latest unified editorial preview | [PDF](manuscripts/paper-p1/editorial-unified-preview-2026-11-07/pdf/P1_Unified_Editorial_Preview_Main_2026-11-07_EN.pdf) | [TeX](manuscripts/paper-p1/editorial-unified-preview-2026-11-07/sources/main.tex) |
| Companion, latest unified editorial preview | [PDF](manuscripts/paper-p1/editorial-unified-preview-2026-11-07/pdf/P1_Unified_Editorial_Preview_Companion_2026-11-07_EN.pdf) | [TeX](manuscripts/paper-p1/editorial-unified-preview-2026-11-07/sources/companion.tex) |
| Article, preserved strengthened editorial preview | [PDF](manuscripts/paper-p1/editorial-strengthened-preview-2026-11-07/pdf/P1_Strengthened_Editorial_Preview_Main_2026-11-07_EN.pdf) | [TeX](manuscripts/paper-p1/editorial-strengthened-preview-2026-11-07/sources/main.tex) |
| Companion, preserved strengthened editorial preview | [PDF](manuscripts/paper-p1/editorial-strengthened-preview-2026-11-07/pdf/P1_Strengthened_Editorial_Preview_Companion_2026-11-07_EN.pdf) | [TeX](manuscripts/paper-p1/editorial-strengthened-preview-2026-11-07/sources/companion.tex) |
| Article, preserved simplified editorial preview | [PDF](manuscripts/paper-p1/editorial-simplified-preview-2026-11-07/pdf/P1_Simplified_Editorial_Preview_Main_2026-11-07_EN.pdf) | [TeX](manuscripts/paper-p1/editorial-simplified-preview-2026-11-07/sources/main.tex) |
| Companion, preserved simplified editorial preview | [PDF](manuscripts/paper-p1/editorial-simplified-preview-2026-11-07/pdf/P1_Simplified_Editorial_Preview_Companion_2026-11-07_EN.pdf) | [TeX](manuscripts/paper-p1/editorial-simplified-preview-2026-11-07/sources/companion.tex) |
| Article, separate structural editorial preview | [PDF](manuscripts/paper-p1/editorial-structural-preview-2026-11-07/pdf/P1_Structural_Editorial_Preview_Main_2026-11-07_EN.pdf) | [TeX](manuscripts/paper-p1/editorial-structural-preview-2026-11-07/sources/main.tex) |
| Companion, separate structural editorial preview | [PDF](manuscripts/paper-p1/editorial-structural-preview-2026-11-07/pdf/P1_Structural_Editorial_Preview_Companion_2026-11-07_EN.pdf) | [TeX](manuscripts/paper-p1/editorial-structural-preview-2026-11-07/sources/companion.tex) |
| Article, separate condensed editorial preview | [PDF](manuscripts/paper-p1/editorial-condensed-preview-2026-11-07/pdf/P1_Condensed_Editorial_Preview_Main_2026-11-07_EN.pdf) | [TeX](manuscripts/paper-p1/editorial-condensed-preview-2026-11-07/sources/main.tex) |
| Companion, separate condensed editorial preview | [PDF](manuscripts/paper-p1/editorial-condensed-preview-2026-11-07/pdf/P1_Condensed_Editorial_Preview_Companion_2026-11-07_EN.pdf) | [TeX](manuscripts/paper-p1/editorial-condensed-preview-2026-11-07/sources/companion.tex) |
| Article, version 1.8 working draft | [PDF](manuscripts/paper-p1/v1.8/pdf/P1_V1_8_Main_Article_2026-11-07_EN.pdf) | [TeX](manuscripts/paper-p1/v1.8/sources/main.tex) |
| Technical companion, version 1.8 working draft | [PDF](manuscripts/paper-p1/v1.8/pdf/P1_V1_8_Technical_Companion_2026-11-07_EN.pdf) | [TeX](manuscripts/paper-p1/v1.8/sources/companion.tex) |
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

The historical development ledger contains **1005 entries: 1003 proof improvements and two statement-scope corrections**. These are documented proof-development steps, not 1003 independent manuscript amendments. See the [grouped review guide](docs/editorial-proposals/2026-11-07/HISTORICAL_CHANGE_GUIDE.md). That frozen guide covers the first 1004 checkpoints; the new Palm bridge is documented separately.
Proof substitutions, exact parameter ranges and the scope of stronger
unasserted analytic or geometric results are documented in the source revision.

| Review material | Record |
|---|---|
| Version 1.8 strengthened statements and editorial integration | [Revision report](docs/MANUSCRIPT_REVISION_V1_8.md), [167-result ledger](docs/manuscript-results-v1.8.json), [validation](docs/manuscript-v1.8-validation.json) |
| Revised 167-statement correspondence | [Revised ledger](docs/manuscript-results-v1.7.json) |
| Original statement identities and proof correspondence | [Baseline alignment](docs/MANUSCRIPT_ALIGNMENT.md), [baseline ledger](docs/manuscript-results.json) |
| Source corrections and revised PDF checks | [Revision report](docs/MANUSCRIPT_REVISION_V1_7.md), [validation record](docs/manuscript-v1.7-validation.json) |
| Every mathematical correction and improvement | [Change ledger](docs/mathematical-changes.json), [narrative record](docs/MATHEMATICAL_CHANGELOG.md) |
| Current proof status and input scope | [Status](docs/FORMALIZATION_STATUS.md), [inputs](docs/LITERATURE_INPUTS.md) |
| Independent mathematical and editorial review | [French report](docs/reviews/2026-11-07/RAPPORT_FR.txt), [exact signatures and proposals](docs/reviews/2026-11-07/review.json), [subsequent corrections](docs/reviews/2026-11-07/disposition.json) |
| Latest complete clause review and remaining editorial proposals | [167-result index](docs/MANUSCRIPT_ENDPOINTS_V1_8.md), [editorial handoff](docs/EDITORIAL_HANDOFF_AFTER_ENDPOINT_REVIEW.md), [source-bound validation](docs/validation/manuscript-endpoints-v1.8/README.md) |
| Concrete proposed TeX edits, checked on a copy | [Five proposals in four files](docs/editorial-proposals/2026-11-07/README.md), [separate review](docs/editorial-proposals/2026-11-07/independent-review.json) |
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

The [exact bivariate reference law](docs/POSITIONAL_BIVARIATE_LAW.md) gives the three-arrival representation, admissible shared covariance and finite point probabilities, including diagonal and zero-rate cases. Its complete replay passed; the [source-bound logs](docs/validation/checkpoint-0997/validation.json) preserve all three checks. The clarification is integrated in the revised companion appendix.

## Build and verification

The committed toolchain is `leanprover/lean4:v4.36.0-rc2`. Mathlib is pinned to
`9d581dfff2e41de989072ea63abf3daf69311520`, whose compiler version matches it.
Use the committed lockfile and the selective cache helper in scripts; all work
and temporary caches are kept on the Ubuntu partition with disk guards.

```sh
python3 scripts/check_disk.py
python3 scripts/check_manuscript_endpoints.py
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

The latest complete project replay with all six consolidated registrations and
seventeen preserved components passed **18,631 build jobs**, **19,995 theorem axiom checks**
and **19,918 distinct reference checks**, all actual exits zero, at
[source d342b507](https://github.com/Vulkin-prog/paper-p1-lean/commit/d342b507332315c67b1463009061c03f14b5be9b).
The substantive mathematical inventory contains **19,567 theorems**; the remaining
428 are complete component and consolidated Solution wrappers. Each mathematical
checkpoint and registry replay records its own exact source commit and scope.
The [evidence checker](scripts/check_registry_evidence.py) validates every
preserved receipt against its historical inventory and current proof imports.

## Palomar preparation

The target is **six registrations in total**, with **one entire submission cycle at a time**. They preserve all **68 selected statements** from the seventeen locally qualified component families; the complete manuscript correspondence remains **167 proved numbered results**.

**Submissions are on hold at the user's request (7 November 2026)** while the
article and companion receive independent mathematical and editorial review.
No full Palomar workflow, intake or registration has been launched.

| Order | Registration | Selected declarations | Configuration and metadata |
|---:|---|---:|---|
| 1 | Arithmetic and geometry | 12 | [configuration](comparator/registrations/p1_arithmetic_geometry.json), [metadata](palomar/v2/arithmetic_geometry/formalization.yaml) |
| 2 | Arithmetic profiles and smooth logarithmic windows | 6 | [configuration](comparator/registrations/p1_profiles_smooth.json), [metadata](palomar/v2/profiles_smooth/formalization.yaml) |
| 3 | Finite affine structure, conditioning and dependent expansions | 12 | [configuration](comparator/registrations/p1_affine_conditioning.json), [metadata](palomar/v2/affine_conditioning/formalization.yaml) |
| 4 | Factorial cumulants, moments and private obstructions | 14 | [configuration](comparator/registrations/p1_cumulants_obstructions.json), [metadata](palomar/v2/cumulants_obstructions/formalization.yaml) |
| 5 | Poisson approximation, scales and positional reference fields | 16 | [configuration](comparator/registrations/p1_poisson_fields.json), [metadata](palomar/v2/poisson_fields/formalization.yaml) |
| 6 | Exponential moments and prime cylinders | 8 | [configuration](comparator/registrations/p1_exponential_cylinders.json), [metadata](palomar/v2/exponential_cylinders/formalization.yaml) |

The [explicit plan](palomar/REGISTRATION_PLAN.json) records every original-to-consolidated declaration, all component source hashes and the strict serial policy. The original [seventeen component interfaces and receipts](palomar/v1/README.md) remain separate proof evidence; they are not seventeen planned submissions. All six consolidated pairs passed standalone comparison and all six local checkers,
then frozen-root Lean/NanoDa qualification. The [six-registration overview](palomar/v2/README.md)
links their receipts and the complete source-bound project replay.

All six metadata files associate **[Brice Pouly](https://orcid.org/0009-0008-8491-2467)** with GitHub `Vulkin-prog` and **ORCID `0009-0008-8491-2467`** in structured author, maintainer and paper-source records accepted by the pinned official Palomar parser.

The [single workflow caller](.github/workflows/palomar-preflight.yml) selects exactly one registration and uses the exact pinned full Palomar pipeline and standard profile. The previous multi-family callers are preserved as [historical source material](palomar/v1/historical-workflows/). The workflow mutex covers its execution; the operator must also finish intake, private editorial review, the human decision, and registration or documented closure before starting the next dossier.

The earlier request concerning fifteen configurations at source `0a9d3e68a8af39b6ea1ce725027f72ca5f10e8c4` is superseded by this six-registration scope. No personal relationship attestation, full workflow dispatch, intake, editorial decision or permanent registry entry is claimed. The [procedure](docs/PALOMAR_PLAN.md) states the remaining stages.

For one individual local comparison:

```sh
lake env lake comparator --config comparator/registrations/p1_profiles_smooth.json
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
original component sources and receipts remain preserved; this family is
included in the consolidated Poisson-fields registration. The original exponent 4/5 and all 167 numbered statements are unchanged.


The [exact reference-arrival marginals](docs/POSITIONAL_ARRIVAL_MARGINALS.md)
identify each site with Poisson(p_x), for arbitrary finite packets and every
independent realization, without an ambient configuration countability input.
Every factorial test is integrable with expectation p_x^j. The original
arithmetic approximation retains its exponent and fixed-degree scope. Its complete replay passed; [the source-bound logs](docs/validation/checkpoint-0993/validation.json) preserve all three checks. The clarification is integrated in the revised companion appendix.


The Poisson-reference family packages four exact finite-product statements:
all integrable factorial tests and marginal laws, the full covariance matrix,
sharp natural-count independence, and the complete dependency-graph property
for disjoint blocks. Its [frozen-root qualification](palomar/v1/poisson_reference/qualification.json)
and verified con-ron replay passed. The [standalone six-checker report](palomar/v1/supplementary/poisson-reference-draft-checks.json)
preserves the exact earlier proof base and byte-identical source files.
This packages checkpoints 993--996 without a new mathematical-change entry.
The consolidated Poisson-fields registration contains this family and the
positional comparison, quadratic approximation and Poisson scales. The overall
target remains six registrations, submitted through complete successive cycles.
