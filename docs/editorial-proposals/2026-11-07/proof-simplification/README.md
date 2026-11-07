# Third simplification pass: SIM12 and coupled SIM13

All thirteen proposals in the [independent review](../../../reviews/2026-11-07/simplification-review.json)
are now applied in a separate marked review copy. The [first pass](../simplification/README.md),
[second pass](../structural-simplification/README.md) and all versions 1.6-1.8
remain preserved. This is not an adopted manuscript version; Palomar stays on hold.

| Document | Frozen v1.8 | First condensed | Structural | Latest simplified |
|---|---:|---:|---:|---:|
| Article | 65 | 65 | 64 | 64 |
| Companion | 104 | 103 | 102 | 101 |
| Total | 169 | 168 | 166 | 165 |

The measured gain is four PDF pages from frozen v1.8. This pass saves 132 physical
source lines, including the short reading route and conventions; the three
passes save 277 relative to the stage after the five earlier clarifications.
Those earlier additions mean that this is not a net-line comparison with v1.8.

## What the shorter proofs require

- **SIM12, T1.14:** choose s nonzero effective projections and fix the other
  centres. The existing conditional half count gives the stronger intermediate
  power N^(r-s/2+epsilon), hence the retained printed estimate. Images may vanish
  modulo the old space, but cannot be zero in their own effective spaces.
- **SIM13, T4.3:** the regular-set convention makes the exact marginals p_x=p.
  Apply 15.5 and multiply by the fixed factor r! for ordered tuples. The proof
  goes from 146 lines to 10.
- **SIM13, T4.4:** the compressed proof is replaced at the same time. Its single
  normalized source centre is counted injectively by 10.1. For at least three
  original targets use the half count and rho<=L. For two targets split at L/4,
  then use the independent dense two-target estimate and the homogeneous source
  sum. Keep q0(e) even for affine-incompatible sources. The one-target clause and
  its seed/Palm argument are preserved verbatim. This proof remains 46 lines;
  the gain comes from removing the geometric duplication in T4.3.

The source bound used now is q0(e)<=N^(-kappa_b+epsilon), already established.
The old good/private constant-loss rank observation is not asserted false;
it is unnecessary for this shorter argument. Both the finite source count and
the point bound precede the sum. The source pair is not treated as two free centres.

The reading guide explicitly routes the reader to 10.1, 15.2 and 15.5. These
geometric proofs do not use the moment theorem, T4.3 or either reconstruction
of the law. T4.1/T4.2, the small-kernel inputs, T14-T17 and all positional and
growing-order results remain. No original-window envelope is silently applied
to compressed windows.

## Statement and label changes

All 167 result identities and actual printed result numbers are preserved.
Two numbered blocks only make inherited conventions explicit: distinct original
windows in 7.2, and 6bB<=H<=DB with fixed D>=6b in the fixed-height branch of T1.9.
The other 165 blocks are byte-identical to the structural preview. Relative to
frozen v1.8, 164 blocks are unchanged; the third clarification is the earlier
H=C_D B reminder in 15.4. These are recorded scope precisions, not newly false
original formulations.

The projective/Hilbert encoding of 13.4 is already described in the existing
endpoint index. The formal/effective-kernel distinction of T22.7 is already in
the earlier clarified preview, with its full propagation and moment clauses.
Those explanations are not duplicated for line-count purposes.

Four equation labels belonged only to the removed T4.3 proof. Their equations
and labels are removed together, never reassigned to different formulas:

| Former label | Former role | References outside removed proof / remaining |
|---|---|---:|
| p1:fixed:group-tail | Large-group host count N^(r-9/5+epsilon) | 0 / 0 |
| p1:fixed:component-kernel | Truncated-kernel bound after group omission | 0 / 0 |
| p1:fixed:high-hosts | Dense host count N^(r-3/2+epsilon) | 0 / 0 |
| p1:fixed:very-high-hosts | Very dense host count N^(r-9/5+epsilon) | 0 / 0 |

There are 548 label occurrences instead of 552. Subsequent T4 equation numbers
change naturally; all retained references are rebuilt. No result label is removed.

## Evidence and limits

The [patch](last-proof-cuts.patch) applies exactly to the structural sources
at `bc9517fc5a685135722fe4a4231c16f6bf67e796`.
The [initial patch receipt](patch-validation.json) is frozen with its historical
pending status. The [final receipt](final-validation.json) records completed checks.
The [conditional analysis](conditional-followup.json) explains why these options
require explicit connections. The [independent exact diff review](independent-patch-review.json)
reads the actual bodies and types and reports no confirmed gap or required correction.
It is AI-assisted review, not human certification.

Thirty existing declarations were actually re-extracted under Lean 4.36.0-rc2:
[inventory](scope-declarations.json), [types](scope/compiled-types.json),
[type/axiom receipt](scope/compiled-types-validation.json), [log](scope/compiled-types.log)
and [actual exit](scope/compiled-types.exit). They include 29 audited propositions
and one separately described conclusion definition. Only standard axioms occur.
No Lean source or theorem is added. The proof source remains 7bfc953c and the
full checkpoint 1004 replay remains the last complete build/audit/reference replay.
The 1004-entry development ledger is unchanged.

All 165 pages were rendered and visually checked in eleven contact sheets;
26 complete pages were inspected in detail, without observed layout defects.
Six LaTeX executions succeeded in three alternating rounds, with no undefined
references, overfull boxes or missing glyphs. Raw logs are retained byte-for-byte
as gzip files. The reviewer did not claim to run Lean or inspect these PDFs.

Frozen reports retain their original absolute work paths. Identical input bytes
are supplied here; apply the patch to its base to reproduce the scientific copy.
The delivered copy changes only three root files for preview dates, footers,
metadata and cross-PDF filenames. For this preview use the reconstruction
instructions below; the v1.8 builder named in the retained guide rebuilds frozen
v1.8, not this separate review copy.

## Deliverables

- [Article PDF](../../../../manuscripts/paper-p1/editorial-simplified-preview-2026-11-07/pdf/P1_Simplified_Editorial_Preview_Main_2026-11-07_EN.pdf)
- [Companion PDF](../../../../manuscripts/paper-p1/editorial-simplified-preview-2026-11-07/pdf/P1_Simplified_Editorial_Preview_Companion_2026-11-07_EN.pdf)
- [Editable sources](../../../../manuscripts/paper-p1/editorial-simplified-preview-2026-11-07/sources/)
- [French description and reconstruction](../../../../manuscripts/paper-p1/editorial-simplified-preview-2026-11-07/LISEZMOI.txt)
- [All 167 result source bindings](preview-result-map.json)
- [All 13 proposals and their integration stages](../integration-status.json)
- [Build record](../../../../manuscripts/paper-p1/editorial-simplified-preview-2026-11-07/validation/build-validation.json)
- [Completed visual inspection](../../../../manuscripts/paper-p1/editorial-simplified-preview-2026-11-07/validation/visual-review.json)
