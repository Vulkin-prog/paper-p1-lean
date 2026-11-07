# Second simplification pass: SIM09-SIM11

This separate marked preview applies eleven of the thirteen proposals in the
[independent simplification review](../../../reviews/2026-11-07/simplification-review.json).
The [first eight cuts](../simplification/README.md), all prior previews and versions
1.6-1.8 remain preserved. This is a review copy, not an adopted manuscript version.
Palomar submissions remain on hold.

| Document | Frozen v1.8 | First condensed preview | Current structural preview |
|---|---:|---:|---:|
| Article | 65 | 65 | 64 |
| Companion | 104 | 103 | 102 |
| Total | 169 | 168 | 166 |

The actual gain is three PDF pages from v1.8, two from the first condensed copy.
This pass saves 25 physical source lines; both simplification passes save 145
relative to the earlier clarification stage. Source-line totals do not measure
printed duplication: the shared note appears in both documents. Earlier
clarifications added explanatory material relative to frozen v1.8.

## Changes and exact scope

- **SIM09:** expose the existing algebraic scope of article 15.1 for arbitrary
  real pair coefficients. The error uses `sum |c(e)|`, not `|sum c(e)|`.
  T17.4 specializes to one pair after establishing `n>=2`, retains its displayed
  binomial expansion, and uses the independently proved covariance bound.
- **SIM10:** move each of the two original counterexample paragraphs verbatim
  beside T1.10 and T5.1. Shorten the shared correspondence note; retain the AI
  assistance statement and the distinction between formal checking and scope review.
- **SIM11:** move the full power-margin table and parameter recipe verbatim to
  the reconstruction section, leaving an introductory reference.

No new Lean theorem, exponent, numbered statement or registration selection is
introduced. The protected compressed proof and T14-T17 remain. SIM12 and SIM13
are not applied; their conditional status is preserved.

All 167 numbered statement blocks are byte-identical to the previous condensed
stage. All 552 label occurrences and all 167 actual typeset numbers are preserved.
The earlier `H=C_DB` reminder in 15.4 remains the only numbered-block clarification
relative to frozen v1.8. Both counterexamples and the margin table have one
physical copy in the scientific sources after their verbatim moves.

## Review and evidence

The [exact patch](structural-simplifications.patch) applies to the scientific
sources of the first condensed preview at documentary commit
`0f67b5432ea89fbc64adb0ee4ea44e72370c195b`.
Its [initial receipt](patch-validation.json) deliberately retains its historical
pending status. The [final receipt](final-validation.json) records the completed
independent diff review, compilation and visual inspection.

The [preliminary review](preliminary-review.json) and
[exact diff review](independent-patch-review.json) are frozen outputs from the
separate AI instance. It read the diff, five existing proof bodies and their
actual compiled types; no mathematical gap or necessary correction was found.
This is AI-assisted review, not independent human certification.

The [five declarations](scope-declarations.json) were actually extracted under
Lean 4.36.0-rc2: [compiled types](scope/compiled-types.json),
[axiom/type receipt](scope/compiled-types-validation.json),
[log](scope/compiled-types.log), [actual exit](scope/compiled-types.exit).
The proof source remains `7bfc953cd6092eebfbae5f24aeb72b7180693537`, whose complete
checkpoint 1004 replay passed 18,629 build jobs, 19,991 axiom checks and 19,914
distinct references. No proof source is changed by this pass.

Frozen reviews retain their original absolute work paths. Their identical bytes
are supplied here: `proposal/` maps to this directory, `scope/` to the local scope
directory, and the manifest to [scientific-sources-manifest.json](scientific-sources-manifest.json).
That scientific source state is reproduced by applying the exact patch to the
base sources. The delivered sources differ only in the three root files used
for preview dates, footers, PDF metadata and cross-PDF filenames.

The two PDFs compiled in three alternating rounds (six successful executions),
followed by one successful metadata-only companion pass. That follow-up changed
no auxiliary bytes or page counts. All 166 pages were rendered and examined in
eleven contact sheets; 44 complete pages were inspected at detail resolution,
with no observed clipping, overlap or glyph defect. The independent reviewer
did not claim to run Lean or inspect these PDFs. Raw LaTeX logs are preserved
byte-for-byte as gzip files.

## Deliverables

- [Article PDF](../../../../manuscripts/paper-p1/editorial-structural-preview-2026-11-07/pdf/P1_Structural_Editorial_Preview_Main_2026-11-07_EN.pdf)
- [Companion PDF](../../../../manuscripts/paper-p1/editorial-structural-preview-2026-11-07/pdf/P1_Structural_Editorial_Preview_Companion_2026-11-07_EN.pdf)
- [Editable sources](../../../../manuscripts/paper-p1/editorial-structural-preview-2026-11-07/sources/)
- [French description and reconstruction](../../../../manuscripts/paper-p1/editorial-structural-preview-2026-11-07/LISEZMOI.txt)
- [Build record](../../../../manuscripts/paper-p1/editorial-structural-preview-2026-11-07/validation/build-validation.json)
- [Rendering record](../../../../manuscripts/paper-p1/editorial-structural-preview-2026-11-07/validation/render-validation.json)
- [Completed visual inspection](../../../../manuscripts/paper-p1/editorial-structural-preview-2026-11-07/validation/visual-review.json)
