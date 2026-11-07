# P1 version 1.7 source revision

Version 1.7 is a separate draft derived from the preserved version 1.6
package after completion of the original valid statements through
P1-MATH-0983. It retains all 167 labels. The baseline ledger remains
165 proved, 0 conditional and 2 false-original scopes in progress.
The revised ledger tracks the two corrected statements separately and records all
167 revised statements as proved after full checkpoint P1-MATH-0984.
The replay passed 18,535 build jobs, 19,288 theorem axiom checks and
19,607 distinct declaration-reference checks. Its proof commit is
27bc1758cb8ed6b2a95add0f70f90dfe450c2de7.

| Result | Source revision | Checked mathematical basis |
|---|---|---|
| T1.10 | Match the asymmetric alignment radius to the old interval; state the actual expanded old-centre domain and cutoff interval. | SharpAsymmetricProfile.uniform_profile; SharpExpandedAsymmetricProfile.uniform_profile; the revised small-prime invariance declaration. |
| T5.1 | Add the trivial cap 1 to the exponent minimum; make the integer and kernel bins explicit; qualify the uncapped exact comparison. | PrescribedQuadraticKernelTheorem.actual_exponent_counts; QuadraticKernelExponents.capped_le_affine and exponent_le_affine_of_range. |
| T19.17 | Replace the required proof input by the internally proved sufficient logarithmic-window census; retain the original theorem statement and both coefficients. | SmoothLogarithmicWindowDensity.uniform_bound; UnconditionalOrdinarySourceCensus.ordinary_census; both UnconditionalPrintedAnchorObstruction declarations. |

The revised T1.10 convention is also stated at its uses in compressed
third-cumulant, conditional arithmetic and homogeneous comparison
arguments. The original equal-window radius-one convention remains
unchanged.

The formalization appendix records the counterexamples behind the two
corrections, the exact Gaussian smooth census argument, and the stronger
statements that the development does not claim. The complete mathematical
change ledger remains docs/mathematical-changes.json; intermediate proof
improvements are retained there with their declarations and validation
commits.

The revised source checker verifies the following:

- The original v1.6 manifests and 167-statement baseline remain intact.
- The revised source has exactly the same 167 labels.
- Exactly T1.10 and T5.1 have changed statement hashes.
- Every revised source locator and proof reference matches its separate
  revised ledger.
- Both false originals retain their baseline status, even after their
  corrected replacements are validated.

The TeX builder produces both PDFs with shell escape disabled and stable
cross-references. The PDF review covers every rendered page in contact
sheets and the changed mathematical and formalization pages at higher
resolution. The current review and revised proof-validation state are
recorded in docs/manuscript-v1.7-validation.json.

Checkpoint P1-MATH-0985 also makes the exact uncapped comparison criterion
necessary and sufficient for the actual nonnegative divisor exponent. For
arbitrary real parameters it is described only as sufficient. This wording
is integrated in the unnumbered formalization appendix; no numbered statement
block changes. Its four theorems passed a complete replay with 18,539 build
jobs, 19,295 theorem axiom checks and 19,611 distinct checked references.
Both PDFs were rebuilt: all 165 pages were rendered, 163 were pixel-identical
to the previously reviewed pages, and both changed pages were inspected at
higher resolution.


Checkpoint P1-MATH-0986 integrates the one-sided prime-cylinder finite bound
in the unnumbered companion appendix. A start of length at least q-1 needs
only the preceding negative sign, so the retained count improves from
N/q-2N/q^2-4 to N/q-N/q^2-3. Both actual exponential moments obey the stronger
lower bound. The original t>2 domain, prime scale and asymptotic coefficient
are retained. Its full source replay passed 18,563 build jobs, 19,452 theorem
axiom checks and 19,625 distinct declaration-reference checks. All 167
numbered statement blocks are preserved. Both PDFs were rebuilt with stable
references: 65 main and 100 companion pages; 163 pages are pixel-identical
to the reviewed version and the two changed companion pages passed detailed
visual inspection. The exact proof commit and original logs are preserved
in [the validation record](validation/checkpoint-0986/validation.json).
