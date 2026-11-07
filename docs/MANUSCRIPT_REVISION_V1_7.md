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


Checkpoint P1-MATH-0987 further restricts the cylinder to the prime signs
actually used by the retained starts, through M=2*q*floor(N/q)<=2*N.
The full count can use later signs; the proof integrates the retained
subcount first and compares both actual full moments monotonically for
t>=0. Its original prime scale and t>2 limit are preserved. The q=7,
N=64 example certifies exact prime charges 30, 31 and 32 and a factor-four
lower-bound gain at equal count contribution. The full replay passed
18,567 build jobs, 19,485 theorem axiom checks and 19,643 distinct references.
The appendix integrates this refinement without changing any numbered
statement block. Both PDFs were rebuilt with stable references. Of their
165 pages, 164 are pixel-identical to the reviewed version and the changed
companion page 98 passed detailed visual review. Exact proof and log hashes
are preserved in [the validation record](validation/checkpoint-0987/validation.json).


Checkpoints P1-MATH-0988 and P1-MATH-0989 are integrated together in the
unnumbered companion appendix. The exact even-valuation start criterion
adds the checked N=18,q=3 example. Every finite depth k has explicit
budget N/(q+1)*(1-q^(-2*k))-3*k and both actual exponential-moment bounds
at the same supported cylinder cost. Depth one recovers the previous
budget; depth two strictly improves it at q=17,N=2^16. Larger depth need
not improve the explicit budget because its endpoint error grows. The
original t>2 theorem and every numbered statement block are preserved.
The source replays passed 18,571/19,513/19,660 and 18,573/19,540/19,692
build jobs, theorem axiom checks and distinct references respectively.

Both PDFs were rebuilt with stable references: 65 article pages and 101
companion pages. All 166 pages were rendered. The 161 unchanged pages are
pixel-identical to the reviewed version, and the five changed or new
companion pages (2,98,99,100,101) passed detailed visual inspection.
The companion gains one page; the original v1.6 package and all 167
numbered statement identities remain preserved. Exact proof commits,
source and PDF hashes, and original replay logs are recorded separately.


Checkpoint P1-MATH-0990 adds the complete valuation-layer cover, explicit
logarithmic depth, two-sided count, actual exponential bounds, fixed-prime
retained-start density and uniform absolute normalized error. The approximation
threshold is independent of the prime. This concerns the deterministic
retained forced subset; the original t>2 moment theorem is preserved.
The full source replay passed 18,575 build jobs, 19,567 theorem axiom checks
and 19,722 distinct references, with original logs and immutable proof commit.

Both PDFs were rebuilt with stable cross-references and their page counts
remain 65 and 101. All 166 pages were rendered: 164 are pixel-identical to
the reviewed version, and the two changed companion pages (98,99) passed
full visual inspection at 110dpi. No overflow or unresolved references were
found. All 48 authored source hashes, both PDF hashes, provenance and
the unchanged 167 numbered statement identities were checked.


Checkpoint P1-MATH-0991 integrates the actual compatible affine forcing
fiber and its exact effective-rank mass. Both full exponential moments
inherit the rank cost and earlier count budgets. An unused-prime kernel
vector proves at least a factor-two gain for the five-start N=18,q=3
example, with the explicit lower bound exp(5*t)/1024 for t>=0. The
original t>2 theorem and all numbered statement blocks are preserved.
The full source replay passed 18,577 build jobs, 19,598 theorem axiom
checks and 19,759 distinct references, with original immutable-source logs.

Both PDFs were rebuilt with stable references, remaining 65 and 101
pages. All 166 pages were rendered: 165 are pixel-identical to the
reviewed version, and companion page 99 passed full visual inspection
at 110dpi. There are no overfull boxes or unresolved references. The 48
authored source hashes, PDF hashes, provenance and 167 numbered statement
identities were checked.
