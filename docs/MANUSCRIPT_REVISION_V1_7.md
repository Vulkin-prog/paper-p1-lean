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


Checkpoint P1-MATH-0992 identifies the positional target with literal mutually
independent Poisson arrivals, constructs a concrete finite product realization,
and proves the original weighted grid comparison for every realization, with
explicit summability and one threshold before the probability space and all
variables. The original grid, arithmetic individual rates, exponent 4/5 and
all 167 numbered statement blocks are preserved. The full source replay passed
18,587 build jobs, 19,631 theorem axiom checks and 19,783 distinct references.

The unnumbered companion appendix now explains this exact independent-arrival
interpretation. Both PDFs were rebuilt with stable cross-references and no
overfull boxes or unresolved references. The article retains 65 pages; the
companion grows from 101 to 102 pages. All 167 current PDF pages were rendered:
162 are pixel-identical at 55dpi to the previous reviewed version, and all five
changed/new companion pages (2,99,100,101,102) passed full visual inspection at
110dpi. All 48 authored source hashes, both PDF hashes, source provenance and
unchanged numbered statement identities were checked.


Checkpoint P1-MATH-0993 proves exact Poisson marginals for every site of the
compensated reference arrival field, in every independent realization and the
canonical product law. Arbitrary finite packets and ambient index types are
allowed without a countable-configuration hypothesis. Every natural-order
factorial test is integrable with expectation p_x^j. These are reference-field
identities; the arithmetic approximation retains its original exponent and
fixed-degree scope. The full replay passed 18,591 build jobs, 19,655 theorem
axiom checks and 19,796 distinct references, with all three actual exits zero.

The unnumbered companion appendix includes the exact marginal and factorial
moment statements, explicitly quantified over natural orders. Both PDFs were
rebuilt with stable cross-references, no unresolved references and no overfull
boxes. Long Lean identifiers have normal optional line breaks. All 167 pages
were rendered: 165 are pixel-identical to the prior reviewed version, and both
changed companion pages (99,100) passed full inspection at 110dpi. Page counts
remain 65 and 102. All 48 source hashes, provenance, both PDF hashes and all
167 numbered statement identities were checked.


Checkpoint P1-MATH-0994 proves the exact covariance matrix of the literal
reference arrivals, with square-integrability assertions. For arbitrary
finite packets the covariance is the compensated single rate on the
diagonal plus all shared packet rates. For pairs its diagonal is p_x and
its off-diagonal entries are the retained pair rates, zero otherwise.
The formulas hold for every independent realization and the concrete
finite product law, without countable-configuration hypotheses. They do
not identify the original arithmetic covariance or change the original
exponent and fixed-degree scope. The full replay passed 18,593 build jobs,
19,673 theorem axiom checks and 19,815 distinct references, all actual exits 0.

The unnumbered companion appendix states the shared-arrival formula, square
integrability and full pair specialization with the reference-field scope.
Both PDFs were rebuilt with stable cross-references, no unresolved references
and no overfull boxes. All 167 pages were rendered: 165 are pixel-identical
to the prior reviewed version, and both changed companion pages (99,100)
passed full inspection at 110dpi. Page counts remain 65 and 102. All 48 TeX
hashes, provenance, both PDF hashes and all numbered statement identities
were checked. All sixteen local registry receipts remain valid.


Checkpoint P1-MATH-0995 proves the sharp independence criterion for actual
reference coordinates. Two finite sums of independent Poisson cells are
independent exactly when their total shared rate is zero. Shared zero-rate
cells vanish almost everywhere, leaving functions of disjoint independent
cell families. For pair arrivals, distinct reference coordinates are
dependent precisely on retained edges with positive rate. Natural-valued
counts, their real versions, arbitrary finite packets and the concrete
product law are covered, including all degenerate rates. This is specific
to the reference construction; the original arithmetic comparison keeps
its rates, exponent 4/5 and fixed-degree quantifier order. The full replay
passed 18,595 build jobs, 19,691 theorem axiom checks and 19,833 distinct
references, all actual exits 0. All sixteen local registry receipts remain
valid with unchanged original statement and imported proof bytes.

The companion appendix includes the sharp independence criterion, positive
pair-rate distinction and natural-valued scope. Both PDFs were rebuilt
with stable cross-references, no unresolved references and no overfull
boxes. All 167 pages were rendered: 165 are pixel-identical to the prior
reviewed version, and both changed companion pages (99,100) passed full
inspection at 110dpi. The declaration/module pointer paragraph is kept
together so no Lean identifier is split across pages. Page counts remain
65 and 102. All 48 TeX hashes, provenance, both PDF hashes and all numbered
statement identities were checked.


Checkpoint P1-MATH-0996 proves independence of complete natural-valued
reference-coordinate vectors. Two finite blocks, even possibly overlapping,
are independent exactly when all their cross covariances vanish. The
proof explicitly removes shared zero-rate cells from full arrival tuples
almost everywhere and reconstructs each whole block measurably. For
pair packets and disjoint blocks, the exact criterion is that every
retained crossing pair rate is zero. Equivalently, no positive-rate
retained edge crosses, establishing the full dependency-graph condition.
The canonical product law and factorization of measurable block-event
probabilities are included. These are reference-field identities; the
original arithmetic comparison, exponent and fixed-degree regime are
preserved. The full replay passed 18,597 build jobs, 19,709 theorem axiom
checks and 19,854 distinct references, all actual exits 0. All sixteen
local registry receipts remain valid with unchanged original proof closures.

The companion appendix states the full vector criterion, positive-rate
dependency-graph property and event factorization, with the reference scope
explicit. Both PDFs were rebuilt with stable cross-references, no unresolved
references and no overfull boxes. All 167 pages were rendered: 165 are
pixel-identical to the prior reviewed version, and both changed companion
pages (99,100) passed full inspection at 110dpi. The complete module-pointer
paragraph stays on one page. Counts remain 65 and 102 pages. All 48 TeX
hashes, provenance, both PDF hashes and all numbered statement identities
were checked.
