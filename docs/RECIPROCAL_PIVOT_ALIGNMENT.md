# Companion T19.15 — Finite reciprocal-pivot reductions

Source: Lemma T19.15, page79, `p1:limits:reciprocal`,
`companion_sections/limits_appendix.tex:1138`.
Statement SHA-256: `50c4669b813dd7368744a6b5195d48ce2be90fbf7ec6976ccb98bee12f86a816`.
Original bytes are preserved. Status: **in progress**.

The finite arithmetic reduction of companionT19.15 is proved for the
actual largest prime with odd valuation, including the prime2. Its
value on a square is1. The cutoff predicate agrees exactly with the
existing intrinsic defect predicate. The pivot is at most the actual
largest prime factor, and equals the largest prime factor of the
canonical squarefree kernel for every positive integer.

The canonical square-part map is proved injective and lands in the
actual finite domain a>=1, a<=sqrt(X), 1<=v<=floor(X/a^2). Positive
summation therefore proves, with literal natural floors,

    S_plus(X)<=S_kappa(X)<=sum_{1<=a<=sqrt(X)} S_plus(floor(X/a^2)).

No squarefree counting estimate or multiplicity bound is assumed.
For every integer cutoffA>=1, the actual a>A contribution is at most
2X/A, by a proved reciprocal-power tail. Thus the finite small-a sum
plus2X/A bounds the actual reciprocal-pivot sum.

The exact dyadic transfer is also proved. Multiplication by any power
of2 preserves every actual pivot greater than2. The least doubling
exponent sends each 1<=n<=N into [N,2N), and is bounded by
Nat.clog2N. The pair (exponent,image) is injective. Actual finite
positive sums give, for everyN>=1,

    S_kappa(N)<=2*(floor(sqrt(N))+1)+(Nat.clog2N+1)*D_kappa(N),
    D_kappa(N)<=S_kappa(2N).

The first term is proved by the existing defect representation count
at cutoff2. No dyadic preimage count, square-part injection, pivot
invariance or small-pivot estimate is supplied as a premise.

These finite statements prepare the exact asymptotic ofT19.15.
The cited Erdos--Ivic--Pomerance ordinary reciprocal-prime asymptotic,
the explicit saddle scales, their uniform comparison on the small-a
range and the final logarithmic equivalents remain unformalized.
T19.15 is in progress, not proved or conditionally complete.
Coverage77/167 (main28/73, companion49/94), findings86 unchanged.
The PaperC port is limited to the pivot definition, positive lower
bound, cutoff equivalence and pivot population definition at the
recorded immutable commit/blob; its unproved analytic interfaces are
not imported. All other reduction, injection, tail and dyadic proofs
are new P1 code. No new external mathematical argument, dependency
download, source-byte change or Palomar registration is introduced.

## Kernel audit and statement scope

The completed finite inequalities are ordinary theorems with no external
analytic input. All new public theorem/lemma declarations are included in
the generated actual kernel-axiom audit. The finite helper count does not
add numbered-result coverage. The comparison sum uses the actual canonical
squarefree kernel, positive integer bounds, the square-part reconstruction,
and exact integer division. It does not replace the pivot by an arbitrary
chosen prime or silently exclude the prime2.

Lean v4.36.0-rc2 full build passed (10663 jobs); actual axiom audit passed for all 6289 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 4006 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records remain intact. Ubuntu available space: 15.74 GiB. Actual reciprocal-pivot comparison, canonical square-part injection, literal finite sum reduction, the2X/A tail and logarithmic-preimage dyadic transfer are proved with no analytic premise. The exact Erdos--Ivic--Pomerance and uniform saddle asymptotics remain open; T19.15 is in progress. Coverage77/167 (main28/73, companion49/94); confirmed findings86. Only the exactly attributed elementary pivot fragments are ported from PaperC; no old analytic assumption or binary is imported. No new external mathematical input, dependency download, source-byte change or Palomar registration.
