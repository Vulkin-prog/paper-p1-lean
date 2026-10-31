# Companion T1.3: local and global defect counts

**Status: proved**, including all three estimates and fixed positive real
dilations and real translations of the intervals.

Original locator: companion V1.6, page 6, Lemma T1.3,
`p1:arith:defects`, `companion_sections/arithmetic_appendix.tex:90`.
The standing convention B=L+1 is recorded in the companion guide and the
main arithmetic section. The source block and its SHA-256 are unchanged.

## Complete statements and quantifiers

The principal declarations are

- `PaperP1.UniformDefectCounts.companion_T1_3_run_length`;
- `PaperP1.UniformDefectCounts.companion_T1_3_run_length_fixed_affine`.

The more general `companion_T1_3` and `companion_T1_3_fixed_affine`
keep a real budget B independent of the run length.

All macroscopic, logarithmic and width comparison constants are fixed first.
There is then a local constant K>0, independent of the error exponent.
For every ε>0, one common threshold precedes every N, cutoff H, length L,
local interval and global counting endpoint. Under the original comparisons
B ≍ log N and H ≍ B, these theorems give all three conclusions:

| Original conclusion | Actual finite set used in Lean | Bound |
|---|---|---|
| Local defects in a short interval | `LocalDefectBound.defectsInInterval H U R`, with cN ≤ U ≤ CN and R=O(B) | K B/log B |
| Global defects | `GlobalDefectCount.positiveDefectsBelow H X`, for every integer X ≤ CN | N^(1/2+ε) |
| Dyadic starts with two defective vertices | `TwoDefectWindows.dyadicTwoDefectWindows N H L` | N^ε |

The global and window estimates are quantified independently of the local
interval. The literal B=L+1 corollaries include every local width comparison
constant, even when it is smaller than 1.

## Intrinsic arithmetic dictionary

`LargeOddKernel.largeOddKernel H n` is the product of primes above H whose
valuations in n are odd. Equality to 1 is proved equivalent to
`DefectivePredicate.HDefective H n`.

Every positive defective integer has its canonical odd-prime-support times
square representation. Its support lies among primes at most H. The square
part is reconstructed by halving the prime exponents. These are proved
arithmetic statements, not supplied representations of the actual values.

The global set uses positive integers. Its real-endpoint membership theorem
identifies the exact condition n ≤ Y with the natural floor of Y, and handles
negative endpoints by the empty positive set. This supplies the literal
counting endpoint CN. The manuscript's cutoff domain H ≥ 2 is included;
the formal definitions also make sense at smaller natural cutoffs.

## Local proof

For any actual interval [U,U+R], the small-prime cutoff and interval width
remain separate. An augmented parity code has at most π(H)+1 rows.
A kernel word selects an even square product. The proved T1.1 bound excludes
every nonzero word of weight ≤2t under `(64R)^(2t)<U`.
Sphere packing and rank-nullity prove the Hamming volume bound, including
the small-cardinality cases.

The direct coding radius is `floor(log U/(4 log(64R)))`.
An elementary Chebyshev bound is proved from Mathlib's primorial estimate.
The uniform prime budget is then **proved** from the macroscopic and
logarithmic comparisons. It is not an assumption of the final theorem.

For a width bounded above by E log N, enlarge it to a common rounded width
comparable to log N. The radius is bounded below uniformly by
log N/(32 log log N), and the prime count is bounded above by a fixed
multiple of the same quantity. The resulting local rate is
O(log N/log log N). The explicit B comparisons give O(B/log B).
All thresholds are independent of the chosen interval and cutoff.

## Global and two-defect proofs

The actual positive global set is proved equal to the represented-value set.
Weighted counting and a finite reciprocal-square-root sum give

`#defects ≤ sqrt(X) exp(2 sqrt(H))`.

Uniform absorption of the exponential and the fixed macroscopic coefficient
gives N^(1/2+ε) whenever H ≤ D log N and X ≤ CN.

For two defects, an actual start is covered by a configuration consisting of
two distinct offsets, two small-prime supports, and an actual positive
quadratic solution. The equation is exactly
`c₁a²-c₂b²=i-j≠0`. Support products have uniform polynomial height, and
the proved T1.2 count covers both square and nonsquare coefficient products.
Offset and support counts are uniformly subpolynomial. See the detailed
[two-defect alignment](TWO_DEFECT_ALIGNMENT.md).

The dyadic window is exactly [x-1,x+L-1], with x in [N,2N). The injective
shift x ↦ x-1 retains the left boundary vertex.

## Fixed affine interval changes

The scale a>0 and real translation are fixed before K and all thresholds.
The proofs count positive integer points inside the real image intervals.

- Local interval: [aU+shift, a(U+R)+shift].
- Global interval: [shift, aCN+shift].
- Dyadic start interval: [aN+shift, 2aN+shift).
- Complete vertex window at integer start y: [y-a, y-a+aL].

Exact real-bound filters prevent artificial points when an endpoint is
negative. The local enclosing interval starts at the natural ceiling and has
rounded scaled width. For affine dyadic windows, the injective map is
y ↦ y-floor(a), after the proved threshold makes this a positive base.
Every integer vertex lies in the corresponding rounded enclosing window.
Thus the fixed-affine conclusions follow with the same exponents.

## Improvement, provenance and checks

The local estimate only needs H=O(B), with B ≍ log N. Its lower comparison
H ≳ B is unnecessary. The global and two-defect estimates need only upper
logarithmic bounds on H and on the relevant width. This complete strengthening
is tracked as P1-MATH-0003; all original hypotheses remain covered.

The generic parity, coding, weighted counting and elementary growth inputs
are the exact audited ports recorded in [PAPER_C_REUSE.md](PAPER_C_REUSE.md).
The uniform budgets, actual-set bridges, affine interval definitions and
complete assembly are new P1 proofs. No literature estimate or target bound
remains as an unproved premise.

The full project builds under Lean v4.36.0-rc2. The actual kernel-axiom audit
passes for all 862 current proved declarations, permitting only propext,
Classical.choice and Quot.sound. Numbered-result coverage is now 9/167.

