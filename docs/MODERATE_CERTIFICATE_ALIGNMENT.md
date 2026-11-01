# Moderate certificates — article Lemma 7.2

**Status: in progress. The full first finite counting conclusion is proved;
the weighted second conclusion remains open.** Source: article V1.6, page 23,
`main_sections/cores.tex:65`, label `p1:core:moderate`. Exact statement SHA-256:
`9594d0ca09a407ca09f83dbf5e3e3a35c779690b9000a1041eb967ba1042956a`.

## Actual kernels, anchors and the literal exponent

`TruncatedKernelProducts` identifies the exact prime support of K_Y(n),
proves positivity, divisibility by n and squarefreeness, and proves that
kernels of two distinct values at distance at most Y are coprime. Thus two
chosen values in one width-B window, with Y>=B, give a squarefree kernel
product Q. Actual source-value bounds give Q<=9*N^2. If both kernels exceed
T, their product exceeds T^2.

Every prime factor of Q exceeds Y. Taking logarithms of the actual finite
prime product proves

`card(primeFactors Q) <= ceil(2*log(3*N)/log(Y))`.

`PrimeProductBudget.assignmentExponent` is precisely this natural ceiling.
No unspecified constant or asymptotic prime bound replaces it.
`ModerateAnchors.anchor_data` combines all these facts for actual anchor
centres in [N,2N) and two physical offset indices. There are exactly
r*N*B^2 unrestricted anchor choices.

## Every prime is assigned once

`PrimeAssignments.Code P B` assigns each actual prime in P to one receiving
window and one offset in Fin(B). Its exact number is `(h*B)^card(P)`, where
h is the number of receivers. Grouping by receiver gives coprime products,
and their product is exactly prod(P), by the proved finite partition identity.
No prime is omitted or counted twice in the product.

For one fixed assignment, `ModerateReceiverCost.assignments` is exactly the
receiving-centre tuples in [N,2N) satisfying every actual divisibility.
Finite lcm and least-centre quotient arguments give at most
floor(N/D(j))+1 possible centres at receiver j, without an assumed CRT bound.
Positive modules with total product at most 9*N^2 have at most two entries
above N, for N>=10. The moderate cap D(j)<=6*N*B therefore gives the exact
cost

`36*B^2*2^h*N^h/Q`.

`ModeratePrimeAssignments.card_covered_le` counts every moderate prime
assignment and all its receiving tuples. It retains empty receiving groups
with modulus one and permits coincident centres when making an upper bound.

## Actual source tuples and the first source inequality

`ModerateCertificateCount.sourceTuples` is an actual finite population of
ordered distinct centres. Its certificate has an unmarked anchor (every
window value has kernel>T), two distinct chosen offsets, and an assignment
of every prime of their actual kernel product to an odd-valuation occurrence
in another window. The assigned receiving products obey the moderate cap.
Membership is proved in `mem_sourceTuples`.

Actual odd-valuation membership implies divisibility. Restricting a tuple to
the r-1 non-anchor receivers therefore puts it in the counted congruence
cover. `sourceTuples_subset_cover` proves this containment. The larger
`ModerateTupleCover` also counts divisibility-only witnesses and allows
coincident centres, so this enlargement is explicit rather than an assumed
arithmetic counting interface.

The receiver type has exactly r-1 elements. Its assignment alphabet has
size at most r*B, and the proved prime-count ceiling gives the factor
`(r*B)^m`, with the literal m above. Multiplying by the actual r*N*B^2 anchor
count and replacing Q>T^2 gives

`card(sourceTuples) <=
 36*r*B^4*2^(r-1)*N^r/T^2 * (r*B)^m`.

`main_7_2_finite` proves this for r>=1, N>=10, 2<=B<=N+1, Y>=B and T>=1.
These finite conditions hold eventually in the manuscript's critical band.
`main_7_2_finite_criticalBand` proves that specialization with one threshold
before **every** r, Y,T and tuple. Thus the finite bound is valid on a
growing-order range; no fixed-order uniformity is silently substituted.

## Remaining weighted conclusion

The source second conclusion sums all orders with weights `(u*p)^r/r!`.
That infinite weighted sum, its factorial/exponential majorant and the
literal growing ceiling asymptotic remain to be proved. The full numbered
lemma is therefore still in progress and adds no completed numbered result.
No new mathematical improvement is asserted by this checkpoint.

## Inputs, history and validation

All displayed kernel, cover, assignment, congruence and counting estimates
are proved internally. Mathlib at `9d581dfff2e41de989072ea63abf3daf69311520`
supplies finite products, prime factors, logarithms, natural division and
finite function counts. No additional Paper C source is ported.

The earlier checkpoint proved only the receiving-centre cost, with 2,047
audited declarations:
[c389a5368f0aa4ab70adc436c6bb34ba0db16432](https://github.com/Vulkin-prog/paper-p1-lean/commit/c389a5368f0aa4ab70adc436c6bb34ba0db16432).
That partial scope is retained as historical validation, rather than evidence
for the later arithmetic cover.

The current full Lean v4.36.0-rc2 build passed (8,865 jobs), followed by the
actual axiom audit of all 2,092 project theorem/lemma declarations. Only
`propext`, `Classical.choice` and `Quot.sound` occur. Completed coverage
remains 31 / 167. No Palomar registration is made.

All 337 distinct coverage/finding declaration names were checked directly by Lean.

Validated implementation of the full first finite counting conclusion:
[e349c4801dffc0e0e76a7caa152c3aa2330e55f7](https://github.com/Vulkin-prog/paper-p1-lean/commit/e349c4801dffc0e0e76a7caa152c3aa2330e55f7).
