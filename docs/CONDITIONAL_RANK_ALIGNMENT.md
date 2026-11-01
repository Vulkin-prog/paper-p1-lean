# Rank loss and exact probabilities after old raw observations

Target: companion Lemma T21.2, page 87,
`p1:consequences:conditional-rank`,
`companion_sections/arithmetic_consequences.tex:139`.
Original statement SHA-256:
`818e94ea77616ce313f8e69cbcebc377f10bdc8f890c65705c43961bdb26a2e8`.

Status: **proved**, including the finite rank, exact conditional laws,
conditional mean and matching fixed-j logarithmic asymptotic. The
earlier finite checkpoint is preserved below.

## Actual old space and the supported even kernel

For any finite set R of old positive integer values, `oldSpan R` is the
span of their actual prime-parity vectors. The pool contains all primes
at most B and every prime divisor of an old value. The relative kernel
is the preimage of this old span under the parity map on even selections
of the new B-value window. It includes all local relations.

`ConditionalWindowRank.coefficient_zero_outside_pool` proves every
kernel word vanishes outside the t supported values. A prime outside
the pool is larger than B, private in the new window and absent from
every old value. Its coordinate forces the selected coefficient to
zero. `EvenSupportRank` restricts the word to its actual support and
retains the zero-sum constraint, including the empty-support case.
Thus `conditionalNullity_le` gives rho<=(t-1)_+ exactly.

`ConditionalRunRank.rowKernelEquiv` uses the full boundary equivalence
and the injective finite prime-character pairing. It proves this
square-class kernel has exactly the dimension of the actual new run
rows modulo the old raw-value row span.

## Original conditional probabilities

`Affine.ConditionalMass` defines conditioning as the actual joint mass
divided by the old-observation mass under the finite uniform sign law.
The old prescription is realizable and its mass is strictly positive.
On a nonempty intersection, the joined effective space and rank-nullity
give the exact probability 2^rho/2^L; an empty intersection has mass zero.
When rho=0, annihilator duality and uniform independent rows prove that
every new output is realizable, rather than assuming compatibility.

`ConditionalRunProbability` identifies these old observations with all
the actual raw values in R and transports both joint and old event
probabilities to the original infinite prime-sign measure. Its
`conditionalStartProbability` is literally their ratio. It is zero or
p*2^rho, and `conditionalStartProbability_nominal` proves it equals p
whenever t<=1. Every realizable old raw vector has a finite-cylinder
witness; no independence, compatibility or conditional mass estimate
is an input.

`ConditionalCountMean` defines the conditional expectation as the
original Bochner count integral on the old event divided by its positive
probability, and proves it equals the sum of the exact conditional
start probabilities.

## Finite mean budget and an improvement

`WindowPoolCount.sum_supportedIndices_dyadic` proves the actual incidence
budget sum_x t_x<=B*card(poolValues) by exchanging the two finite sums
and using an injective start-to-value map at each fixed offset.

For any O contained in the dyadic block, define D to be the starts
outside O with t_x>T. `ConditionalRunBudget.conditional_count_bound`
gives precisely the finite source bound

    E[Z | old] <= N*p + card(O) + card(D)
                       + p*2^(T-1)*B*card(poolValues).

This includes the source contact set O and requires no contact estimate.
All cutoffs and positivity hypotheses are explicit; in particular the
original prime observations and new windows fit the same finite cylinder.

`conditional_count_bound_sharp` improves the last coefficient to

    p * (2^(T-1)-1)/T.

For t<=1 the conditional probability is exactly p. For 2<=t<=T its
excess over p is at most p*(2^(t-1)-1). The ratio
(2^(t-1)-1)/t is nondecreasing for positive integers t, as proved in
`ExponentialSupportSlope.cross_bound` and `loss_le_slope`.
Charging only this excess to the incidence budget proves the improvement.
The refined finite bound also holds for T=0, with the totalized slope
zero; the source range 1<=T<=L is retained in its specialization.
P1-MATH-0029 records this improvement without any optimality claim or
claim that the remaining large-t population is small.

All proofs are new P1 code. No further Paper C source or unproved
literature statement is introduced. Mathlib at the pinned revision
supplies finite-dimensional quotient and annihilator duality, finite
sums, finite product probabilities and the infinite-cylinder bridge.

## Earlier finite checkpoint validation

The full Lean v4.36.0-rc2 build passed (9,049 jobs). The actual axiom
audit passed for all 2,655 theorem/lemma declarations, allowing only
`propext`, `Classical.choice` and `Quot.sound`. All 589 distinct
coverage/finding names were checked directly by Lean. All original
source bytes and 167 numbered statement hashes are preserved.
Coverage at that earlier checkpoint was 40 / 167; its T21.2 asymptotic
was then still open.
There are 29 confirmed improvements; no Palomar registration is made.
Available Ubuntu-root space is 17.92 GiB.

Validated finite conditional-rank implementation and P1-MATH-0029:
[dd3755df492b2fab0b50515d6b3b1dfc75014e3d](https://github.com/Vulkin-prog/paper-p1-lean/commit/dd3755df492b2fab0b50515d6b3b1dfc75014e3d).

## Closure of the actual fixed-j asymptotic

`OldValuePrimeBudget.rawValues` constructs the union of all raw values
used by the actual old starts. It has at most j*B values, all in [1,3N].
The sum of logarithms of its prime divisors is at most the sum of the
logarithms of these values. Together with the finite primorial bound,
this gives

    sum_{p in pool} log p <= B*log 4 + j*B*log(3N).

The upper critical-band width makes this at most (a_j*log N)^2 for an
explicit constant a_j. `LogSquaredPrimePool.count_le_power_eventually`
uses the already proved prime-budget Euler inequality at sigma=1/2.
Its logarithmic cost divided by log N tends to zero, with an explicit
threshold uniform over every admissible finite prime set. Consequently
`actual_pool_count_critical` proves card(poolValues)<=N^(1/2+epsilon)
uniformly over all old starts and lengths in the fixed critical band.
Positive squares give the lower bound sqrt(N)/2 for every pool.

`ConditionalPoolTerm.binary_factor_bound` keeps the critical offset
and the integer exponent T-1 exactly. It proves the required upper
scale for every integer T<=(1-delta)L. `ConditionalPoolLower` uses the
integer-floor error and squares to prove a matching positive-constant
lower bound at T=floor((1-delta)L). Absorbing only fixed constants and
logarithmic factors yields, for every epsilon>0,

    N^(1/2-delta-epsilon) <= p*2^(T-1)*B*card(poolValues)
                         <= N^(1/2-delta+epsilon).

`ConditionalRankTheorem.floor_conditions` proves 1<=T<=L eventually.
`companion_T21_2` bundles this asymptotic with every finite source
conclusion and the sharper coefficient. One threshold precedes all
critical lengths, all old sets of cardinality at most fixed j, and
every realizable old raw vector. Sets of cardinality at most j also
cover repeated entries in an indexed list of j old starts.

No prime-pool estimate, Euler factor, conditional law or asymptotic is
a theorem premise. No new Paper C source or unproved external input is
added. The positive conditional observation probability is retained.

## Complete-result validation

The full Lean v4.36.0-rc2 build passed (9,061 jobs). The actual axiom
audit passed for all 2,687 theorem/lemma declarations, allowing only
`propext`, `Classical.choice` and `Quot.sound`. All 602 distinct
coverage/finding names were checked directly by Lean. Source checks
passed for 138 manifest entries and all 167 original statement hashes.
Numbered coverage is now 41 / 167: main 15 / 73, companion 26 / 94.
The 29 confirmed mathematical improvements retain their validation
history. No original source bytes are changed and no Palomar registration
is made. Available Ubuntu-root space is 17.90 GiB.
