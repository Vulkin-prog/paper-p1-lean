# Small truncated kernels — article Lemma 7.1

**Status: proved in full.** Source: article V1.6, page 23,
`main_sections/cores.tex:24`, label `p1:core:rankin`. Statement SHA-256:
`62a5de96e9fb6301b919b824ad4160de336e6eb3dd71840afec97e3408f10973`.
The companion proof is `companion_sections/cores.tex:11`, under
`p14:comp:certificate-rankin`.

## Actual population and real cutoffs

`RankinSmallKernel.truncatedKernel Y n` is exactly the product of primes
p>Y occurring to odd exponent in n. `truncatedKernel_eq_floor` identifies
it with the previously proved natural-cutoff kernel. `values X Y T` counts
actual positive integers n<=X whose kernel is at most T. `mem_values`
proves that literal description; zero is excluded.

All three cutoffs are real. Floor transport is proved in both the interval
and the kernel condition. There is no integer-cutoff substitution left as an
external argument.

## Exact finite cover and Euler-product bound

The canonical valuation decomposition is n=k*s*a^2, with k the actual large
odd-prime kernel, s the product of the actual small odd-prime support, and a
the canonical positive square part. Thus each counted n belongs to a finite
cover over 1<=k<=floor(T) and subsets of primes up to floor(Y).

For fixed k and small support S, its fibre contains at most
floor(sqrt(floor(X)/(k*prod(S)))) values. The denominator is positive. If it
exceeds floor(X), that natural fibre is empty. Otherwise the quotient is at
least one, so its square root is at most its sigma power whenever sigma>=1/2.
Consequently the entire count is at most

`floor(X)^sigma * sum_{k=1}^{floor(T)} k^(-sigma) *
 prod_{p<=floor(Y), prime}(1+p^(-sigma))`.

The cover may include noncanonical supports and noncoprime factors; these
only enlarge the upper bound. No injectivity or uniqueness assumption is
needed for the cover estimate. The actual decomposition is proved.

`PartialPowerSum.powerSum_le` proves, for 0<=sigma<1 and every natural Z,

`sum_{k=1}^Z k^(-sigma) <= Z^(1-sigma)/(1-sigma)`.

It uses the monotone sum-integral comparison on (0,Z] and the actual integral
of x^(-sigma). The integrable endpoint at zero is handled explicitly.
The exact finite powerset identity gives the Euler product; 1+u<=exp(u)
and the same partial-sum estimate bound it by
`exp(floor(Y)^(1-sigma)/(1-sigma))`.

## Source quantifiers and explicit constants

`RankinSmallKernel.rankin_bound` proves for 1/2<=sigma<1 and X,Y,T>=0:

`card(values X Y T) <=
 X^sigma * T^(1-sigma)/(1-sigma) * exp(Y^(1-sigma)/(1-sigma))`.

Floor monotonicity is proved using the nonnegative exponents. In
`main_7_1`, the exponential constant 1/(1-sigma) is chosen before C1.
The prefactor at X=C1*N is C1^sigma/(1-sigma), independent of N,Y,T.
The theorem holds for every natural N, every Y>=0 and T>=1; in particular it
covers all Y>=B in the manuscript. Its original strict range 1/2<sigma<1
is a direct specialization. This is the complete original asymptotic bound
with explicit uniform constants, rather than an interface assuming it.

## Confirmed endpoint improvement

`rankin_half` proves the stronger endpoint bound

`card(values X Y T) <= 2*sqrt(X)*sqrt(T)*exp(2*sqrt(Y))`.

The original companion proof enlarges the square-part sum to zeta(2*sigma),
which diverges at sigma=1/2. Counting each finite square-root fibre first
avoids that loss. `P1-MATH-0015` records the endpoint, real nonnegative
cutoffs and explicit constants. No original conclusion is corrected, and
no optimality claim is made.

## Provenance and validation

The real/natural Rankin square-root comparisons and product-power rewrite
are adapted from Paper C's `PaperCV11/RankinTilt.lean`, Git blob
`0e160cd09e337d5b6142c75524a2da9da7ec5584`, commit
`b9fa9ba490f201b408a302a86f1594ee620b228b`, Apache-2.0. The exponent is
complemented and the natural comparison includes empty fibres above X.
See [reuse record](PAPER_C_REUSE.md). The rest of this P1 counting argument
is new here. No old compiled artifact was used.

Mathlib at `9d581dfff2e41de989072ea63abf3daf69311520` supplies real powers,
finite sums/products, sum-integral comparison and real-power integration.
No zeta estimate, prime asymptotic or unproved literature input is needed.

The full Lean v4.36.0-rc2 build passed (8,805 jobs). The actual axiom audit
passed for every one of the 1,914 project theorem/lemma declarations, with
only `propext`, `Classical.choice` and `Quot.sound`. Coverage is 27 / 167:
11 main results and 16 companion results. No Palomar registration is made.

All 251 distinct coverage/finding declaration names were checked directly by Lean.

Validated implementation of article Lemma 7.1 and P1-MATH-0015:
[77ac64fd3085c4f58ebb6a071f5c3fa30779a85b](https://github.com/Vulkin-prog/paper-p1-lean/commit/77ac64fd3085c4f58ebb6a071f5c3fa30779a85b).
