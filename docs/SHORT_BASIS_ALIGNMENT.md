# Actual finite stages of short-basis extraction

Source: article theorem13.1, `p13:rig:short-basis`,
`main_sections/pair_rigidity.tex:88`, and its companion proof in
`companion_sections/pair_rigidity.tex:159`. Status: **in progress**.
Coverage75/167 (main27/73, companion48/94); confirmed findings77.

## Actual components and finite deletion costs

`MediumPrimeColumns` constructs the actual medium primes z<p<=10B,
the actual vertex sets of the actual large-prime components, their
literal prime-parity sums and the supports of these columns. Here
B=L+1 and the two physical blocks stay disjoint formal copies.
For any selected component family, disjointness implies

    sum(column weights) <= sum_p #(actual odd p-occurrences).

Each original block injects into its actual interval of length B.
Counting its multiples gives at most B/p+1 occurrences, even before
discarding even prime valuations. Thus the total actual column weight
is at most 2B*sum_p(1/p)+2*#P. All interval shifts, including the left
true-window endpoint, are retained.

`DisjointColumnWeights` proves the exact finite deletion cost:
weight>=3 columns number at most one third of the total weight.
There is no factor M multiplying that loss. The actual component
vertex sets are disjoint and have total size at most2B, so deleting
components of size>M costs at most2B/(M+1).

`ShortBasisComponentStage` constructs the actual retained family.
Using the already proved comparison with the actual intersection rank,
its cardinality is at least

    d_xy - D0 - 2B/(M+1) - (2B*sum_p(1/p)+2*#P)/3,

where D0 is the actual defective vertex count and P is the actual
medium-prime set. Every retained component has size at most M and
an actual medium-prime column of weight at most two. No defective
count or prime asymptotic is assumed as an unconditional conclusion.

## Actual physical and square-class injectivity

`ComponentProjectionInjectivity` proves that selecting the free
nontrivial components satisfies every actual large-prime equation.
Every such component meets both physical blocks, so both physical
projections are injective. An actual large prime carried by an edge
occurs once in each block and witnesses the coefficient of that
component in the actual first-block prime-parity map. This proves
square-class-image injectivity, without an assumed rank or separation
property. Later subspaces inherit these injectivities.

## Actual medium-prime incidence model

`BinaryIncidenceAugmentation` adds one row equal to the sum of all
original rows. The resulting linear map is injective, hence preserves
the kernel after composition with any actual column map. Every finite
binary column of weight at most two is realized by actual endpoints
among the original row vertices plus one infinity vertex. A zero
column is a loop, a weight-one column joins infinity, and weight-two
columns join their actual distinct row vertices. Edge labels retain
parallel columns.

`MediumPrimeIncidence` proves that the typed column indicators equal
the actual component prime-parity sums. Its actual medium-prime map
is also identified with the literal equations on the selected formal
physical occurrences. The labelled incidence map and this actual
medium-prime map have exactly the same kernel. This is a constructed
finite model, not a postulated incidence or kernel correspondence.

## The final actual small-prime and parity cut

`SupportedLinearSection` extracts a basis of the actual range from
actual single-column images, chooses the corresponding pivot columns
and constructs an actual right inverse supported on at most the target
dimension many pivots. `SparseKernelBasis` projects each actual single
column into the kernel. These projected vectors span the actual kernel;
a basis extracted from them has support at most target dimension+1.
The result holds even for arbitrary coordinate index sets.

`LinearCombinationSupport` bounds the literal support of a linear
combination by the actual union of its input supports.
`SparseConstraintBasis` transports the coordinate kernel back into
the original space. Thus a basis with physical support at most ell,
cut by s finite equations, has an actual kernel basis of physical
support at most ell*(s+1). No sparse basis or pivot conclusion is an
unproved argument of this theorem.

`ShortBasisFinalCut` constructs the actual pi(z) small-prime equations
and the separate two block-parity equations on any actual medium-prime
subspace. Every vector of the resulting actual kernel is proved to be
an actual complete even relation: every prime is checked in its large,
medium or small range; nonprime parity coordinates are zero. The map
into the actual complete relation code is injective and loses at most
pi(z)+2 dimensions. Both physical projections and the actual first-
block prime-parity image remain injective after this cut.

The resulting actual kernel has a basis of physical support at most
ell*(pi(z)+3) whenever its supplied input basis has physical support
at most ell. This is the proved final linear-algebra step of the source
proof. The requisite input short-cycle space and its short basis still
must be constructed from the actual retained incidence model.

## The actual sharp prime harmonic window

`MangoldtFloorBudget` proves the exact factorial identity with the
actual floor divisions N/d. Their errors lie in [0,1], so Chebyshev's
proved psi bound and actual log-factorial bounds give

    log N - 1 <= sum_{n<=N} Lambda(n)/n <= log N + log4 + 4.

`PrimeLogMertens` proves actual nonprime prime-power terms summable
using the pinned Mathlib elementary prime-power/geometric-series
lemma at modulus1. Their actual convergent sum gives an absolute
constant H>0 bounding the weighted prime-log summatory error at every
real endpoint>=2. No PNT remainder or weighted-sum bound is assumed.

`LogarithmicAbelWindow` proves and estimates the actual Abel identity.
All differentiability, integrability of the actual finite summatory
function, envelope inequalities and log-log/inverse-log integrals are
proved. The constant-error hypothesis is instantiated with the actual
H just constructed, giving actual harmonic-window error<=2H/log a.

`MediumPrimeHarmonic` identifies the actual finite medium-prime set
with the real cutoff B^a<p<=10B. The two-logarithm shift and exact
log-rpow identities give

    abs(sum_{B^a<p<=10B} 1/p - log(1/a))
      <= (2H/a+log10)/log B.

An explicit power/ceiling threshold supplies the eventual estimate
for every fixed0<a<=1. Only one missing Mathlib cache file was fetched
for the log-factorial bounds; all caches remain on Ubuntu.

## The actual uniform retained-component coefficient

`RetainedComponentAsymptotics` combines the actual harmonic estimate,
prime-count budget, one-third column deletion and component-size cut.
With M=floor(log B), the exact actual retained family has count at least

    d_xy - D0 - (2/3)B log(1/a) - ((2/3)K_window+18)B/log B.

The actual defective-vertex estimate then proves, uniformly over every
critical dyadic pair,

    #retained >= d_xy - (2/3)B log(1/a) - K_a B/log B.

K_a is chosen before C; only the eventual threshold depends on C.
This propagates the existing uniformity improvement P1-MATH-0006.
Compatibility, nonalignment and non-overlap are unnecessary. This is
the full initial retained-component estimate of the source argument;
it does not assert a completed short-cycle space or short basis.

## Remaining obligations

The short-cycle construction with its length and retained-rank bounds,
and the full source asymptotic short-basis assembly remain open. The
final cut accepts an actual medium-prime subspace with its actual basis;
the required short-cycle inputs must still be constructed from the
actual incidence model. Article13.1 remains in progress. No source-
conclusion error, optimized constant, external graph bound, new Paper C
source, manuscript-byte change or Palomar registration is claimed.

## Validation

Lean v4.36.0-rc2 full build passed (10493 jobs); actual axiom audit passed for all 5801 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 3516 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records are intact. Ubuntu available space: 15.98 GiB. Actual factorial floors and prime-power summability construct the weighted prime-logarithm error constant; the actual Abel integral and exact real cutoffs prove the source prime-harmonic estimate with inverse-log error. Actual component deletion, internally proved prime-count and defective-vertex budgets give retained count>=d_xy-(2/3)B log(1/a)-K_a B/log B uniformly over all critical pairs, with K_a before C. No weighted-error, prime-harmonic, PNT-remainder or retained-count estimate is an unproved input. Graph short-cycle length/rank estimates and full short-basis assembly remain open; article13.1 stays in progress. Coverage75/167 (main27/73, companion48/94); findings77. Only one selective Log.Sum cache file was fetched; no additional Paper C source, manuscript-byte change or Palomar registration.
