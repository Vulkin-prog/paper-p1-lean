# Complete incoming and outgoing certificates — companion T6.3

Companion Lemma T6.3 is proved, including the actual receiver extraction,
actual short certificate graph and both directed counts. Coverage is 62/167
(main 19/73, companion 43/94). The final source declaration is
`AnchorRelationCertificates.companion_T6_3`.

## Literal certificate graph and a sharp first passage

For positive centres bounded by X and offsets in [-W,W], let B=2W+1 and
Z=2XB. An actual edge x->y contains t actual anchor offsets, a subset T
of their actual prime divisors above Y, and actual receiving offsets at y.
The subset satisfies product(T)>Z and

    |T| <= k = floor(log(Z)/log(Y))+1.

The receiving congruences are part of the edge predicate. The graph is
allowed to contain additional edges, including repeated anchor positions;
its proved degree bounds therefore also count every source certificate.
The relation extraction uses distinct selected anchors and their odd
kernels. No target population is supplied as an input.

`ShortPrimePassage.exists_short_subset` constructs a minimal-cardinality
subset of a given large product. Deleting any retained prime leaves a
product at most Z. Taking logarithms of that erased subset proves the
stated order bound, regardless of the size of the last retained prime.

## One finite bound for both directions

Every actual individual value is at most Z. The actual source prime pool
of t values therefore has cardinality at most t*k. The actual receiver
prime pool of B values has cardinality at most B*k. These logarithmic
budgets are proved from actual prime divisibility and product heights.

At a fixed prime subset and offset-assignment code, the coprime product
exceeds the entire centre interval, so there is at most one actual centre.
The finite covers and actual assignment functions are counted. Applying
the proved colored-subset tilt gives the same bound in both directions:

    outgoing degree, incoming degree <= B^t*(e*t*B)^k.

For the source pool the color budget is B and tilt parameter t; for the
receiver pool those roles are exchanged. No condition k<=|P|/2 or a split
according to the prime-pool size is needed. This is a direct count of the
actual finite incoming/outgoing centre sets.

The order k has a proved uniform upper envelope whose scaled limit is
1/A at Y=(logN)^A. Its division by logN tends to zero. Taking logarithms
of the full finite bound proves both degrees <=N^(1/A+epsilon), uniformly
before all centres, logarithmic radii and actual centre subsets.
The degree theorem itself only needs A>0.

## Actual relations supply a received product

For primes above the block diameter, distinct actual signed offsets cannot
both give multiples of that prime. Evaluating the actual parity relation
at a selected anchor prime proves that it occurs in another selected block.
The t actual odd kernels are squarefree and pairwise coprime, and their
prime product exceeds N^(t/5).

Every prime is allocated once to an actual receiving block. The allocated
moduli have exactly that product. If m is the number of other old or new
blocks and t/5>m, a proved polynomial-versus-polylogarithmic budget shows
that not all allocated moduli can be <=Z. A minimal first-passage subset
of a larger modulus gives an actual edge to one actual receiver. All prime
privacy, allocation, product and short-subset assertions are proved.
The empty-receiver case is included by contradiction from the same actual
prime product; no extra receiver-existence premise is assumed.

## The full old span and overlapping sources

`OldBlockSelections.exists_selections` represents every vector in the full
old value span by actual selections in the old blocks. The proof uses the
finite binary linear-combination representation, grouping coefficients by
their actual old occurrences. No parity restriction is imposed on old
selections. Overlapping values and dependent old blocks are included.

`ProjectedControl` is the literal implication for a new source selection,
other new selections, and a sum in that full old span. It returns a receiver
in the actual outgoing set counted above. Other new projections need not
remain nonzero modulo the old space. Neither affine compatibility nor
independence of source blocks is used.

## Critical blocks and stronger A range

The source theorem includes every fixed comparable positive interval and
critical B0=L+1. It uses the common radius R=W+B0 for all physical offsets
of radius W<=D*B0. This retains every actual block and ensures

    2*K*N*B0 <= Z=2*K*N*(2R+1) < product(T),

so the certificate exceeds the required fixed multiple of N*B0. Pointwise
positivity and the identity of the natural and literal signed values are
proved at the same common threshold.

The full theorem holds for every fixed A>1, which is enough for prime
privacy at logarithmic widths. This extends the surrounding A>=2 regime;
the separate T6.2 smooth-modulus result retains its own range. Improvement
P1-MATH-0063 records that extension and the common explicit finite degree
bound. Here r=1+card(nu), s=card(kappa), so the precise source hypothesis
is t/5>card(nu)+card(kappa)=r+s-1.

No unproved literature input, new Paper C port, manuscript-byte change or
Palomar registration is introduced. The simultaneous induction and stage
iteration in main Theorem 10.1 remain separate open work.

Verification checkpoint: Lean v4.36.0-rc2 full build passed (9,757 jobs); actual axiom audit passed for all 4,362 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 2,077 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records remain intact. Ubuntu available space: 17.31 GiB. No unproved receiver/degree count, new literature input, new Paper C port, manuscript-byte change or Palomar registration.
