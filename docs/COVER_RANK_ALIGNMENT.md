# Companion T20.7 — Covering cost and free three-block components

Source: Lemma T20.7, page 84, `p1:offset:cover-rank`,
`companion_sections/offset_geometry.tex:271`, statement SHA-256
`3ee81e33259f97340c3f952b3d45dabdc65d472d4c67f1c0bedd44538fa460f1`.

`TripleCoverRank.companion_T20_7` proves every source conclusion on
the actual complete window coordinates. One explicit positive constant
precedes the critical-band constant, and one threshold then precedes
every N, length, regular triple and shared-prime hyperedge cover.
No rank estimate, defective-count bound, component count or prime-count
estimate is an input. Primitive triple host and mass estimates are
separate results and are not asserted here.

## The exact covered relation space

Vertices are the 3B formal copies (i,j), with actual label X_i-1+j.
The relative relation space consists of selections even in every block
whose full prime-parity sum is zero. The space R_D is the subspace
vanishing on the chosen coordinates D. Formal copies are retained even
when physical window values coincide.

Actual valuation rows have at most one position in each block for every
prime greater than H. `SharedPrimeCover` proves that a row has three
positions exactly when that prime has odd valuation in all three
windows. Thus `CoversShared` is the original hyperedge-cover condition.
After deleting D, every row has size at most two. Size-two rows are
edges; singleton rows and every deleted vertex are pins.

`CoverGraphResolution.zeroed_eq_graph_space` proves equality with the
constructed pinned graph space. The generic coordinate-restriction
kernel equivalence proves dim R<=|D|+dim R_D, with no assumption that
the chosen coordinates are independent. The existing attributed
pinned-graph equivalence gives one coefficient per unpinned component.

## A finite bound including singleton components

For each specified missing block, select arbitrary binary coefficients
on all free components avoiding that block. `ComponentSelection` proves
that this encoding is injective and satisfies every large-prime row.
Its actual small-prime coordinates and the two remaining block parities
form a target of dimension pi(H)+2.

The kernel is zero: a vanishing small-prime vector gives a full relative
relation in at most two blocks. Injectivity of the local even maps and
pairwise directness of their actual square-class images force that
relation to vanish. These hypotheses follow from the stated regularity
and pairwise directness of the original triple; no three-block
independence is imposed.

Every non-full free component misses some block. Consequently

    dim R_D <= c3(D) + 3*(pi(H)+2).

This includes singleton free components. No separate defective-vertex
estimate is needed. The finite bound and weaker hypotheses are recorded
in P1-MATH-0032.

## Products, real cutoffs and critical-band uniformity

The indicator of each free component is an actual large-prime solution.
The product of its positive integer labels, counted with their formal
multiplicities, therefore has zero parity at every prime above H.
`component_product_square_small` constructs its literal representation
as a product of distinct small primes times an integer square. This is
the source assertion about being a square modulo small primes.

For the real cutoff H=C0*B, the natural cutoff is floor(H). Exact
equivalences are proved both for primes above the real cutoff and
primes at most it. The internal finite Chebyshev estimate gives the
explicit B/log(B) constant

    K(C0) = 3*(14*log(2)*C0+2).

For every fixed critical band, B>=4 eventually. The same threshold
works before all triples and covers. The proof permits C0=1 and
overlapping windows under the retained local injectivity and pairwise
directness conditions. No separation premise is used by the finite
comparison. These extensions do not prove a primitive-host counting
estimate or the subsequent six-vertex budget.

## Validation

The full Lean v4.36.0-rc2 build passed (9,135 jobs). The actual axiom
audit passed for all 2,927 theorem/lemma declarations, permitting only
`propext`, `Classical.choice` and `Quot.sound`. All 700 distinct
coverage/finding names were checked directly by Lean. Source checks
passed for all 138 manifest entries and 167 original statement hashes.
Coverage is 45 / 167: main 15 / 73, companion 30 / 94. There are
32 confirmed improvements, with no new manuscript version or Palomar
registration. Ubuntu-root space is 17.80 GiB.

Validated implementation of companion T20.7 and P1-MATH-0032:
[2ecbeb2a1c57c75e700e1efc63225a9107335400](https://github.com/Vulkin-prog/paper-p1-lean/commit/2ecbeb2a1c57c75e700e1efc63225a9107335400).


## Covered residual host counts and exact packing

The prescribed-plane and unrestricted host assertions of T20.8 are
proved on the actual covered three-window relation space. For each
arbitrary cover, its unpinned components meeting all three blocks give
an exact finite family of pairwise disjoint transverse motifs. Their
natural products equal the component products used by T20.7, so their
small-prime square constraints are literal. Component-to-vertex-set
injectivity preserves their exact count. The finite small-prime rank
cost is uniformly below any fixed fraction of B.

Consequently, if any cover has residual dimension at least eta*L,
then the triple admits at least (eta/4)*B actual disjoint transverse
square products, eventually and uniformly in all covers. T20.6 then
gives N^(1+epsilon) hosts and N^(-1+epsilon) original affine mass on
every prescribed polynomial family of integer planes. The cover stays
inside an existential host predicate and is never enumerated. The
bound holds before primitive filtering, and hence for the literal
primitive mass as well. The real cutoff H=C0*B is retained exactly.

The unrestricted N^(3/2+epsilon) count of primitive triples is also
proved. In fact it follows from the stronger elementary fixed-order
count of all primitive hosts, without a residual-dimension premise.
A new exact finite conversion from unordered families to injective
center functions supplies the r! enumeration factor and works at
every fixed r>=2. It preserves the original primitive predicate.

The six-vertex packing calculation itself is now exact and checked:
6*dim(R_D)+|D| <= 3B+3*s(D)+18*(pi(H)+2), where s(D) is the literal
number of free transverse components of size at most five. Its real
form gives (3B-|D|)/6+s(D)/2+3*(pi(H)+2). This includes arbitrary
covers and pins. The remaining unproved part of T20.8 is the exceptional
mass N^(-1+epsilon) needed to bound s(D) by a fixed constant simultaneously
for every cover. That small-component exclusion still needs the
unrestricted degree-one geometric count. It is not inferred from
packing or from the planar proposition.

T20.8 moves from not started to in progress; coverage stays 79/167
(main 28/73, companion 51/94), with 97 confirmed improvements. These
are applications and exact interfaces for existing improvements,
not a new counted finding. No external premise, manuscript edit,
dependency download or Palomar registration is introduced.

Verified with Lean v4.36.0-rc2: full lake build (11107 jobs), actual axiom audit of all 7200 theorem/lemma declarations, direct Lean checks of all 4917 ledger/finding references, source integrity (138 manifest entries and 167 numbered statements), and git diff --check. Only propext, Classical.choice and Quot.sound occur. Ubuntu root space after verification: 14.91 GiB.
