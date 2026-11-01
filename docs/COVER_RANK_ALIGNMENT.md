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
