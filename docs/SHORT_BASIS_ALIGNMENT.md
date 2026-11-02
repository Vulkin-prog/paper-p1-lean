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

## Remaining obligations

The quantitative prime harmonic estimate at z=floor(B^a), the short-
cycle construction with its length and retained-rank bounds, the
sparse fundamental kernel basis for the final small-prime/parity
equations, and the full asymptotic short-basis assembly remain open.
The retained candidate coordinate space is not counted as a complete-
relation subspace before the remaining equations are imposed.
Article13.1 is not counted proved. No source-conclusion error,
optimized constant, external graph bound, new Paper C source,
manuscript-byte change or Palomar registration is claimed.

## Validation

Lean v4.36.0-rc2 full build passed (10469 jobs); actual axiom audit passed for all 5737 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 3452 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records are intact. Ubuntu available space: 16.01 GiB. The actual retained component family, literal medium-prime columns, finite one-third heavy-column loss and oversized-component budget are proved. Both physical projections and the actual first-block prime-parity image are injective. Actual medium-prime equations equal selected physical-occurrence sums and have a constructed labelled incidence model with identical kernel. Quantitative short cycles, the prime harmonic estimate, sparse final kernel basis and full short-basis assembly remain open; article13.1 stays in progress. Coverage75/167 (main27/73, companion48/94); findings77. No source-conclusion error, external graph estimate, additional Paper C source, manuscript-byte change or Palomar registration.
