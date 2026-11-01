# Relative participation — a proved extension of main Theorem 10.1

`RelativeBlockRelationsCount.uniform_count` proves the same half-count
N^(r/2+epsilon) under a weaker hypothesis than a single full-support
relation. This is P1-MATH-0065. Main 10.1 was already complete; this
extension adds no new numbered result.

## Actual weaker condition

`RelativeBlockRelations.Covered blocks O n` states that for every new
coordinate i there exists a tuple u of actual effective block vectors with
u_i nonzero and total in the full old value span. The tuple u may depend
on i, and its other coordinates may be zero. A single full-support witness
satisfies this condition. The distinction matters over F2: three equal
nonzero one-dimensional spaces each participate in a pair relation, while
three nonzero projections cannot sum to zero simultaneously.

The complete count is uniform in every fixed number s of old sources,
all old positions and old block shapes, arbitrary finite candidate-centre
sets, and every fixed logarithmic signed-distance bound. Actual values
satisfy a fixed positive comparable height bound. The old space is the
full value span. Overlap, dependence and empty old blocks are included.
No nonzero-modulo-old condition is substituted for an own-space condition.

## Actual support extraction and remaining population

Choose one coordinate and one actual relative relation that is nonzero
there. Its nonzero support is nonempty. `group_exists` constructs an actual
finite bijection separating the zero and nonzero coordinates, preserving
every block value and centre. No minimal dependent support is needed.
The nonzero group satisfies exactly the complete 10.1 full-support
hypothesis relative to the fixed old sources.

For any other coordinate, use its own original relation. Decompose its
actual sum into the exposed and remaining groups. The exposed effective
vectors belong to their actual full value spans. Submodule subtraction
therefore places the remaining sum in the old span enlarged by all exposed
full blocks. Its designated own-space projection remains nonzero.
`remainder_covered` proves this exact invariant for the actual tuple.

`FiniteBlockAppend` proves that concatenating the fixed old and exposed
block tuples gives exactly the union of their actual full value sets,
and preserves the literal height and signed-distance hypotheses.

## Genuine simultaneous induction and finite enumeration

The actual tuple population and actual split classes are finite sets.
At a fixed exposed-group tuple, the full tuple is determined injectively
by its remaining coordinates. `fibre_count` maps that actual fibre into
the actual smaller relative-participation population. `cell_count` sums
these actual fibres over the actual full-support exposed tuples.

Strong induction in the number of new targets, simultaneously for every
old-source count, instantiates all remaining counts. At each split the
remaining target count k is strictly smaller; the old-source count increases
by the nonempty exposed group size. The complete 10.1 count is instantiated
for that actual group. Internal margins epsilon/4 give a class exponent
r/2+epsilon/2. There are finitely many group-size/bijection codes depending
only on r. Their fixed factor is absorbed by the remaining margin.
Every common threshold is chosen before positions, candidate sets or shapes.
There is no unproved extension, group or target population bound.

## Canonical connectedness and source status

`ConnectedRelations.coordinate_relation` works with the manuscript's
actual finest relation-respecting partition. If a coordinate were zero
in every global relation, the partition isolating it would be direct.
It would contradict a single canonical component with at least two indices.
Thus every coordinate has an actual nonzero global relation.

`ConnectedBlockLists.covered_of_connected` transports this fact to actual
finite effective blocks. `ConnectedBlockCount.uniform_count` gives their
actual connected tuple host count by the proved relative-participation
estimate with no old sources. It does not identify connectedness with one
full-support relation.

Main Corollary 10.2 is still in progress for original-window/set-family
alignment, primitive families and the actual independent-mass statement.
See [its precise scope](CONNECTED_FAMILY_ALIGNMENT.md). Numbered coverage
remains 64/167 (main 21/73, companion 43/94); confirmed improvements are 65.
No external unproved input, new Paper C port or manuscript-byte change occurs.

Verification checkpoint: Lean v4.36.0-rc2 full build passed (9,821 jobs); actual axiom audit passed for all 4,501 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 2,216 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records remain intact. Ubuntu available space: 17.20 GiB. No unproved group, extension or target count, new external input, Paper C port, manuscript-byte change or Palomar registration. Coverage remains 64/167; confirmed improvements are 65; main 10.2 is still in progress.

Proof checkpoint: [2e1bbd65872d4f73927ba606ef20cb592c8b81bb](https://github.com/Vulkin-prog/paper-p1-lean/commit/2e1bbd65872d4f73927ba606ef20cb592c8b81bb).
