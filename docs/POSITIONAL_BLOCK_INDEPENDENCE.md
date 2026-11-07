# Full finite-block independence of the Poisson reference field

Checkpoint P1-MATH-0996 strengthens the preceding two-coordinate criterion
to complete finite vectors of actual natural-valued reference counts.
For arbitrary finite blocks A,B, including possible overlap, it proves

```text
(Z_x)_(x in A) and (Z_y)_(y in B) are independent
    iff Cov(Z_x,Z_y)=0 for every x in A and y in B.
```

This equivalence is specific to the stated independent Poisson packet
construction. In general, independence of every cross pair does not imply
independence of the two whole vectors. The proof here represents each
whole block as a measurable function of its finite tuple of arrival cells.
The total rate of all shared cells is zero exactly when it vanishes for
each cross pair of observed sets. Shared zero-rate cells vanish almost
everywhere, and the remaining disjoint tuples are genuinely independent.
The tuple construction and the almost-everywhere vector identity are
formalized explicitly.

For a pair packet family and disjoint coordinate blocks this is exactly

```text
the two full block vectors are independent
    iff every retained edge crossing between A and B has rate zero
    iff no positive-rate retained edge crosses between A and B.
```

Consequently the graph of positive-rate retained edges has the standard
dependency-graph property: disjoint vertex blocks with no crossing graph
edge carry independent complete random vectors. The weaker condition of
no retained crossing edge is also sufficient. No positivity of every
retained rate is assumed. For any measurable events C,D on independent
blocks, the joint probability is exactly the product of the probabilities.

All results hold for every independent realization and the canonical
finite product Poisson law. Arbitrary finite packets, empty blocks,
degenerate rates and arbitrary ambient index types are allowed. For
overlapping blocks the full cross-covariance criterion still applies;
the pair-edge formulation explicitly requires disjoint blocks. These are
properties of the reference arrival construction. The original arithmetic
field, comparison exponent 4/5 and fixed-degree regime are preserved.

The main declarations in PaperP1.PositionalBlockIndependence are
`independent_tuples_iff`, `independent_sum_blocks_iff`,
`independent_blocks_iff_cross_covariance_zero`,
`independent_pair_blocks_iff_cross_rates_zero`,
`independent_pair_blocks_iff_no_positive_crossing`,
`independent_canonical_pair_blocks_iff` and `independent_pair_block_events`.

Eighteen theorems and three definitions passed direct Lean v4.36.0-rc2 compilation with proof warnings as errors and exact permitted-axiom checks. Whole-project replay and manuscript integration are pending.
