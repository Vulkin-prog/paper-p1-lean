# Exact independence of the reference arrival coordinates

Checkpoint P1-MATH-0995 proves the sharp independence criterion for the
actual Poisson reference arrivals of main lemma 20.1. It includes the
natural-valued counts and their real versions, arbitrary finite packets,
every independent realization, and the explicit product law.

For independent Poisson cells X_a of nonnegative rates mu_a and any two
finite sets S,T of cell indices, the exact criterion is

```text
sum_(a in S) X_a and sum_(a in T) X_a are independent
    iff sum_(a in S intersection T) mu_a = 0.
```

The forward direction uses square integrability and the exact covariance.
For the reverse direction, nonnegativity forces each shared rate to zero.
Such a cell is almost surely zero by its actual Poisson law. Removing all
shared cells almost everywhere leaves sums of disjoint independent cell
families, which are genuinely independent.

For two distinct reference sites x,y this gives

```text
Z_x and Z_y are independent
    iff sum_(e in E, x in e and y in e) q_e = 0.
```

In a pair family, they are independent exactly when {x,y} is absent from E
or q_{x,y}=0. Equivalently, dependence occurs precisely when that edge is
retained and has strictly positive rate. A reference coordinate is
independent of itself exactly when p_x=0. Empty families and degenerate
rates are included; no countability or measurable structure is required
on the ambient configuration space.

This is a special property of the stated independent Poisson construction.
It asserts neither a general implication from zero covariance to
independence nor independence for the original arithmetic indicators.
The arithmetic approximation keeps its original rates, exponent 4/5 and
fixed-degree quantifier order. Pairwise statements alone do not assert
independence of arbitrary coordinate blocks.

The main declarations in PaperP1.PositionalArrivalIndependence are
`independent_nat_sums_iff`, `independent_real_sums_iff`,
`independent_distinct_coordinates_iff`, `independent_pair_counts_iff`,
`dependent_pair_coordinates_iff` and `independent_canonical_pairs_iff`.

Full Lean v4.36.0-rc2 replay passed at source 5d76e8c2ea7f8b3b4eb810c56db23330b3f0499b: 18,595 build jobs, 19,691 source-discovered theorem axiom checks and 19,833 distinct declaration-reference checks, all actual process exits 0. Proof warnings are errors; only propext, Classical.choice and Quot.sound occur.

The full replay and compressed original logs are preserved in [the validation record](validation/checkpoint-0995/validation.json). The clarification is integrated in the unnumbered version 1.7 companion appendix, under Realize the positional target by independent arrivals. Both PDFs were rebuilt and reviewed: 65 article pages and 102 companion pages. All 167 numbered statement blocks are preserved. See [the manuscript validation](manuscript-v1.7-validation.json).
