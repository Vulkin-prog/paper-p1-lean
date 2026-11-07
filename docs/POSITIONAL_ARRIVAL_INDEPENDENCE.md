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

Eighteen theorems passed direct Lean v4.36.0-rc2 compilation with proof warnings as errors and exact permitted-axiom checks. Whole-project replay and manuscript integration are pending.
