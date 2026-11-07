# Exact covariance matrix of the reference arrival field

Checkpoint P1-MATH-0994 gives the complete covariance of the literal Poisson
reference coordinates of main lemma 20.1, together with their required
second-moment integrability. The earlier weighted arithmetic comparison
retains its original rates, exponent 4/5 and fixed-degree regime.

For a finite ground G and finite packet family E, put

```text
r_x = p_x - sum_(e in E, x in e) q_e >= 0.
Z_x = U_x + sum_(e in E, x in e) V_e,
```

where all arrivals are mutually independent, U_x has Poisson(r_x) law and
V_e has Poisson(q_e) law. Every Z_x is square integrable, with mean and
variance p_x. The shared arrival indices give exactly

```text
Cov(Z_x,Z_y) = 1_(x=y) r_x + sum_(e in E, x in e and y in e) q_e.
```

When every packet has cardinality two, this is the full matrix

```text
Cov(Z_x,Z_y) = p_x                          if x=y,
               q_{x,y}                    if x!=y and {x,y} is in E,
               0                          otherwise.
```

The statements cover every independent realization on any probability
space and the explicit finite product Poisson law. Arbitrary ambient index
types are allowed; the proof needs no countability or measurable structure
on the full configuration space. Zero rates and empty packet families are
included.

These are identities for the reference arrivals. In the arithmetic model
the original indicator pair covariance would subtract the product of its
means from its joint probability; that different covariance is not
identified with the retained reference intensity here. Neither an improved
approximation rate nor coordinate independence is inferred from the matrix.

The main declarations in PaperP1.PositionalArrivalCovariance are
`covariance_coordinates`, `memLp_coordinate`, `variance_coordinate`,
`covariance_pair_matrix`, `covariance_canonical` and
`covariance_canonical_pairs`. The proof first derives square integrability
and the variance of a Poisson variable from its actual integrable factorial
tests, expands covariance over finite observed-cell sums, and identifies
their exact shared indices.

Eighteen theorems and one coordinate definition passed direct Lean v4.36.0-rc2 compilation with proof warnings as errors and exact permitted-axiom checks. Whole-project replay and manuscript integration are pending.
