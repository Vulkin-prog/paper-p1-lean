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

Full Lean v4.36.0-rc2 replay passed at source 72c3ec562b832d46779a7fff91b52a750b43ebfb: 18,593 build jobs, 19,673 source-discovered theorem axiom checks and 19,815 distinct declaration-reference checks, all actual process exits 0. Proof warnings are errors; only propext, Classical.choice and Quot.sound occur.

The full replay and compressed original logs are preserved in [the validation record](validation/checkpoint-0994/validation.json). The clarification is integrated in the unnumbered version 1.7 companion appendix, under Realize the positional target by independent arrivals. Both PDFs were rebuilt and reviewed: 65 article pages and 102 companion pages. All 167 numbered statement blocks are preserved. See [the manuscript validation](manuscript-v1.7-validation.json).
