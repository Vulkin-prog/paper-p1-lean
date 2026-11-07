# Independent arrivals realizing the original positional comparison

Checkpoint P1-MATH-0992 clarifies main lemma 20.1. Its original arithmetic
rates, finite grid, polynomial weights and exponent 4/5 are preserved.
All 167 numbered statements retain their existing scope and coverage.

For a finite ground G and finite edge family E, set

```text
iota_x = sum_(e in E, x in e) q_e,
U_x ~ Poisson(p_x-iota_x),    V_e ~ Poisson(q_e),
Z_x = U_x + sum_(e in E, x in e) V_e.
```

All the U_x and V_e are mutually independent. Nonnegative single and edge
rates suffice for this finite construction. A finite product of genuine
Poisson probability measures supplies a concrete probability space; its
evaluation variables have exactly these laws and are independent. The
generic finite construction permits arbitrary finite packets; the original
arithmetic application uses the actual two-site good edges.

PositionalPoissonRealization identifies the law of each Poisson jump and
proves that multiplication of completed positional laws becomes convolution
of their probability measures. It then identifies the law of every finite
independent sum. Consequently every realization of the displayed arrivals
has exactly the completed single/pair target law. On a supported finite
ground, each original-grid event has its encoded configuration coefficient.
The measure identification uses a countable configuration space with
measurable singletons, satisfied by the arithmetic configuration space.

IndependentPositionalApproximation applies this identification to the original
dyadic block, good edges with cutoff 8(L+1), nominal site intensity 2^(-L)
and individual infinite joint moments q_e. The earlier internal incidence
bound supplies positivity of the single rates. For each fixed polynomial
degree j and epsilon>0, one threshold precedes every critical word length,
probability space and independent realization. The literal grid error

```text
sum_z (1+sum_x z_x)^j * |Pr(actual unsigned field=z)-Pr(Z=z)|
```

is summable and at most N^(-4/5+epsilon). The canonical product realization
has the same convergent comparison. Summability is transported from the
already proved full coefficient series using injectivity of grid encoding;
the inequality is not used as a substitute for convergence.

The canonical new declarations are
`PositionalPoissonRealization.field_coordinate`,
`hasLaw_single_pair_field`, `hasLaw_canonical_single_pair_field`,
`grid_probability_of_hasLaw`, and
`IndependentPositionalApproximation.main_20_1` and `main_20_1_canonical`.
The earlier coefficient and grid formulations remain available unchanged.

All 20 new theorems and four definitions passed a direct Lean v4.36.0-rc2
replay and exact axiom audit with warnings treated as errors. Only
`propext`, `Classical.choice` and `Quot.sound` occur. Whole-project replay
and integration of this clarification into the unnumbered version 1.7
appendix are pending.
