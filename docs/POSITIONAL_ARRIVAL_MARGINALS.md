# Exact marginal laws and factorial moments of the reference arrival field

Checkpoint P1-MATH-0993 strengthens the independent-arrival interpretation of
main lemma 20.1. Its original grid, arithmetic rates, exponent 4/5 and
fixed-degree asymptotic regime are preserved.

Let G be any finite ground and E any finite family of finite packets. For
nonnegative packet rates q_e and compensated single rates

```text
r_x = p_x - sum_(e in E, x in e) q_e >= 0,
```

take mutually independent arrivals with laws Poisson(r_x) and Poisson(q_e).
At a site x in G, the reference count Z_x is its single arrival plus every
packet arrival containing x. Coordinates can share packet arrivals.

The observed-cell set contains exactly these arrival indices. A finite sum of
independent Poisson variables has the sum of their parameters, and the actual
observed parameter sum is proved to equal p_x. Thus Z_x has exactly the
Poisson(p_x) law in every independent realization, including the explicit
finite product realization. The proof handles arbitrary finite packets and
any ambient index type; it requires no countability or measurable-space
assumption on the full configuration space.

For every natural order j, the actual factorial test is integrable and

```text
E[(Z_x).descFactorial(j)] = p_x^j.
```

This includes zero rates and order zero. Integrability is proved from the
convergent Poisson factorial-moment series, then transported through the
actual marginal law. The integral identity therefore includes the required
convergence assertion. These are exact identities for the Poisson reference
arrivals; the arithmetic approximation keeps its existing fixed-degree scope.

The main declarations in PaperP1.PositionalArrivalMarginals are
`rate_sum_observed`, `hasLaw_coordinate`, `hasLaw_canonical_coordinate`
and `coordinate_factorial_moment`. The generic finite-sum and law-transfer
lemmas are included in the complete audit. The earlier completed-law and
weighted-grid formulations remain available unchanged.

All twelve new theorems and the observed-cell definition passed direct Lean
v4.36.0-rc2 compilation and exact axiom audit, with proof warnings as errors.
Only `propext`, `Classical.choice` and `Quot.sound` occur. Whole-project replay
and integration of this clarification into the version 1.7 appendix are pending.
