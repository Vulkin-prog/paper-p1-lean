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

Full Lean v4.36.0-rc2 replay passed at source 2d09439656cc0f923203a465582324237b5bb4cb: 18,591 build jobs, 19,655 source-discovered theorem axiom checks and 19,796 distinct declaration-reference checks, all actual process exits 0. Proof warnings are errors; only propext, Classical.choice and Quot.sound occur.

The full replay and compressed original logs are preserved in [the validation record](validation/checkpoint-0993/validation.json). The clarification is integrated in the unnumbered version 1.7 companion appendix, under Realize the positional target by independent arrivals. Both PDFs were rebuilt and reviewed: 65 article pages and 102 companion pages. All 167 numbered statement blocks are preserved. See [the manuscript validation](manuscript-v1.7-validation.json).
