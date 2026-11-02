# Growing-degree point counts: proved analytic reduction, explicit BCN input

Source: article13.4 and corollary13.5 in
`main_sections/pair_rigidity.tex:214,228`.
Status:13.4 **in progress**;13.5 **conditional** on the named
`PlaneCurvePointCount.UniformBound c kappa` input.
Neither row adds proved coverage:76/167, confirmed findings79.

## Primary input and exact conditional scope

The specified [author version, arXiv2302.04209v2](https://arxiv.org/pdf/2302.04209v2),
20September2023, Theorem2, equation(27), page7, was inspected.
It gives a degree-uniform bound c(n)D^2 H^(1/D)(log H)^kappa
for integer points on integral curves over a subfield of C, H>2.
Its coefficients and degree do not enter c(n).

`UniformBound` is only an ordinary explicit hypothesis in separate
conditional theorems. It quantifies over actual irreducible nested
plane polynomials over characteristic-zero fields with an algebra
structure on C, their literal coefficient-support total degree, and
their literal integer-coordinate grids. The external theorem proof
and geometric curve/polynomial specialization remain unformalized.
There is no global axiom or claimed proof of13.4.

## Actual grids and source boxes

`PlaneCurvePointCount.grid` filters the actual finite integer box by
the actual polynomial evaluation. `mem_real_grid` proves exact real
box membership using the natural floor. The degree agrees exactly
with the existing integer nested-polynomial total degree. An actual
negation bijection identifies its cardinality with the negative-
offset grid already used in the proved proposition13.3.

## Proved analytic endpoint estimate

For s=log D, the logarithm of the actual profile D^2 H^(1/D) is

    2s + log(H)*exp(-s).

This is convex for H>=1. The actual convex maximum principle gives
the profile maximum at an endpoint of every interval2<=D<=M.
When M>=log H, the large endpoint is<=e M^2. Splitting at log H
also proves the unconditional cap-growth-free estimate

    D^2 H^(1/D) <= 4sqrt(H) + e*(M^2+(log H)^2).

No differentiation, endpoint maximum, exponential bound or target
little-o estimate is an unproved theorem argument.

## Exact uniform source consequence under BCN

The ratio log(c0 B)/log B tends to1, and every fixed real power of
that ratio tends to1. Thus the actual logarithmic weight at height
c0 B is at most twice(log B)^kappa eventually. Actual logarithmic-
power limits absorb(log(c0 B))^2 into sqrt B. Under the explicit
BCN input, a single constant before all fields, degrees, coefficients
and caps gives the exact source bound

    #grid <= A*(sqrt(B)+M^2)*(log B)^kappa.

The actual two-power envelope tends to zero after division by B
uniformly for2<=D<=B^b, every fixed0<b<1/2. For any upper power
cap and0<=a<1/2, choose fixed b between a and1/2. This proves the
source uniform o(B) conclusion under the same named BCN hypothesis.
All thresholds precede every varying polynomial, field and degree.

`upperPowerCap_of_log_ratio` proves that the source positive-cap
logarithmic-ratio exponent condition implies this upper-cap input.
`article_13_5_under_BCN` combines both the source big-O bound and
the uniform little-o statement. It is conditional and is counted as
such; the original broad algebraic-variety presentation is not silently
identified with a proved Lean geometric specialization.

## Recorded improvement and remaining input

P1-MATH-0079 records that only an upper cap is needed and that a=0
is allowed, including bounded and polylogarithmic caps. The analytic
improvement is unconditional; the curve-count consequence retains its
explicit BCN argument. No source-conclusion error is claimed.
Full BCN and its algebraic-geometric specialization remain open.
No new Paper C source, dependency cache or manuscript change was made.

## Validation

Lean v4.36.0-rc2 full build passed (10525 jobs); actual axiom audit passed for all 5900 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 3616 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records are intact. Ubuntu available space: 15.93 GiB. Actual finite plane-polynomial integer grids, exact real floor boxes and a negation bijection to the previously used offset grid are proved. Convex logarithmic degree profiles prove the endpoint maximum and the cap-growth-free bound4sqrt(H)+e*(M^2+(log H)^2). All real-logarithmic weights and uniform little-o limits are internally proved. The actual source big-O and uniform o(B) grid-count conclusions retain PlaneCurvePointCount.UniformBound c kappa as an ordinary explicit argument. The external BCN proof and geometric plane-polynomial specialization remain open; no global axiom or completed proof of13.4 is introduced. Article13.5 is conditional and adds no proved coverage. P1-MATH-0079 records that only an upper degree cap and0<=a<1/2 are needed. Coverage76/167 (main28/73, companion48/94); confirmed findings79. The exact primary author version arXiv2302.04209v2, Theorem2 equation(27), page7 was checked. No extra Paper C source, dependency download, manuscript-byte change or Palomar registration.
