# Actual noncritical fibres and the integer offset-grid problem

Source: article proposition13.3, `p13:rig:grid-fibres`,
`main_sections/pair_rigidity.tex:166`. Status: **proved**.
Coverage75/167 (main27/73, companion48/94).

## The actual exceptional polynomials

`BivariateCurveDegrees` proves that both actual partial degrees are
bounded by the actual total degree, that Y-differentiation cannot
increase X-degree, and that exchanging variables exchanges their
partial degrees.

`PolynomialDeterminantHeight.determinant_degree` bounds the actual
determinant degree by matrix size times entry degree, using the
permutation expansion and actual finite product degrees.
`BivariateResultantHeight.resultant_degree` applies this to the actual
Sylvester matrix. No resultant degree is inserted as a target premise.

`CurveCriticalFibres` constructs

    critical(C) = leadingCoeff_Y(C) * Res_Y(C, derivative_Y(C)).

For an irreducible curve of positive Y-degree this is a nonzero integer
polynomial: the derivative is nonzero in characteristic zero, and its
strictly smaller Y-degree forbids divisibility by C. The already
proved actual resultant nonvanishing then applies.

The critical polynomial has degree at most dX+2*dX*dY. Its actual
negative integer roots form the finite set `badOffsets`; membership is
proved equivalent to vanishing of the critical polynomial at -u.
Outside it, both the leading coefficient and the derivative resultant
are nonzero. The actual root-cardinality bound gives

    card(badOffsets(C)) + card(badOffsets(swap(C))) <=6*D^2,

where D is the actual total degree. There is no dependence on heights,
the ambient box or the size of the word space.

## The actual specialized fibres

`CurveFibreRegularity` specializes the original integer polynomial at
X=-u and embeds its coefficients in any characteristic-zero field.
Outside the actual exceptional set its degree is exactly dY. The
actual resultant remains nonzero under this specialization. Derivative
compatibility and the native resultant criterion prove separability.
Every actual root therefore has nonzero derivative. Over an
algebraically closed field the actual finite root set has exactly dY
elements. The evaluation at an integer second offset is identified
with the cast of the original integer curve equation.

Geometric integrality of C after field extension is not assumed.
The source irreducibility is used over the original integer ring,
and the specialized separability follows from the actual resultant.

## Actual formal branch and functional-square root matching

`PowerSeriesHenselLift` proves the formal lifting theorem for a
polynomial over K[[T]] with unit leading coefficient and a simple
root modulo T. The polynomial is normalized to be monic, and the
actual T-adic completeness instance proves the Henselian hypothesis.
The result is a genuine root series with the prescribed constant term.
Only the two required Mathlib modules and their missing dependencies
were cached (42 files), on the Ubuntu partition.

`CurveFormalBranch` constructs X(T)=T-u and the actual integer-curve
polynomial over K[[T]]. The coefficient/constant-term diagram is exactly
the already proved regular fibre. Every regular fibre root z therefore
lifts to Y(T), with Y(0)=z and C(T-u,Y(T))=0. The coefficient lift is
proved injective using the actual Taylor ring equivalence and the
polynomial-to-power-series embedding.

`CurveSeriesField` proves that the full substitution kernel is (C):
a nonmultiple in the kernel would force a nonzero actual resultant
in X to vanish at the transcendental formal parameter. The actual
coordinate ring consequently injects into K[[T]], and its fraction
field maps into Frac(K[[T]]), with exact specialization compatibility.

`CurveWordSeries` evaluates the literal finite word products along
this branch. If u is selected and z is not matched by a selected
second-block offset, the actual word series is T times an explicitly
constructed unit. `PowerSeriesSquareGap` proves this is irreducible
and nonsquare; integral closure of the power-series ring shows it
remains nonsquare in its actual fraction field.

`CurveSquareMatching.root_matches_offset` maps the actual functional
square into that fraction field and derives a contradiction. Thus
every regular selected first-block fibre root is -v for an actual
selected second-block integer offset. No normalization, branch,
valuation, substitution-kernel or target matching fact is an unproved
premise. The theorem holds over any characteristic-zero field containing
the chosen root; geometric integrality is not required.
P1-MATH-0077 records this local proof improvement for future integration.

## The actual coordinate cut and support unions

`CurveCoordinateCut` constructs the kernel of the actual functional
square-class map on V, then the kernel of the actual evaluations at
the two finite bad-offset sets. Rank-nullity gives retained dimension
at least t-1-6D^2. Every retained word is proved to have a literal
functional-square polynomial; every selected coordinate is regular.

`FiniteSupportImageRank` proves that an injective finitely supported
projection has rank at most its actual basis-support union cardinality.
Coordinate functionals show that these unions support every vector.
The bounded original basis therefore bounds every retained word.
Injectivity of both source physical projections is preserved on the
constructed nested kernels.

## Both actual integer-fibre counts

`CurveIntegerFibres` defines the actual finite integer grid and fibres
by filtering the offset box with C(-u,-v)=0. Complex polynomial roots
have the full distinct-root cardinality outside the bad offsets.
Hensel root matching puts each root in the negative integer image of
the selected second-block support, proving at least dY points in each
selected first-block fibre. The actual grid cardinality is the sum
of its fibre cardinalities.

`CurveSwapField` constructs the injective map of actual coordinate
rings under variable exchange and the induced actual fraction-field
map. Specialization commutes with it, so actual functional squares
transport to the swapped literal word. Swapping the grid preserves
its cardinality. Applying the same argument gives dX times the
retained dimension. No horizontal matching or field transport is an
assumed input.

`IntegerGridTheorem.certificate_grid_bound` applies to any actual
common-curve certificate with both injective physical projections.
`article_13_3` constructs such a certificate through the fully proved
article13.2 from the original actual bounded even independent basis,
real B,q and comparable integer points. It keeps the point, degree
and height conclusions and proves

    #grid >= max(dX,dY) * (t-1-6D^2).

Both the original real inequality and its natural truncation at zero
are proved. `mem_real_grid` identifies membership exactly with integer
points in [-B,B]^2 satisfying the original curve equation. This is the
full numbered proposition with explicit safe constant6, independent
of t,B and the curve degree. No optimized constant or source-conclusion
error is asserted. P1-MATH-0077 records the proof improvement.
No external point-count estimate, Paper C source, manuscript-byte
change or Palomar registration is introduced.

## Validation

Lean v4.36.0-rc2 full build passed (10457 jobs); actual axiom audit passed for all 5685 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 3400 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records are intact. Ubuntu available space: 16.04 GiB. Full article13.3 is proved through the actual common-curve certificate, the actual class-map and exceptional-coordinate kernels, bounded basis supports, both injective physical projections, actual Hensel root matching and the actual swapped function-field map. The retained dimension is at least t-1-6D^2 and the actual integer-grid lower bound has constant6. Original real parameters, exact real-box grid membership and the original real/truncated natural lower bounds are proved. No branch, normalization, matching, dimension-loss or target grid count is an unproved input. Coverage75/167 (main27/73, companion48/94); findings77. No optimized constant, source-conclusion error, external point-count estimate, Paper C source, manuscript-byte change or Palomar registration.
