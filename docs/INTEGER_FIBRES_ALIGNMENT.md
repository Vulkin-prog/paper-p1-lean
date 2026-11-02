# Actual noncritical fibres and the integer offset-grid problem

Source: article proposition13.3, `p13:rig:grid-fibres`,
`main_sections/pair_rigidity.tex:166`. Status: **in progress**.
Coverage remains74/167 (main26/73, companion48/94).

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

## Remaining obligations

The coordinate restrictions excluding the bad offsets must still be
assembled with the class-map kernel and injective physical projections
to derive the dimension and final actual integer-grid lower bound.
These quantitative assembly steps remain open; article13.3 is not
counted complete. Coverage stays74/167 and confirmed findings now77.
No new external estimate, Paper C source, manuscript-byte change or
Palomar registration is introduced.

## Validation

Lean v4.36.0-rc2 full build passed (10443 jobs); actual axiom audit passed for all 5652 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 3367 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records are intact. Ubuntu available space: 16.05 GiB. Actual simple-root lifting follows from proved power-series adic completeness and Hensel after unit leading-coefficient normalization. The actual formal branch, exact curve substitution kernel, injective coordinate-ring map and actual function-field fraction map are proved. An unmatched selected fibre gives an actual T-times-unit word series, irreducible and nonsquare in its fraction field; actual functional squares therefore force an integer-offset match. No normalization, branch, valuation, kernel or target matching conclusion is assumed as an external theorem. This confirms P1-MATH-0077. Coordinate-cut dimension and final grid-count assembly remain open; article13.3 stays in progress. Coverage74/167 and findings77. No new manuscript conclusion error, external estimate, Paper C source, manuscript-byte change or Palomar registration.
