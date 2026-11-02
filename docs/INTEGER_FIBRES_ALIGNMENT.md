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

## Remaining obligations

A functional square must force each root of a selected regular fibre
to match a selected second-block offset. This local matching statement
has not been proved or assumed as an unconditional input.
The coordinate restrictions excluding the bad offsets must be assembled
with the class-map kernel and injective physical projections to derive
the dimension and final actual integer-grid lower bound. These steps
remain open. Article13.3 is not counted complete, and no new independent
mathematical correction or improvement is confirmed at this checkpoint.
No external estimate, new Paper C source, manuscript-byte change or
Palomar registration is introduced.

## Validation

Lean v4.36.0-rc2 full build passed (10359 jobs); actual axiom audit passed for all 5628 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 3343 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records are intact. Ubuntu available space: 16.10 GiB. Actual nonzero exceptional polynomials, exact bad-offset membership and the combined6D^2 budget are proved. Regular specialization over any characteristic-zero field preserves degree and is separable; each root has nonzero derivative, and the actual finite root set over an algebraically closed field has cardinality dY. Literal integer point evaluations are retained. Functional-square root matching, coordinate-cut dimension and the final integer-grid lower bound remain open, so article13.3 stays in progress. Coverage74/167 and findings76 are unchanged. No new external estimate, Paper C source, manuscript-byte change or Palomar registration.
