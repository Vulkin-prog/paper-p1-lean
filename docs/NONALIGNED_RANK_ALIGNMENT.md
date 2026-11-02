# Actual finite nonaligned-rank stages

Source: article13.6, `p13:rig:nonaligned`, `main_sections/pair_rigidity.tex:259`. Status: **in progress**.

`BivariateLineGeometry` proves that an actual total-degree-one
nested integer polynomial is a literal nonconstant linear form. Its
actual zero points satisfy the exact collinearity determinant.

`BoundedPointAlignment` proves that two distinct actual integer points
p,q in[-B,B]^2, collinear with a center(x,y) having x,y>B, force
positive reduced coefficients a,b<=2B and

    abs(b*x-a*y) <= (a+b)B.

Ordering the first coordinates forces the second coordinates to have
the same order, because both center differences are positive. Actual
gcd division gives positive coprime coefficients, the small coefficient
bounds and the exact reduced affine error. For B>=2 this is the actual
source alignment with allowed coefficient height B^3.

`LinearCurveAlignment.actual_linear_case` applies the already proved
actual common-curve grid bound. At total degree1, actual relation rank
at least9 leaves at least two bounded integer points after the safe
exceptional budget6. The actual positive-center alignment follows.
Consequently, nonalignment excludes degree1 for such an actual common
curve. No line coefficient-height estimate, sign input or additional
functional-square/root-matching witness is supplied.

P1-MATH-0080 records this proof simplification. It does not remove the
common-curve construction or its point threshold from the full argument.
The critical asymptotic threshold assembly, the actual degree>=2 BCN
input/geometric specialization, and the final nonaligned contradiction
remain open. Article13.6 stays in progress. Coverage76/167, confirmed
findings80; no new external theorem, Paper C source, dependency download,
manuscript-byte change or Palomar registration.

## Validation

Lean v4.36.0-rc2 full build passed (10537 jobs); actual axiom audit passed for all 5935 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 3651 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records are intact. Ubuntu available space: 15.90 GiB. Every actual degree-one nested integer polynomial has a proved nonconstant linear form and actual collinear zero points. Two actual bounded distinct integer points and a center with both coordinates>B give positive reduced alignment coefficients<=2B and exact affine error<=(a+b)B. Actual gcd reduction, sign, coefficient bounds and source-height conversion are proved. The already proved actual common-curve grid lower bound supplies two such points at relation rank>=9 when D=1. Nonalignment therefore excludes degree1 for that actual common curve. P1-MATH-0080 records the proof simplification: no coefficient-height sign argument or additional functional-square/root-pairing witness is needed in the linear branch. The original curve construction and point  threshold remain necessary. Critical threshold assembly, unformalized BCN/geometric specialization and the final nonaligned contradiction remain open;13.6 stays in progress. Coverage76/167 (main28/73, companion48/94); confirmed findings80. No optimized threshold, source-conclusion error, new external theorem, added Paper C source, cache download, manuscript-byte change or Palomar registration.
