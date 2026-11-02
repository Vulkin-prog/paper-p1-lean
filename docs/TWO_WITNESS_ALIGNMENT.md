# Two-witness auxiliary: exact finite kernel budget

Source: companion Proposition T9.5, `p13:rig:two-witnesses`,
`companion_sections/pair_rigidity.tex:277`. Status: **proved**, including the field-norm moreover clause.
Coverage is 73/167 (main25/73, companion48/94).

## Explicit integer pigeonhole theorem

`SmallIntegerKernel` constructs the actual boxes of integer vectors
[0,M]^n and [-nHM,nHM]^t. Their exact cardinalities are proved, and
every matrix of entry height H maps the first box into the second.
A strict cardinal inequality gives two distinct vectors with the same
image; their difference is a nonzero integer kernel vector with every
coordinate at most M in absolute value.

`power_capacity` proves the cardinal inequality with M=(3nH)^7
whenever n,H>0 and 8t<=7n. Thus `exists_small_kernel` proves the exact
height bound without invoking an external Siegel lemma. This condition
is weaker than the source's t/(n-t)<6 requirement; the source dimension
budget is explicitly proved to satisfy both. The same height power 7
is retained. No improvement to the source final polynomial bound is
asserted from this observation alone.

## Actual coefficient slots and equation indices

`BiquadraticAuxiliaryCoordinates.CoefficientIndex` is the disjoint union
of the A0 rectangle of side 3q+1 and the three rectangles of respective
sides 3q-r_i+1 and 3q-s_i+1. Its exact cardinality is

    n=(3q+1)^2+sum_i (3q-r_i+1)(3q-s_i+1).

`EquationIndex` has the exponent pairs (a,b) with a+b<=6q. Its exact
cardinality is t=(6q+1)(6q+2)/2, with the total-degree bound proved
for every actual index. `BiquadraticAuxiliaryBudget` proves

    21q^2+18q+4 <=n <=4(3q+1)^2,
    t=18q^2+9q+1,   7t<6n,   8t<=7n.

The lower bounds assume only 0<=r_i,s_i<=q. A finite equivalence
transports the proved integer kernel vector back to the actual slot
set, and every original indexed equation vanishes.

## Height absorption

For 1<=q<=B, the upper dimension bound gives
3n<=(B+1)^(10q). If the matrix entry height H is at most
(B+1)^(cq), the actual kernel vector height is consequently at most
(B+1)^[7(10+c)q]. Both inequalities are explicit natural-number
statements, with no asymptotic premise left as an argument.

## Actual Runge matrix and explicit coefficient heights

`BivariateRungeCoefficients` proves the stars-and-bars coefficient bound
for all root-list sizes, including zero. Finite binomial integrality
gives the common denominator 2^(12q)=4^(6q) for every branch coefficient
of total degree at most 6q. For root lists of total size at most 4q and
offsets of absolute value at most B, the scaled integer coefficient has
height at most (B+1)^(28q). No analytic estimate is needed.

`BiquadraticRungeMatrix` constructs the literal rational convolution
entry at each equation/slot and its integral multiple. Slot shifts are
proved consistent with the source pole weights. The actual integer
matrix has the stated entry height. The proved indexed integer kernel
and dimension budget then give a nonzero coefficient array w with

    |w_i| <=(B+1)^(266q).

Every actual rational coefficient equation vanishes; no matrix or
coefficient-height estimate is supplied as an unproved premise.

## Actual formal numerator and integer coefficient polynomials

`BiquadraticFormalNumerator` uses nested formal power series, with inner
X and outer Y. Its four branch series are the actual products of the
univariate square-root binomial series. Every coefficient is identified
with the finite Runge formula. The numerator is the explicit finite sum
over the coefficient slots, shifted by 3q-r_chi-a and 3q-s_chi-b.
Its equation coefficients are exactly the constructed rational matrix
applied to w. Thus every coefficient of total degree <=6q is zero.

`BiquadraticCoefficientPolynomials` assembles the same array into four
actual integer bivariate polynomials. Coefficient extraction recovers
every slot exactly, so at least one polynomial is nonzero. Their partial
degrees are at most 3q-r_chi and 3q-s_chi, and every integer coefficient
has absolute value at most (B+1)^(266q). `exists_auxiliary` supplies all
these facts and the actual formal numerator cancellation together.

This replaces the first source Cauchy estimate by finite coefficient
combinatorics and gives explicit height constants (P1-MATH-0074).
It does not replace or prove the later integer-gap estimate.

## Actual primitive coefficient reduction

`PrimitiveCoefficientFamily.extract` proves finite common-factor
extraction in a normalized gcd monoid. For the actual four nonzero-family
integer polynomials, it supplies a nonzero common factor D and integer
quotients Q_chi. Every common divisor of all quotients is a unit; this
also removes common integer content. At least one quotient is nonzero.

`BivariateDivisionBounds` proves the exact reduced partial degree bounds
and derives an explicit quotient-height consequence of complete T9.4.
If the original partial degrees are at most 3q and its height is at most
(B+1)^(cq), the quotient height is at most (B+1)^[(c+9)q], for 1<=q<=B.
Zero coefficient polynomials are included in the same bounds.

`BiquadraticPrimitiveCoefficients.exists_primitive_coefficients` applies
these results to the actual constructed auxiliary family. It gives

    deg_X Q_chi <=(3q-r_chi)-deg_X D,
    deg_Y Q_chi <=(3q-s_chi)-deg_Y D,
    height(Q_chi) <=(B+1)^(275q).

The original formal numerator cancellation remains in the same existential
construction. The required cancellation statement for the DIVIDED
numerator is a separate remaining obligation, not a consequence silently
assumed from polynomial divisibility.

## Exact reciprocal order and coefficient-level division

`IteratedPowerSeriesEquiv` is a minimal selected adaptation of the
option-variable correspondence from Mathlib commit
`9d581dfff2e41de989072ea63abf3daf69311520`, source
`Mathlib/RingTheory/MvPowerSeries/Equiv.lean`, blob
`29a3a9340ea5d982e0c9af5f3444a9d25c463ca6` (Apache-2.0, Bingyu Xia
and Wenrong Zou). The four adapted proof declarations are part of
the project kernel audit. The selected correspondence keeps the
dependency budget focused on formal series.

`BivariateSeriesOrder` identifies every actual nested coefficient with
a coefficient of a two-variable multivariate series. Total order is
therefore multiplicative by the pinned Mathlib domain theorem.
A proved coefficient-level division theorem says: if D has finite
order delta and D*g has every coefficient of total degree <n zero,
then g has every coefficient of total degree <n-delta zero.

`BivariateTotalDegree` defines the ordinary total degree of a nested
integer polynomial and proves a nonzero coefficient attains it,
with total degree at most the sum of the partial degrees.
`BivariateReciprocalSeries` constructs the finite reversed coefficient
series explicitly, recovers every rectangular coefficient exactly,
and proves for nonzero P with partial degrees at most a,b:

    order(reciprocal(P,a,b)) =a+b-totalDegree(P).

Thus the exact order of the actual reciprocal common factor is proved.
The next checkpoint below supplies the actual product identity and
instantiates division in the source construction.

## Actual primitive numerator division

`BivariateReciprocalProduct` proves reconstruction from rectangular
integer coefficients, embeds the actual nested series domain injectively
in its fraction field, identifies every reciprocal with the corresponding
polynomial evaluation at inverse variables, and proves reciprocal
multiplication with arbitrary sufficient partial degree bounds.

`BiquadraticNumeratorFactor` identifies the original indexed numerator
with the sum over its four actual coefficient polynomials. It proves
that the old numerator equals the actual reciprocal common factor times
the reduced numerator. Zero coefficient polynomials are included; they
do not impose spurious degree equalities.

`BiquadraticPrimitiveOrder.exists_primitive_vanishing` constructs the
same actual w,D,Q as the prior primitive-coefficient theorem, retaining
nonzero D, a nonzero quotient member, no common nonunit divisor,
reduced partial degrees and height (B+1)^(275q). With k=3q, a=degreeX D,
b=degreeY D and e=totalDegree D, every coefficient of its reduced
numerator of total degree at most (k-a)+(k-b)+e is zero. Equivalently,
its order is at least (k-a)+(k-b)+e+1, exactly the source primitive-order
step. This follows from the proved product identity and exact reciprocal
order, without division by D(x,y). No target vanishing estimate is
supplied as an external assumption.

## Literal formal words and the nonzero norm

`BivariateWordSquares` treats actual finite offset sets I,J. Their word
polynomial is the product of the distinct factors X+i and Y+j. Every
nonempty word is proved nonsquare in Q(X,Y): an injective coefficient
localization gives a separable nonconstant univariate polynomial, while
integral closure reflects a fraction-field square to a polynomial square.
The empty word is correctly excluded from this nonsquare conclusion.

`FormalWordPolynomials` proves the exact overlap identity over every
commutative ring:

    F(I,J)*F(K,L) =F(I symmetricDifference K,J symmetricDifference L)
                    *F(I intersection K,J intersection L)^2.

It constructs the quotient H=F(K\I,L\J) with G*H=F(K,L), and
identifies the integer polynomials with their rational counterparts.
`BiquadraticNorm` proves the elementary normalized norm is zero iff all
four coefficients are zero when F1,F2,F1*F2 are nonsquares. The proof
uses quadratic anisotropy and a difference of squares; it assumes no
four-character basis.

`BiquadraticWordNorm.normPolynomial_ne_zero` applies this criterion to
the literal integer source norm U^2-4F1*V^2, using F3 from symmetric
difference and H from the proved quotient. It is nonzero for every
nonzero four-polynomial coefficient family whenever both words and their
symmetric difference are nonempty. `independent_of_distinct` derives
these conditions from two distinct nonempty word pairs. Evenness and
offset bounds are unnecessary for this nonzero-norm component.

`IntegerOverlapRoot` and `exists_third_root` construct the third integer
root from the two actual square roots and a nonzero overlap value, with
the required signed relation G*w3=w1*w2. Positivity of word values is
proved when the coordinates exceed the absolute offset bound.
The literal norm evaluates to zero if the actual auxiliary integer value
is zero. `auxiliary_ne_zero` proves nonzero auxiliary functions in every
injective domain realization of these radical identities; such a
realization is structural data, not an assumed target estimate.

This checkpoint records P1-MATH-0075, a separate algebraic proof
improvement. No analytic integer-gap estimate is inferred from it.

## Exact norm degrees and an explicit finite height bound

`FormalWordDegrees` proves the literal word partial degrees are exactly
the corresponding offset cardinalities. The symmetric-difference and
intersection cardinal identities give the quotient rank balance

    degreeX(H)+r1 =r2+r3,

and its Y analogue. `BiquadraticNormDegree` proves degree(U)<=2k,
degree(V)<=2k-r1, hence degree(R)<=4k over any commutative coefficient
ring. `BiquadraticWordNormDegree.q_bounds` gives the exact source
partial bounds 12q and total bound 24q, including zero coefficient
polynomials.

`PolynomialHeightArithmetic` proves finite coefficient height estimates
for sums, differences, scalar multiples and products. The bivariate
product cost is the literal rectangle
(dX(P)+dX(Q)+1)(dY(P)+dY(Q)+1), proved from the two finite coefficient
convolutions. `FormalWordHeight` proves linear-product height at most
(B+1)^card and word height at most (B+1)^(cardX+cardY); thus all three
word radicals and the intersection quotient have height <=(B+1)^(4q).

`BivariateHeightPower` absorbs every product rectangle of degrees <=32q
into (B+1)^(12q), uniformly for 1<=q<=B. The literal source norm built
from coefficients of height <=(B+1)^(275q) has height

    H(R) <=(B+1)^(1200q).

The internal verified exponent is already 1189; 1200 is a convenient
safe constant. This is a finite coefficient proof; the later analytic
integer-gap estimate is not inferred from it.

`BiquadraticAlgebraicAuxiliary.exists_auxiliary` assembles the same
actual w,D,Q,R with primitive nonzero coefficient family, all reduced
degrees, coefficient height 275q, numerator factorization, old and
primitive-order cancellation, literal nonzero word norm, norm partial
degrees 12q, total degree 24q and height exponent 1200q.
The general branch-list data remain explicit. Their identification with
the actual word radicals and the integer-gap step are not assumed.

## Geometric numerator coefficients and actual real branches

`BivariateBranchBounds` proves coefficient bounds for every shifted
formal branch and every actual reciprocal polynomial times that branch.
The literal rectangular coefficient count is retained.
`BiquadraticNumeratorBounds.geometric_bound` applies to the actual
reduced family for every pair of coefficient indices:

    |c_ab| <=(B+1)^(300q)*(2B)^(a+b).

It requires only the proved quotient height 275q, reduced partial
polynomial degrees, kx,ky<=3q, and the actual offset/rank bounds. It
includes zero polynomials, empty branch lists and arbitrary large a,b.

`RealSeriesEvaluation` defines the real value of a rational formal
series by its sum, proves absolute convergence from a geometric
coefficient majorant, and proves addition, Cauchy multiplication and
finite products for absolutely convergent series. This uses pinned
Mathlib's ordinary infinite-sum/Cauchy-product theorems, not an
analytic binomial theorem or an assumed branch identification.

`RealSeriesTail` bounds the nonconstant tail by r/(1-r).
`RungeSeriesValues` proves each actual formal factor converges for
|gamma*t|<1 and its real value squares to 1+gamma*t. When
|gamma*t|<=1/4 this value is positive. Its products are positive and
have the actual split-product square, including empty products. For
2r offsets, the scaled value x^r*value(1/x) squares exactly to
product_i(x+gamma_i), and positivity holds at positive x. The small
parameter condition follows from x>=4B and the actual absolute offset
bound. No square-root value is inserted as an axiom.

## Literal bivariate value and its actual vanishing tail

`WeightedGeometricTail` proves the ordinary weighted geometric sum and,
for 0<=r<=1/4, bounds its tail starting at M by
2*(M+1)*r^M. A real sequence with the corresponding norm majorant and
an actual zero prefix inherits this bound. M=0 and r=0 are included.

`BivariateSeriesValue` defines the actual term c_ab*xi^a*eta^b and sums
it over the literal finite antidiagonal a+b=n, before summing over n.
Every pair of coefficient indices is included exactly once. The
coefficient majorant |c_ab|<=C*R^(a+b), with |xi|,|eta|<=t, implies the
diagonal norm bound C*(n+1)*(R*t)^n and absolute convergence for R*t<1.
If the actual coefficients below total degree M vanish and R*t<=1/4,
then the actual real value satisfies

    |value(f,xi,eta)| <=2*C*(M+1)*(R*t)^M.

The actual formal branch value is identified with the product of its
two one-variable Runge values by the proved ordinary Cauchy product.
`BivariateSeriesOperations` proves finite sums and scalar multiples,
and proves convergence and value under the actual monomial shift.
The shifted antidiagonal identity is a finite bijection with its exact
zero prefix. No analytic-value or target tail premise is used to assert
these conclusions.

## Actual polynomial auxiliary values and finite word lists

`BivariateEvaluation` defines nested integer-polynomial evaluation in
any commutative ring and proves its compatibility with integer-point
casting. Its finite reciprocal coefficient sum, scaled by x^a*y^b,
is exactly the polynomial evaluation at nonzero field coordinates.

`BivariateReciprocalValue` expands every actual reciprocal polynomial
times a branch as the literal finite sum of scalar monomial shifts.
It proves convergence and the real reciprocal-branch value formula.
Scaling gives the actual polynomial evaluation times the branch value.

`BiquadraticAuxiliaryValue.primitive_pole_budget` proves the full
remaining-pole budget for each nonzero primitive quotient, retaining
the source r,s<=q assumptions. This hypothesis is needed to prevent
unrelated natural-subtraction saturation outside the source ranks.
`scaled_value` handles zero quotient members separately and proves
that the literal scaled numerator value equals the actual sum over
its four polynomial evaluations and scaled branch values. The identity
is not an assumed analytic-value premise.

`BiquadraticWordEnumeration` constructs injective root lists from the
actual finite word sets. The four offset sets are exactly
[empty,I,K,I symmetricDifference K], with lengths 2*blockRank(r,chi).
Every finite product on the list is the corresponding product on the
literal offset set. The actual absolute offset bounds are proved for
all characters, including the empty list. No arbitrary branch list is
silently declared to enumerate a word.

## The actual integer gap and vanishing polynomial

`PrimitiveTailScaling` proves the finite power budget and the actual
remaining-pole scaling. With K=kx+ky, K+1<=M<=6q+1, 1<=q<=B and
N>=8B, the scaled tail is at most (B+1)^(400q)/N. The proof compares
N^K/N^M with 1/N and absorbs the finite factors into exponent 326q,
then uses the convenient safe exponent 400q.

`BiquadraticAuxiliaryGap.primitive_bound` instantiates this estimate
for the actual w,D,Q and its proved divided cancellation:

    |auxiliaryValue(Q,x,y)| <=(B+1)^(400q)/N.

`BiquadraticWordValues` and `BiquadraticWordRealization` identify the
enumerated scaled branch values with the actual positive integer roots
of the two words and their symmetric difference. The third root is
derived, including its signed overlap relation; it is not an extra
square-point assumption. The actual auxiliary is the real cast of the
literal four-term integer polynomial-root expression. Integer separation
therefore forces it to be zero once N>(B+1)^(400q).

`TwoWitnessPolynomial.threshold` shows the convenient common source
threshold N>(B+1)^(1200q) implies N>=8B and the integer-gap threshold.
`exists_polynomial` constructs the same primitive nonzero coefficient
family Q and actual literal norm polynomial R with

    R !=0, R(x,y)=0,
    degreeX R,degreeY R <=12q,
    totalDegree R <=24q,
    height R <=(B+1)^(1200q).

The theorem is uniform for 1<=q<=B, the actual source half-ranks and
offset bounds, literal independent word sets, both actual integer-square
conditions and every comparable integer point N<=x,y<=2N. Thus it
includes the source half-open dyadic range. No tail, branch-value,
auxiliary-integrality or target point-vanishing premise is inserted.
This is the actual polynomial conclusion of T9.5. P1-MATH-0076 records
the separate real-series integer-gap proof improvement; P1-MATH-0075
retains the algebraic nonvanishing/degree/height improvement.

## The actual degree-four field norm and completed source theorem

`BiquadraticNormModel` constructs two actual quadratic algebras over
K=FractionRing(Q[X][X]). Literal formal independence proves that the
word functions f,g and fg are nonsquares. The tower is a field of
K-dimension four. `BiquadraticNormGenerators.generators_top` proves
that its two radical generators generate the full K-algebra.

The determinant definition of `Algebra.norm`, quadratic conjugation
and norm transitivity identify the auxiliary norm with the literal
source polynomial. The third radical is W1*W2/G; its square and exact
overlap relation are proved. `WordNormCertificate.Certificate` packages
the field, dimension, generators, nonzero auxiliary, four-term
expansion, radical identities and the actual Algebra.norm identity.
Its polynomial coefficients are the same primitive family Q as in the
point and height construction.

`TwoWitnessTheorem.companion_T9_5` assembles every source conclusion
with the explicit absolute constant c=1200. It permits real B and q,
1<=q<=B, by using floor(B) for the integer offsets and floor(q) for
the integer half-ranks. Monotonicity restores the original real power
thresholds and heights. Its partial degrees <=12*floor(q) and total
degree <=24*floor(q) imply the stated source bounds. The closed range
N<=x,y<=2N includes the source half-open dyadic range. In particular,
no integrality restriction on B or q has been inserted.

The four polynomial coefficients have every common divisor a unit,
which implies the source absence of a common nonconstant factor.
No target norm-nonzero, basis, tail bound, value identity, auxiliary
integrality or point-vanishing premise is assumed. T9.5 is now proved;
the subsequent article common-curve theorem13.2 remains open. Confirmed
findings remain76; this completes the existing improvements 75 and76.
No new external estimate, Paper C source, manuscript-byte change or
Palomar registration is introduced.
