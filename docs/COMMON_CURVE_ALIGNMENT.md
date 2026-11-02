# Common-curve theorem: point factors and functional square-class collapse

Source: article theorem13.2, `p13:rig:common-curve`,
`main_sections/pair_rigidity.tex:127`, with its companion proof in
`companion_sections/pair_rigidity.tex:434`. Status: **proved**, with explicit absolute constant1000000.
Coverage is74/167 (main26/73, companion48/94).

## The actual curve field

`CurveFunctionField` constructs the coordinate ring Z[X,Y]/(C) and
its fraction field for an actual irreducible integer polynomial C.
The ideal (C) is prime. The specialization kernel is proved exactly:

    specialize(C,P)=0 iff C divides P.

Positive Y-degree proves characteristic zero by excluding nonzero
integer constants from (C). Positive degree in both variables excludes
every factor X+i and Y+j from (C), so all finite word functions are
nonzero and define units in the fraction field. This is a concrete
model of the characteristic-zero function field of the curve.

## The actual field square classes and linear map

`FieldSquareClasses` constructs the additive group of field units
modulo doubles and its ZMod2-module structure. The zero class is
proved equivalent to an actual square in the field. Multiplication
and finite products become addition and finite sums. For nonzero a,b,

    IsSquare(a) or IsSquare(b) or IsSquare(ab)

is equivalent to one class being zero or their classes being equal.

`CurveNormCollapse` specializes the literal integer norm polynomial.
The exact overlap identities survive every ring homomorphism. If the
specialized norm is zero and some coefficient survives, the previously
proved anisotropy forces square-class dependence. If ker(specialize)
is (C), primitivity of the four coefficient polynomials proves that
some coefficient survives; the target image-rank assertion is never
inserted as a premise.

`CurveWordSquareClasses` instantiates this argument for the actual
curve fraction field. `PairwiseEqualSpan` proves that a family whose
nonzero values are pairwise equal spans at most one dimension, with
no dependence on its cardinality.

`CurveWordMap` defines the actual linear map from the two copies of
finitely supported integer-indexed ZMod2 selections. On the encoding
of finite offset sets it is exactly the class of the literal word
polynomial. A basis-span identity identifies its image on an arbitrary
word subspace with the span of the actual basis-word classes. Hence
pair norms divisible by C, with primitive coefficient families, imply
the dimension bound for the entire image, not just for a list of words.

`FormalWordEncoding` proves that every binary finitely supported
selection equals the finite-set encoding of its actual support, and
that this encoding is injective. Distinct actual basis vectors give
literal independent words, without an additional independence premise.

## Constructing the first irreducible factor through the point

`IrreduciblePointFactor` uses actual irreducible factorization and
an integral evaluation map to choose an irreducible factor which
vanishes at the integer point. No such factor is assumed to exist.

`BivariateDivisionBounds.quotient_height_power_general` extends the
proved factor-height bound to partial-degree budget d*q and height
budget (B+1)^(c*q). Every integer quotient has height at most

    (B+1)^((c+3*d)*q), for 1<=q<=B.

`BivariateLargeRoot` proves height invariance under exchanging the
variables. The strong Cauchy integer-root bound shows that a nonzero
polynomial through an integer point with both absolute coordinates
larger than its height must have positive degree in both variables.

`InitialCurveFactor.exists_curve` assembles these facts: the actual
vanishing irreducible factor has both partial degrees <=d*q,
total degree <=2*d*q, the stated explicit height bound, positive
degree in both variables and primitivity. Primitivity is supplied both
as a polynomial over Z[X] and as exclusion of nonunit integer constant
factors. No common curve, factor height or positive degree is inserted
as an unproved consequence of the source threshold.

## Actual uniform resultants and a simultaneous common factor

`BivariateResultantNonzero` uses Gauss's lemma over the actual
coefficient fraction field to prove that an irreducible factor of
positive Y-degree has nonzero resultant with a polynomial it does not
divide. No integral Bezout-coprimality assumption is inserted.
`BivariateResultantPoint` evaluates the actual Sylvester Bezout identity:
the common integer point forces the resultant to vanish at x.

`PolynomialDeterminantHeight` proves finite product and determinant
heights by coefficient arithmetic and the actual permutation expansion.
`BivariateResultantHeight` bounds every actual Sylvester entry from the
bivariate coefficient bounds, giving

    height(Res_Y(f,g)) <= n! * (((n*d+1)*H)^n).

Here n is the actual Sylvester size, d bounds the X-degree and H the
coefficient height. The estimate includes zero entries and the empty
matrix. `ResultantPowerBudget` absorbs every factorial and degree factor
uniformly. For n<=48q, d<=24q and H<=(B+1)^(2472q), 1<=q<=B, the
resultant height is at most (B+1)^(124608*q^2).

`CommonCurveFamily.exists_curve` now constructs one actual irreducible
primitive factor for an arbitrary family of integer polynomials through
the same point, with partial degrees24q and heights(B+1)^(2400q).
One member is required nonzero; zero other members are permitted.
If both absolute coordinates exceed (B+1)^(1000000*q^2), the factor
divides every member, has both degrees positive, total degree<=48q
and height<=(B+1)^(2472q). There is no dependence on family cardinality.
A common factor or resultant height is not assumed as a target premise.

## Completed assembly from the actual source basis

`EvenWordRanks` derives all literal even-cardinality and symmetric-
difference identities. An even subset of the integer interval [-B,B]
has half-cardinality at most B. Two basis supports each of cardinality
at most2q0 therefore give the actual pair-rank budget min(2q0,B).
No independent rank or parity premise is introduced for their sum.

`TwoWitnessFromSupports.exists_norm` instantiates completed T9.5 for
these literal sets and produces the actual primitive pair norm, nonzero
and vanishing at the point, with partial degrees24q0, total48q0,
height exponent2400q0 and a field-norm certificate. Actual basis
independence is derived from the binary support encoding.

`CommonCurveTheorem.integer_parameters` constructs the norms for every
unequal pair of actual basis indices, applies `CommonCurveFamily` to
that actual family and then applies the actual word-map rank theorem.
The first unequal pair exists from t>=2. The output certificate contains
an actual irreducible primitive polynomial, positive degrees in both
variables and the rank<=1 conclusion for the image of the whole source
space in its actual function-field square classes. The point, total
degree48q0 and height exponent2472q0 are supplied for this same curve.

`CommonCurveTheorem.article_13_2` covers arbitrary real B and q0 with
1<=q0<=B. Even-cardinality identities convert cardinal bounds to bounds
with floor(q0); the integer offsets lie in the floor(B) box. Monotone
base and exponent comparisons restore the original real thresholds.
The explicit common source constant c=1000000 gives both

    N > (B+1)^(c*q0^2),
    height(C) <= (B+1)^(c*q0), totalDegree(C) <=48q0.

The closed range N<=x,y<=2N includes the paper's half-open range. The
constant is independent of t. No curve, shared factor, pair norm,
image-rank or external height bound is assumed to prove the result.
Theorem13.2 is now complete. The subsequent integer-grid-fibre theorem
13.3 remains open. Coverage is74/167; findings remain76. No new
independent mathematical correction, external estimate, Paper C source,
manuscript-byte change or Palomar registration is counted.

## Validation

Lean v4.36.0-rc2 full build passed (10353 jobs); actual axiom audit passed for all 5607 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 3322 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records are intact. Ubuntu available space: 16.11 GiB. Full article theorem13.2 is proved from the actual bounded independent even basis through actual T9.5 pair norms, simultaneous primitive irreducible curve extraction and the actual function-field square-class map. Real B,q0, source comparable points, total degree48q0, point zero and common threshold/height constant1000000 are included, uniformly in the basis size. No pair-norm, common-factor, resultant bound, image-rank or unproved external premise is inserted. Coverage is74/167 (main26/73, companion48/94); findings remain76. No new manuscript conclusion error, external estimate, Paper C source, manuscript-byte change or Palomar registration.
