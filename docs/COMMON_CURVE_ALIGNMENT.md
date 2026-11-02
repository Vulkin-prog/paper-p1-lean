# Common-curve theorem: point factors and functional square-class collapse

Source: article theorem13.2, `p13:rig:common-curve`,
`main_sections/pair_rigidity.tex:127`, with its companion proof in
`companion_sections/pair_rigidity.tex:434`. Status: **in progress**.
Coverage remains73/167 (main25/73, companion48/94).

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

## Remaining obligations

The resultant of this first factor and any other pair norm must be
shown nonzero whenever divisibility fails, with a coefficient height
bound uniform in the degree. Its common-point root would then violate
the integer-root bound under an explicit quadratic-support threshold.
This will force the same factor to divide every pair norm.
The construction must still be assembled for an actual independent
even bounded basis using completed T9.5, with the original source
quantifiers and a threshold independent of the basis size.
Until these steps are checked, theorem13.2 remains in progress.
No new mathematical correction, external estimate, Paper C source,
manuscript-byte change or Palomar registration is counted here.

## Validation

Lean v4.36.0-rc2 full build passed (10333 jobs); actual axiom audit passed for all 5572 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 3287 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records are intact. Ubuntu available space: 16.13 GiB. Actual curve field and square classes, entire formal-word image-rank collapse from shared primitive norms, and actual irreducible point-factor extraction with explicit height and positive-degree budgets are proved. Uniform resultant nonvanishing/height and final source assembly remain open; article13.2 is in progress. Coverage remains73/167 and confirmed findings76. No new external estimate, Paper C source, manuscript-byte change or Palomar registration.
