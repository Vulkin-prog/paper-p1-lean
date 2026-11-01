# Main 14.2 — Sharp rational overlap and its unique extremal triple

Source: Lemma 14.2, page 35, `p13:third:rational-rank`,
`main_sections/third_cumulant.tex:79`. Statement SHA-256:
`1444566fc49d3124a28816f757f4d3b2f6dd5360c6017e8b9b97f606942c573c`.
The source bytes are preserved. The full numbered statement is **proved**.

`RationalTripleIntegers.article_14_2` proves the literal source assertion
for every integer triple u<v<w<2u with gcd(u,v,w)=1:

    D(u,v,w) = gcd(u,v)/v + (gcd(u,w)+gcd(v,w)-1)/w <= 19/30.

The strict integer range itself implies positivity. Actual gcds,
denominators and inequalities are transported to positive natural slopes,
without adding a positivity hypothesis to the original statement.

## Stronger conclusions

`RationalTripleIntegers.equality_iff` proves equality if and only if
(u,v,w)=(10,12,15). `bound_away_from_extremal` proves D<=11/18 for every
other primitive ordered triple in the source range. The actual primitive
triple (8,9,12) attains 11/18; `sharp_witnesses` checks both tuples'
complete admissibility and exact rational densities. The next-value bound
is sharp and the gap is 1/45. This is P1-MATH-0067.

## Checked proof chain

1. `RationalTripleDensity` defines the symmetric density from three
   actual pair gcds, their larger slopes and the largest slope. It proves
   permutation identities and equality with the exact ordered source
   formula. The third-window bound includes all possible orderings of
   the three positive denominators.
2. If every reduced pair height is at least five, the three pair
   contributions sum to at most 3/5. Otherwise, division by the actual
   pair gcd and coprimality prove that a pair has ratio 2:3 or 3:4.
   All three possible pair positions in the original triple are treated.
3. `RationalTripleSmallRatios` retains the third-slope coprimality. For
   the 2:3 pair the numerator gcd(c,2)+gcd(c,3)-1 is at most c/4 when
   c>=16. Every smaller numerator and every denominator allowed by the
   strict ratio range is checked. Only d=5,c=12 can exceed 11/18,
   giving the primitive set {10,12,15}.
4. For the 3:4 pair, gcd(c,3)+gcd(c,4)-1 is at most c/3 when c>=18.
   The complete smaller cases, strict range, coprimality and distinctness
   give at most 11/18. The finite checks are ordinary kernel proofs,
   without native_decide, assumptions or admissions.
5. `RationalTripleOverlap.gap` combines the cases and identifies the
   only ordered exceptional tuple. `RationalTripleIntegers` proves the
   literal integer statement, equality classification, sharp gap and
   both admissible witnesses.

## Exact scope

This is canonical coincidence geometry on primitive integer slopes.
Additional square-class relations among distinct normalized values are
not bounded by this result. No triple-rank estimate, probability estimate
or third-cumulant exponent follows without its separate arithmetic input.
Nonprimitive triples are not silently inserted into the source formula.

No Paper C port, new literature proposition or manuscript edit is used.
Coverage is 67/167: main 23/73, companion 44/94. Confirmed mathematical
improvements are 67. Palomar remains a later whole-project milestone.
