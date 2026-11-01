# Actual two-chart resultant denominator identities in T1.4

The actual resultant divisibilities underlying the primitive denominator
budget are proved. Companion T1.4 remains **in progress**: its source
polynomials, their required nondegeneracy and height bounds, eliminant
construction and determinant/lattice stages remain to be connected.

This extends P1-MATH-0048 and the
[grid and primitive arithmetic checkpoint](BIVARIATE_GRID_ALIGNMENT.md).
The source is T1.4 Step 3, `p1:arith:reuss`, original statement hash
`fb662a1d5ab5e605f53d3e8c90093d96c77b1157614bf68fc134d4487283c89b`.

## Actual homogeneous Bezout identity

For integer polynomials f,g of degrees at most d>0, define

    F = homogenize(f,d),       G = homogenize(g,d),
    R = resultant(f,g,d,d),
    R' = resultant(reflect(d,f),reflect(d,g),d,d).

These are actual Mathlib polynomial and determinant definitions.
`homogenized_bezout` constructs homogeneous polynomial multipliers from
the proved Sylvester adjugate/Bezout identity. At general degrees m,n,

    homogenize(f,m)*P + homogenize(g,n)*Q = R*Y^(m+n).

Evaluating at a,b proves q divides R*b^(m+n) whenever q divides both
actual form evaluations. No quotient evaluation or nonzero coordinate
assumption is needed. Zero coordinates are included.

## Both coordinate charts and primitive cancellation

`eval_reflected_homogenize` proves exactly that padded coefficient
reflection exchanges the two homogeneous coordinates. It includes
polynomials whose degree is less than d. Applying the homogeneous
Bezout identity in the reflected chart gives q divides R'*a^(2d),
while the first chart gives q divides R*b^(2d).

If gcd(|a|,|b|)=1, the previously proved primitive gcd calculation
cancels the coordinate powers. `primitive_resultant_product` therefore
proves q divides the actual product R*R'. These two divisibility
identities are derived from the form evaluations, not supplied as
unproved arguments.

## Nonzero resultants and denominator families

`padded_resultant_ne_zero` proves nonvanishing from univariate
coprimality and the requirement that at least one polynomial attains
the padded degree. The other degree may be smaller. The integer
version transports coprimality over Q and preserves actual degrees and
resultants under the injective coefficient map. The full-degree
condition is explicit: coprimality alone does not justify adding empty
top-degree rows to both polynomials.

With the two actual resultants nonzero, `finite_denominator_count`
counts every finite set of signed denominators satisfying the form
divisibilities at some primitive integer coordinate pair. The pair
may vary with each denominator. The count is at most

    2*tau(|R*R'|).

`polynomial_height_denominator_count` proves a common N^epsilon
threshold whenever |R*R'|<=N^K for fixed K. It precedes all integer
polynomials, padded degrees, signed denominator sets and primitive
coordinate witnesses. No coordinate-height or target counting bound
is assumed.

## Remaining scope and provenance

Extraction of the chart polynomials from the source's auxiliary curve,
their nondegeneracy, their uniform coefficient/resultant height and the
eliminant construction are still separate tasks. This checkpoint does
not complete T1.4 or its coefficient-uniform determinant estimate.
Numbered coverage remains 54/167.

The proved Mathlib resultant, homogenization and coefficient-reflection
identities use pin `9d581dfff2e41de989072ea63abf3daf69311520` and are
recompiled under Lean v4.36.0-rc2. Only their selected dependency cache
was fetched. No new Paper C port or unproved literature input is added.

The full build passed (9,489 jobs); all 3,693 declarations passed the
actual axiom audit, permitting only propext, Classical.choice and
Quot.sound. All 1,408 distinct coverage/finding names were checked
directly by Lean. Original manuscript bytes are unchanged.

Validated actual chart-resultant checkpoint (9,489 build jobs;
3,693 audited declarations; 1,408 directly checked coverage/finding names):
[582ea278507fd72b88e47d7dbae9d30ff064f179](https://github.com/Vulkin-prog/paper-p1-lean/commit/582ea278507fd72b88e47d7dbae9d30ff064f179).
