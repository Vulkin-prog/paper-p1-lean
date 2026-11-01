# Whole prime products on an offset line — companion T20.1

**Status: proved, all finite and uniform asymptotic conclusions.** Source:
companion V1.6, page 82, `companion_sections/offset_geometry.tex:25`,
label `p1:offset:line-product`. Exact statement SHA-256:
`3d4614d57da7feeb6e0285ad305978a6ebb6e00ab2cb871ee9fd0ae624c6af41`.

## Actual primes, offsets and lines

`OffsetLinePopulation.pool` is the finite set of actual shared primes
above H with an odd-valuation occurrence in every window and an offset
vector on the line. `mem_pool_iff_actual` proves the exact arithmetic
membership: the finite prime cutoff at 3*N is a consequence of actual
positive value bounds. It is not an added arithmetic restriction.

For H>=B, `odd_offsets_unique` proves that every such prime has one
physical occurrence per window. `chosen_points_iff_actual` identifies the
finite chosen point image with every actual distinct offset supplied by
these primes. A generic divisibility-only prime configuration is counted
first and then instantiated with this exact source population.

Integer collinearity is expressed by zero two-coordinate minors.
`collinearSet_of_real_line` proves it for the integer points of every real
parametrized affine line. No assumed primitive parametrization is hidden
in the line predicate.

## Primitive direction and the whole product

Integer gcd and Bezout identities construct d from two distinct occurring
offsets. `primitive_iff_content_one` identifies its primitivity with gcd
of its three coordinates equal to one. Its height is exactly the maximum
of the three absolute integer coordinates and is at most B.

`PrimitiveProductBound` includes the parametrization of **every integer
point on the line** as the chosen point plus an integer multiple of d,
not just the prime-supplied points. The generic integral-line lemmas prove
this directly from primitivity and collinearity.

Every shared prime divides the same integer minor of d and a value
vector. If all minors vanished, positivity and two distinct offsets
would force two distinct proportional pairs of values. Actual parity
vectors, first-window regularity and directness with the second space
exclude this. Thus some minor is nonzero and its absolute value is at
most 6*N*height(d). Pairwise coprime primes make their entire product
divide that integer. For a single occurring point, their product divides
one actual value and is at most 3*N. The empty population is included.

## Offset count and uniform asymptotics

Both cases give the uniform product bound 6*N*B. For primes above Y>1,
logarithms therefore give the stronger exact count

`card(distinct offsets) <= log(6*N*B)/logY`.

The source majorant `M_Y=1+log(6*N*B)/logY` is also retained explicitly.
It is eventually bounded by

`(1+6*log(2))*B/logB`

uniformly over the critical band and all Y>=B. For every epsilon>0 one
threshold makes M_Y<=epsilon*B for every allowed length and Y. The
constant is absolute and is chosen before the band constant, cutoff
multiple, centers, line and Y. Thresholds are chosen before these varying
arithmetic data.

`OffsetLineTheorem.companion_T20_1` states the original three-regular-
window, pairwise-direct specialization with fixed C0>1. Its stronger
`uniform_stronger` needs only first-window regularity and directness
with the second space, and permits H=B. P1-MATH-0024 and P1-MATH-0025
record these delimited improvements. Later plane statements are not
asserted to inherit the relaxed hypotheses.

## Inputs and validation

Every gcd, line parametrization, prime-product, nonvanishing, arithmetic
population and counting input is proved internally. Mathlib at
`9d581dfff2e41de989072ea63abf3daf69311520` supplies integer Bezout,
finite products, divisibility and real logarithms. No external determinant
or prime-density estimate is used. No additional Paper C source is ported.

The full Lean v4.36.0-rc2 build passed (8,935 jobs), followed by the actual
axiom audit of all 2,305 project theorem/lemma declarations. Only `propext`,
`Classical.choice` and `Quot.sound` occur. Numbered coverage is 36 / 167:
main 15 / 73, companion 21 / 94. No Palomar registration is made.

All 438 distinct coverage/finding declaration names were checked directly by Lean.
