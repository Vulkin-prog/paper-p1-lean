# Forced offset planes — companion T20.3

**Status: proved, including the uniform original affine mass estimate.**
Source: companion V1.6, page 82,
`companion_sections/offset_geometry.tex:96`, label
`p1:offset:forced-plane`. Original statement SHA-256:
`57df7e0bd6cb7653361590ee129d82e799e54eeb64de7c26e3923dd9078bc775`.

## Actual shared primes and physical offsets

`SharedPrimeOffsets.Shared` means exactly a prime above H with an odd
valuation in a value of each of the three windows. The equivalence
`shared_iff_occurs_in_each_window` identifies the vector witness with
the three separate arithmetic occurrences. `shared_unique_offset`
proves uniqueness for H>=B. The source choice H=C0*B, C0>1, is included.
Odd valuation implies divisibility of the actual natural value.

`companion_T20_3_shared` instantiates the complete proposition with this
population and its canonical offsets. The generic arithmetic theorem
works for any specified offsets and distinct common prime divisors,
which is a larger population. It does not assume a geometric or
probabilistic estimate.

## Two primes, the determinant and all three normal coordinates

The two-prime bound is the proved whole-product line estimate applied
to two offset vectors. Every prime in a triple divides its actual
integer determinant. Distinctness makes the product divide its absolute
value, which is at most 18*N*B^2. A larger product forces the determinant
to vanish. The whole-product line bound then excludes a zero normal,
including repeated offsets.

The plane normal is the cross product of the two offset differences;
its coordinates have absolute value at most 2*B^2. Its constant is the
negative dot product with the first offset and has absolute value at
most 6*B^3. The determinant identity gives actual center containment.
Positivity and regular/direct pair projection rigidity prove that every
normal coordinate is nonzero. No nonvanishing or rank conclusion is
assumed in this step.

Every further common divisor q divides the dot product of this normal
with the actual value vector. That integer has absolute value at most
12*B^3, so q>12*B^3 forces the source offset equation. This argument
also works for composite q. The initial three divisors still must be
distinct primes for the whole-product argument used here.

## Geometrically distinct planes and integer points

`OffsetPlaneIntersections.family` is the finite image of the nonzero
offset-normal codes as actual subsets of real three-dimensional space.
It has at most B^9 elements. Equality of coefficient codes is not used
as a substitute for equality of geometric planes.

For two distinct planes with an integer point in common, proportional
normals would make the planes equal. Hence a cross-product coordinate
is nonzero. Fixing that coordinate of a common point determines the
other two by a nonsingular two-equation integer system. Projection is
therefore injective into [N,2N), proving at most N common centers.
The empty intersection is included. A union bound over at most B^18
ordered code pairs gives at most B^18*N centers on two distinct planes.

## Original affine probabilities and uniform mass

`TripleProbabilityBound.tupleSet` is the actual set of the three starts.
`Primitive` means positive effective relative nullity and zero nullity
on every proper subfamily, precisely minimal dependence of the original
block spaces. `OffsetPlaneMass.primitiveCenters` retains ordered
distinct regular starts, pairwise direct spaces, this primitive condition
and membership in two distinct planes. `primitiveMass` sums the original
infinite-model joint Bochner probabilities over these ordered triples.
It is not a nominal or centered substitute.

The proof first bounds the larger `pairCenters` population. Only the
first two starts must be distinct, regular and direct; the third may
be irregular, dependent or repeated. Zero pair nullity and the exact
compatible affine probability formula give the pair bound p^2.
Antitonicity of actual joint activation gives the same bound for the
triple, including incompatible systems. The resulting finite mass is
at most B^18*N*p^2.

The critical band gives p<=2^C/N. A fixed logarithmic polynomial is
uniformly subpolynomial, so for every C and epsilon>0 one threshold
precedes **every** critical length, center, prime and offset and gives

`pairMass N L <= N^(-1+epsilon)`.

The source primitive mass is a nonnegative subsum. This proves the
stated O_C(N^(-1+o(1))) with explicit quantifier order. It proves no
later normal-budget, covering or residual-space estimate.

## Improvement and validation

P1-MATH-0026 records the weaker hypotheses: two regular windows suffice
for the complete geometric conclusion, with all pairwise directness
conditions retained. The mass estimate requires only the first regular
direct pair and includes a larger population than primitive triples.
Canonical odd offsets require H>=B; the subsequent-divisor equation
does not need primality. No original error or optimality claim is made.

All geometry, divisibility, arithmetic populations, actual probability
bounds and uniform asymptotics are proved internally. No new Paper C
source is ported. Mathlib at the pinned revision supplies finite sums,
linear algebra, integer divisibility and real powers and logarithms.

The full Lean v4.36.0-rc2 build passed (8,965 jobs), followed by the
actual axiom audit of all 2,402 project theorem/lemma declarations.
Only `propext`, `Classical.choice` and `Quot.sound` occur. Numbered
coverage is 37 / 167: main 15 / 73, companion 22 / 94. The original
manuscripts are unchanged. No Palomar registration is made.

All 480 distinct coverage/finding declaration names were checked directly by Lean.

Validated implementation of companion T20.3 and P1-MATH-0026:
[1bbce661a7f9c0bdaaccc69e5ab171848a9e5db1](https://github.com/Vulkin-prog/paper-p1-lean/commit/1bbce661a7f9c0bdaaccc69e5ab171848a9e5db1).
