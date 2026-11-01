# Poisson difference norms — article Proposition 19.2

**Status: proved, all three numbered conclusions.** Source: article V1.6,
page 58, `main_sections/discussion.tex:116`,
label `p1:discussion:charlier-norm`. Exact statement SHA-256:
`feae7bf2ac1698222782be84cbdad942cf3bd5eb201709656c01c7a701527e14`.

## Actual signed differences and finite convolution action

`FiniteShiftAction.action` applies a finitely supported signed kernel to
an infinite sequence by its finite sum of exact translations. The action
of Delta^r is `difference r`; its successor is translation minus identity,
proved from finite convolution multiplication. No binomial coefficient
pattern is assumed.

`PoissonDifferenceSigned.signedDifference` repeatedly applies translation
minus identity to the actual signed Poisson measure. It equals the actual
atomic signed measure of the constructed difference sequence. Every
singleton and its ordinary l1 norm are identified. Thus the source norm
is a signed-measure norm by its singleton masses, not a formal symbol.

## All orders, including zero

The exact factorial-moment identity is

`sum_k difference_r(Poisson(mu))(k) * (k)_j = (j)_r * mu^(j-r)`.

Here the natural falling factorial makes the expression zero for j<r.
This is a HasSum theorem, with its real summability consequences. The
finite coefficients of Delta^r express the normalized Charlier function
as a finite combination of (k)_j/mu^j. In its square expectation, every
lower-order term vanishes by the factorial identity and the top term is
r!/mu^r. This proves the required diagonal Charlier identity internally;
full off-diagonal orthogonality is not asserted by this development.

Summing a nonnegative quadratic inequality gives the square-root norm
bound. Translation is an l1 isometry, and subtraction gives the independent
coarse bound 2^r. Together these prove the exact source minimum for every
natural r, including r=0. No analytic generating-function coefficient
comparison or unproved orthogonality estimate is used.

## Exact four-mass formula and endpoints

`CharlierRoots` uses the exact source roots
`mu+1/2 +/- sqrt(4*mu+1)/2`. Both are positive for mu>0 and their gap
exceeds one. The natural indices floor(lowerRoot)+1 and ceil(upperRoot)-1
are therefore the source integer indices. Their interval is nonempty
and exactly characterizes strict negativity of the second difference.
Integer roots contribute zero and are excluded by these endpoints.

`FiniteNegativeMass` proves that a zero-total-mass sequence with a finite
negative support has norm minus twice the sum on that support. Its exact
finite second-difference telescoping identity gives the four Poisson
masses. `extended` is zero at negative integer arguments, as in the source.
The values norm(Poisson(2)*Delta^2)=10/(3*e^2) and C(2)=5/(6*e^2) are proved
symbolically, both using exp(2) and using (exp(1))^2.
`PoissonSecondDifferenceNorm.main_19_2` combines all numbered conclusions.

## Related unnumbered improvement

The source equation `p1:close:constant-bounds` at `closure.tex:99` gives
C(lambda)>=exp(-lambda)/4. Since the signed second difference has total
mass zero, its full norm is at least twice its positive mass at zero.
`coefficient_lower_bound` proves the stronger C(lambda)>=exp(-lambda)/2,
also including lambda=0 for the signed definition. P1-MATH-0023 records
this factor-two improvement. It adds no numbered coverage item.

## Inputs and validation

Mathlib at `9d581dfff2e41de989072ea63abf3daf69311520` supplies Poisson
masses, real sums, finite sets, signed measures, square roots and integer
rounding. No additional Paper C source is ported. Every probability,
coefficient, sign, moment and norm input displayed above is proved.

The full Lean v4.36.0-rc2 build passed (8,919 jobs), followed by the actual
axiom audit of all 2,257 project theorem/lemma declarations. Only `propext`,
`Classical.choice` and `Quot.sound` occur. Completed coverage is 35 / 167:
main 15 / 73, companion 20 / 94. No Palomar registration is made.

All 415 distinct coverage/finding declaration names were checked directly by Lean.

Validated implementation of article Proposition 19.2 and P1-MATH-0023:
[c3ae67f0b8622f142f16dce9eb4bb22fd541a2c5](https://github.com/Vulkin-prog/paper-p1-lean/commit/c3ae67f0b8622f142f16dce9eb4bb22fd541a2c5).
