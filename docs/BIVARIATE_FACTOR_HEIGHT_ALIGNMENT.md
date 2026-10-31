# Companion T9.4: exact bivariate factor height

**Status: proved**, including the integer quotient. At this checkpoint,
coverage is 17 / 167: 8 / 73 main and 9 / 94 companion.
Original locator: companion V1.6, page 41, `p13:rig:factor-height`,
`companion_sections/pair_rigidity.tex:251`. The preserved statement hash is
`4454c486e367672e512f8bdb1d051c4d473a179b07f22204fc4047cf7517576c`.

## Literal degrees, height and norm

Integer bivariate polynomials are represented as `ℤ[X][X]`, with the inner
variable X and outer variable Y. `BivariateDegrees.degreeY` is the outer
natural degree; `degreeX` is the outer degree after Mathlib's variable swap.
`coeff_swap` proves the coefficient identification, and each coefficient
polynomial has degree at most `degreeX`. For a nonzero integer product,
both partial degrees of either factor are at most those of the product.

`BivariateHeight.height` is the maximum natural absolute value of all
integer coefficients. `bivariateL2Norm (complexBivariate P)` is exactly
the square root of the finite sum of squared absolute values of these
coefficients. Its finite-support definition includes every nonzero
coefficient without assuming that the support fills a rectangle.
The support bounds prove the precise estimate

`||P||₂ ≤ sqrt((dX+1)(dY+1)) H(P)`.

## Proof using univariate Mahler bounds and Parseval

The formal proof does not assume a multivariate Mahler estimate. For a
complex univariate polynomial, Mathlib proves its coefficient bound by a
binomial coefficient times its Mahler measure, multiplicativity of Mahler
measure, and Mahler measure at most its coefficient ℓ² norm.

For nested complex polynomials Q and R with outer degrees at most D and E,
specialize the inner variable to z. The univariate bounds give

`|Q_i(z) R_E(z)| ≤ 2^D ||(Q R)(z, Y)||₂`.

The coefficient at the fixed upper degree E is retained even where
specialization lowers the degree of R. If that coefficient vanishes, the
inequality remains valid. Squaring and taking the circle average, Parseval
proves the exact coefficient norm inequality

`||Q_i R_E||₂ ≤ 2^D ||Q R||₂`.

Take E to be the outer degree of the nonzero integer quotient R. Its
coefficient R_E is a nonzero integer polynomial. Its nonzero integral
leading coefficient and the proved univariate leading-coefficient Mahler
bound give `M(R_E) ≥ 1`. Consequently

`M(Q_i) ≤ M(Q_i R_E) ≤ ||Q_i R_E||₂`.

Applying the inner coefficient estimate gives the bound
`|Q_ij| ≤ 2^(degX Q + degY Q) ||Q R||₂`.
The exact partial-degree inequalities then give the original factor
constant `2^(dX+dY)`.

## Full statement and improvement

`BivariateFactorHeight.companion_T9_4_factor_and_quotient` takes the literal
polynomials P, Q, R, assumes only `P ≠ 0` and `P = Q * R`, and proves both
height bounds by `2^(dX+dY) ||P||₂`, followed by the exact rectangle-height
bound. No primitivity, monicity or content-one premise is needed. This
removal of the primitive hypothesis is recorded as `P1-MATH-0008`.
No error in the original conclusion or proof is claimed.

All analytic inputs are proved Mathlib results at the pinned commit
`9d581dfff2e41de989072ea63abf3daf69311520`. No literature proposition or
final height estimate is passed as a hypothesis. The proof does not reuse
Paper C's univariate `PolynomialHeightOperations` module.

## Validation

The complete Lean v4.36.0-rc2 build passed (8,651 jobs), followed by the
actual kernel-axiom audit of all 1,484 project theorem/lemma declarations.
Only `propext`, `Classical.choice` and `Quot.sound` occur. The original
source identity and all 167 statement locators remain checked separately.
These checks do not qualify the unfinished paper for Palomar registration.
