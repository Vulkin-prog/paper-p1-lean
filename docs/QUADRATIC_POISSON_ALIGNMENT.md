# Article Lemma 8.1: the exact quadratic Poisson positivity domain

**Status: proved**, including the singleton formula and both directions of
the probability criterion. At this checkpoint coverage is 18 / 167:
9 / 73 main and 9 / 94 companion. Original locator: main V1.6, page 25,
`p1:close:positivity`, `main_sections/closure.tex:39`; statement hash
`1bda3d739142898ef6191306fe15dfe040c58696c9aeab658210a3674d15e5a0`.

## An actual signed measure

`PoissonSequence.mass μ k` is `exp(-μ) μ^k/k!`. For μ≥0, its sum is one
by Mathlib's proved exponential-series identity. `AtomicSignedLaw.ofSequence`
constructs an actual signed measure from a summable real sequence, using its
integrable density relative to counting measure. The integrability proof is
explicit; the density construction's totalized zero case is not used.

`PoissonSequence.shift` inserts a zero at index zero and moves every mass
one place to the right. Its sum is unchanged. The second difference is
`shift(shift(a))-2 shift(a)+a`, and its sum is zero. The coefficients of
`QuadraticPoisson.reference μ α` are exactly

`mass(μ,k) + (α/2) secondDifference(mass(μ))(k)`.

Their summability and sum one are proved for every real α and μ≥0.
`reference_total_mass` is an equality of actual signed-measure masses.

`poissonSigned_eq_poissonMeasure` identifies the base signed measure with
Mathlib's actual Poisson probability measure. `shiftMap` is the linear
pushforward by successor, which is the representation of convolution by
δ₁ on the natural numbers; `differenceMap` subtracts the identity, giving
convolution by δ₁-δ₀. `ofSequence_shift` proves this coefficient transport.
`reference_eq_poisson_plus_secondDifference` is the full signed-measure
identity `Πμ + (α/2) differenceMap(differenceMap(Πμ))`. Thus the reference
is the source's quadratic correction, with its prescribed zero masses at
negative indices.

## All singleton masses

`mass_succ_mul` proves the exact factorial recurrence, including the first
two indices. It gives

`secondDifference(mass(μ))(k) = mass(μ,k)/μ² * ((k-μ)²-k)`

for μ≠0. `reference_singleton` is the source's exact formula for every
natural k. No asymptotic approximation or truncation is used.

## Exact integer minimum and negative α

`CharlierQuadratic.theta` is μ minus its natural floor. For μ≥0,
`theta_eq_fract` proves equality with the ordinary integer fractional part.
It lies in [0,1). The integer minimum of `(k-μ)²-k` is

`-μ-theta(1-theta)`.

`quadratic_at_floor_succ` attains it at floor(μ)+1 and
`quadratic_ge_minimum` proves the lower bound at every natural k. This
choice remains a minimizer when μ is an integer. For α<0,
`nonnegative_scaled_iff` chooses an explicit sufficiently large natural k
where the coefficient is negative, rather than checking finitely many masses.

For nonnegative α, the attained minimum gives the exact upper endpoint.
The denominator is proved positive. `main_8_1_fract` states

`reference μ α is a probability iff 0≤α≤2 μ²/(μ+fract(μ)(1-fract(μ)))`.

Both endpoints are included. Probability status here means existence of an
actual bundled probability measure whose associated signed measure equals
the reference. `isProbability_ofSequence_iff` constructs that measure from
the nonnegative masses and proves the converse from its singleton masses.
It is not merely an assertion that a list of coefficients is nonnegative.

## Validation and scope

The complete Lean v4.36.0-rc2 build passed (8,699 jobs); the actual axiom
audit passed for all 1,519 project theorem/lemma declarations, with only
`propext`, `Classical.choice`, and `Quot.sound`. Original sources are
unchanged. No new correction or improvement is identified in Lemma 8.1;
the eight existing improvement entries concern other results.

This is the exact positivity theorem for arbitrary parameters. Positivity
of the particular references for all sufficiently large N still requires
the model's parameter asymptotics, which remain separate open results.
No law-approximation estimate or Palomar registration follows from this lemma.
