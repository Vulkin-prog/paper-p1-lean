# The unnumbered asymptotic continuation after T23.1

**Status: proved.** This adds no numbered result to the 167-result baseline.
The original continuation is companion V1.6, page 93,
`companion_sections/moment_obstruction.tex:62` through the end of that file.
Its exact UTF-8 source hash is
`02b88df15e505afb4a57e4fec5c2dd1b017b4cb5077d22735dc876254352b5b6`.
The numbered proposition is covered in [its separate alignment](MOMENT_OBSTRUCTION_ALIGNMENT.md).

## The literal probability family

`MomentObstructionSequence.order N` is floor(sqrt(log N)), and
`parameter N` is `(log N) N^(-2/3)`. The order tends to infinity and the
parameter is nonnegative and tends to zero. `valid_eventually` proves a
single eventual domain with order at least three and parameter in [0,1].
These are proved properties, rather than hypotheses added to the example.

`familyLaw` and `referenceFamily` are actual bundled probability measures
at every natural index. On the eventual valid domain they are exactly
the P and Q constructed in T23.1 with these literal parameters. At invalid
initial indices both use Poisson(1); validity eventually holds, so this
completion affects only finitely many terms. `familyDistance_eq` identifies
their actual total variation with the previously proved exact formula.

## Every fixed factorial order

`PoissonFactorialMoments.hasSum_mass_factorial` proves the closed Poisson
factorial sum μ^r by its exact factorial ratio and a shifted exponential
series. Pascal's binomial identity proves the factorial finite differences.
They give the exact Q moment `1+a choose(r,2)` at mean one, with actual
Bochner integrability already established.

`fixed_factorial_moments_eventually r` then proves

`E_(familyLaw N) (X)_r = 1+choose(r,2) parameter(N)`

for all sufficiently large N, with r fixed before that threshold. No
uniformity in a growing r is asserted. `exponential_bound_eventually`
retains the original explicit bound, with its constant independent of N.

## The full logarithmic distance asymptotic

The proved finite Stirling lower inequality and m!≤m^m give

`m log m-m ≤ log(m!) ≤ m log m` for m≥1.

The exact distance formula and 0≤a≤1 imply
`|log(distance(m,a))+m log m|≤2m` for m≥3. The floor is treated by a
finite inequality, not discarded asymptotically:

`|floor(x) log(floor(x))-x log x|≤x` for x≥3.

It follows that whenever log N≥9, uniformly over every a in [0,1],

`|log(distance(floor(sqrt(log N)),a))
  +(1/2)sqrt(log N) log(log N)|≤3 sqrt(log N)`.

`log_distance_error_isBigO` instantiates this for the actual probability
family. This is precisely the source's entire displayed logarithmic
asymptotic, including the floor and the O(sqrt(log N)) error.

## Larger than every polynomial rate

The proved analytic fact log z=o(sqrt z) supplies the final budget.
`uniform_distance_exceeds_power` proves the stronger uniform statement:
for every fixed γ>0, one N0 works simultaneously for all parameters a in
[0,1], and every N≥N0 satisfies

`N^(-γ)<distance(floor(sqrt(log N)),a)`.

Strict positivity is proved before taking logarithms or exponentiating.
`distance_exceeds_every_power` specializes to the actual family. Thus
fixed-order factorial agreement and the uniform exponential control coexist
with failure of every polynomial approximation rate in this example. There
is no claim of a multiplicative-model realization or of an optimal general
moment-to-distance theorem.

## Inputs and validation

Every input is proved internally or in Mathlib at pinned commit
`9d581dfff2e41de989072ea63abf3daf69311520`. The only Stirling input is
`Stirling.le_log_factorial_stirling`; it is a closed library theorem.
The subsequent log/square-root comparison uses
`isLittleO_log_rpow_atTop` with its exponent 1/2. No asymptotic formula,
rate obstruction or factorial-moment equality is passed as a premise.

The full Lean v4.36.0-rc2 build passed (8,739 jobs), followed by the actual
axiom audit of all 1,680 project theorem/lemma declarations. Only `propext`,
`Classical.choice` and `Quot.sound` occur. The numbered count remains
20 / 167. No new mathematical finding is introduced, and no Palomar
registration is made.
