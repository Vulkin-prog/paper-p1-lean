# Offset-pattern Rankin bounds — companion T21.3

**Status: proved in full.** Source: companion V1.6, page 88,
`companion_sections/arithmetic_consequences.tex:208`,
label `p1:consequences:rankin-patterns`. Statement SHA-256:
`a7a69c333387e3b9aa59a977e6082a4fe46373b4c46d2b3d89d5d47dac8b8cea`.

## Literal finite populations and weights

`OffsetFactorSupports.roughValues Y X` consists of actual positive squarefree
integers Q<=X whose prime factors all exceed Y. `mem_roughValues` proves
that description for real cutoffs. `primeFactors_injective_on_rough` uses
the proved reconstruction Q=prod(primeFactors Q), so no support multiplicity
is lost when the prime sum is covered by a finite Euler product.
The empty prime support corresponds to Q=1, with the usual vacuous lower
prime-factor condition.

`integerSupports Y X` is a finite family, but `mem_integerSupports` proves
it contains exactly every finite set A of distinct natural integers satisfying
all g>Y and prod(A)<=X, when Y>=1. Every such factor is at most the product,
so it belongs to the finite pool up to floor(X). Thus no infinite source
support is omitted. The empty set and its product one are retained.

`roughWeightedCount_eq_source` and `integerWeightedCount_eq_source` prove
that the weights at a=(D0*B)^d are exactly
`(D0*B)^(d*omega(Q))` and `(D0*B)^(d*card(A))`, respectively, with
omega(Q)=card(primeFactors Q).

## Proved finite Rankin and tail bounds

`FiniteEulerRankin.rankin_term` proves the actual termwise comparison from
prod(S)<=X and positivity. Summing over the finite powerset gives the Euler
product and its exponential envelope. No product-counting bound is a premise.

For integer factors, `ClippedPowerSum.finite_tail_le_power` bounds every
finite subset of integers above Y by the actual convergent p-series tail,
then by its proved integral power bound.

For primes, clip the decreasing weight at Y^(-s). Finite Abel comparison
applies the proved prefix bound sum_{p<=Z} log(p)<=Z*log(4).
`clipped_sum_le` bounds its integer comparison by
`(1+C_s)*Y^(1-s)`, with C_s the proved p-series-tail constant.
Since log(p)>=log(Y) above the cutoff,
`PrimePowerTail.finite_prime_tail_le` proves

`sum_{p in P} p^(-s) <= D_s*Y^(1-s)/log(Y)`

for every finite prime set P above Y>1 and s>1, with
`D_s=log(4)*(1+C_s)`. No asymptotic prime-tail estimate is assumed.

## Source exponents, constants and uniformity

Set s=1+(d-1)/c. Substituting Y=B^c and a=(D0*B)^d gives
`a*Y^(1-s)=D0^d*B` and `log(Y)=c*log(B)`.
The explicit prime constant is `D0^d*D_s/c`.
For d=2 or d=3, `prime_patterns_uniform` chooses the maximum of these two
constants before d,B,X, retaining the exact dependence O_{c,D0}(B/log B).

For integer factors set s_zeta=1+(d-1+zeta)/c. The exact identity is now
`a*Y^(1-s_zeta)=D0^d*B^(1-zeta)`.
The explicit constant is `D0^d*C_{s_zeta}`.
`coefficient_power`, `prime_cost_identity` and `integer_cost_identity`
prove these real-power cancellations and logarithmic divisions.

`companion_T21_3` combines both source conclusions, for B>=2 and X>=1,
with c,D0 fixed positive, original d in {2,3}, and 0<zeta<1 in the integer
case. All real cutoffs, weights and quantifier order are retained.

The stronger explicit theorems hold for every fixed integer d>=2, with
constants depending on d, and every zeta>=0 in the integer case.
`P1-MATH-0017` records those ranges. There is no claimed constant uniform
over unbounded d, correction to an original conclusion or optimality claim.

## Provenance and validation

No additional Paper C source is ported. The existing attributed P1
Rankin-comparison infrastructure is reused. Mathlib at
`9d581dfff2e41de989072ea63abf3daf69311520` supplies squarefree prime-factor
reconstruction, finite Abel comparison and real powers. Every finite cover,
weight identity, tail estimate and constant specialization is proved here.

The full Lean v4.36.0-rc2 build passed (8,827 jobs). The actual axiom audit
passed for all 1,978 project theorem/lemma declarations, with only
`propext`, `Classical.choice` and `Quot.sound`. Coverage is 29 / 167:
11 main results and 18 companion results. No Palomar registration is made.

All 283 distinct coverage/finding declaration names were checked directly by Lean.

Validated implementation of companion T21.3 and P1-MATH-0017:
[6848867fb06d1790bc0ff5a0a298671889c1b638](https://github.com/Vulkin-prog/paper-p1-lean/commit/6848867fb06d1790bc0ff5a0a298671889c1b638).
