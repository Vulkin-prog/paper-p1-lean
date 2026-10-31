# Logarithmic prime budgets — companion T22.3

**Status: proved in full.** Source: companion V1.6, page 90,
`companion_sections/uniform_appendix.tex:116`, label `p1:uniform:prime-budget`.
Exact statement SHA-256:
`4f96d8d3c0c83c42415d59c5ef2dff3eed16602b8bebff06bf3ca461a75ca108`.

## Actual integer population and the finite Rankin inequality

`SmoothSquarefreeCount.values P X` counts actual positive integers n<=X
whose odd-prime support is contained in P. `mem_values` proves that literal
condition, with real X and its floor handled explicitly. The squarefree
part is the parity squarefree part, rather than the radical of n.

The canonical decomposition n=prod(S)*a^2 gives a finite cover over S
contained in P, with a positive. Each fibre contributes at most
floor(sqrt(floor(X)/prod(S))) values. The proved Rankin comparison bounds it
by floor(X)^sigma times prod(S)^(-sigma), for every sigma>=1/2, including
empty fibres when prod(S)>floor(X). Finite powerset expansion therefore gives

`card(values P X) <= X^sigma * prod_{p in P}(1+p^(-sigma))`.

For 1/2<sigma<1, the source zeta(2*sigma) factor is retained in
`card_values_le_source_rankin`. It is the literal convergent series
sum_{a>=1} a^(-2*sigma), represented by `PowerSeriesTail.total (2*sigma)`.
Its lower bound one follows from its a=1 term. No special-function value or
upper bound is assumed. The stronger finite-fibre inequality is recorded
as part of `P1-MATH-0016`.

## Elementary uniform prime sum

The existing primorial bound proves, for every natural Z,

`sum_{p<=Z, prime} log p <= Z*log(4)`.

`WeightedPrimeSum.logPrimeSum_le_partialPower` applies Mathlib's finite Abel
comparison to this proved prefix bound and nonnegative antitone power
weights. It gives

`sum_{p<=Y} log(p)*p^(-sigma) <= log(4)*Y^(1-sigma)/(1-sigma)`.

For 0<=sigma<=3/4 the right side is at most
`4*log(4)*Y^(1-sigma)`. The elementary inequality
`log(Y/p) <= 8*(Y/p)^(1/8)` bounds the remaining logarithmic loss.
The finite integer sum at exponent sigma+1/8 is at most
`8*Y^(1-(sigma+1/8))`. Consequently one common constant gives

`log(Y)*sum_{p<=Y} p^(-sigma)
 <= (64+4*log(4))*Y^(1-sigma)`.

All steps use the actual finite prime sets and hold uniformly across the
whole exponent interval; no prime asymptotic or unproved partial-summation
estimate is an argument of these theorems.

## Arbitrary prime sets and source quantifier order

Split the given finite prime set P at Y. Its lower part is contained in the
proved initial-prime sum. For p>Y, monotonicity gives

`p^(-sigma)*log(Y) <= Y^(-sigma)*log(p)`.

The actual budget sum_{p in P} log(p)<=Y thus charges the whole upper part
at most Y^(1-sigma). With C=65+4*log(4), independent of P,Y and sigma,

`sum_{p in P} p^(-sigma) <= C*Y^(1-sigma)/log(Y)`.

The finite Euler product is at most the exponential of that sum.
For X>=1, the integer 1 belongs to the population, so its count is positive
and taking logarithms is justified. `PrimeBudgetRankin.log_values_le` proves

`log(card(values P X)) <= sigma*log(X) + C*Y^(1-sigma)/log(Y)`

for 1/2<=sigma<=3/4 and Y>1. The original range [3/5,3/4], Y>=3 and
O(1+Y^(1-sigma)/log(Y)) follows immediately. The same constant is chosen
before every finite prime set, X,Y and exponent in
`source_uniform_log_bound`. `companion_T22_3` combines both original source
conclusions. No target estimate is assumed in either conclusion.

## Provenance and validation

The finite square-root comparison already attributed to Paper C is reused
through the existing P1 module; no additional Paper C source is ported here.
Mathlib at `9d581dfff2e41de989072ea63abf3daf69311520` supplies finite Abel
comparison (`sum_mul_le_sum_mul_of_sum_range_le`), powers, logarithms and
p-series summability. The actual cover, weighted prime estimates and budget
split are proved in this project.

The full Lean v4.36.0-rc2 build passed (8,817 jobs). The actual axiom audit
passed for every one of the 1,941 project theorem/lemma declarations, with
only `propext`, `Classical.choice` and `Quot.sound`. Coverage is 28 / 167:
11 main results and 17 companion results. No Palomar registration is made.

All 263 distinct coverage/finding declaration names were checked directly by Lean.
