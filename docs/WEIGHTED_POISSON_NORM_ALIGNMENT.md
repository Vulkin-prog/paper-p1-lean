# The weighted recurrence criterion — companion T19.13

**Status: proved.** Source: companion V1.6, page 77,
`companion_sections/limits_appendix.tex:1013`, label
`p1:limits:weighted-residual`. The exact statement hash is
`60b1d2ef56e93da3701c1b41a40c08898e2bb5fe5bb83536aa27b0d26a9a8add`.

## Actual arbitrary probability measures

The carrier of P and Q is `ProbabilityMeasure ℕ`. Their real singleton
masses are nonnegative and have sum one, proved by `hasSum_realMass`.
There is no finite support, finite first moment or exponential moment
hypothesis. Total variation is half the ordinary sum of absolute singleton
differences, as in the manuscript.

`WeightedPoissonNorm.weightedNorm` is the sum of
`|P_(k+1)-μ P_k/(k+1)|` over natural k. `weightedNorm_eq_raw_sum` identifies
this with the literal source summand after the bijection k↦k+1 onto the
positive integers. `weightedNorm_summable` proves absolute convergence.
`poisson_eq_mathlib` identifies the bundled reference with Mathlib's actual
Poisson measure; its residual vanishes by the exact successive-mass identity.

## The closed factorial resolvent

`WeightedRecurrence.factorial_solution` proves the finite recurrence
solution by induction. After dividing by k!, `solution` gives its full
closed form. `FactorialResolvent.factorial_ratio_bound` proves

`j!/(j+n)! ≤ 1/n!`.

The product of the absolutely summable residual and the exponential series
dominates the whole double series. `hasSum_antidiagonal` regroups it using
the actual antidiagonal equivalence, with absolute convergence proved before
regrouping. `correction_l1_bound` gives the bound exp(μ) times the residual
norm. Mass zero then gives `|a_0|≤||b||₁` and finally

`||a||₁≤2 exp(μ)||b||₁`.

These are proved bounds, not recurrence or Stein estimates assumed as
premises. Applying them to the actual mass difference P−Π_μ proves the
lower estimate. The forward operator bound proves the upper estimate.

## All original conclusions and the parameter extension

`companion_T19_13` proves both source bounds for μ>0:

`exp(-μ) TV(P,Π_μ) ≤ V(P;μ) ≤ 2(1+μ) TV(P,Π_μ)`.

`weightedNorm_stability_bounded` proves the source stability estimate with
only `0≤μ≤M`; the second parameter ν can be any real number. In particular
it includes the source domain `0<μ,ν≤M`. The more general theorem is

`|V(P;μ)-V(Q;ν)| ≤ 2(1+|μ|) TV(P,Q)+|μ-ν|`

for all real μ and ν. Its proof bounds the parameter-change term by
`sum_k Q_k/(k+1)≤1`. `poisson_comparison_nonnegative` also includes μ=0,
where the Poisson reference is the point mass at zero. These weaker
parameter hypotheses form `P1-MATH-0010`; they do not change any original
constant or conclusion.

## Inputs and validation

The proof is internal recurrence algebra and absolutely convergent series.
Mathlib at pinned commit `9d581dfff2e41de989072ea63abf3daf69311520`
supplies the exponential series, the elementary factorial divisibility
bound, countable probability masses, and standard summable-series operations.
No external comparison theorem, target estimate or moment bound is an input.

The full Lean v4.36.0-rc2 build passed (8,745 jobs), followed by the actual
axiom audit of all 1,728 project theorem/lemma declarations. Only `propext`,
`Classical.choice` and `Quot.sound` occur. Coverage is 21 / 167 numbered
results: 9 main and 12 companion. No Palomar registration is made.

Validated implementation: [281431eefffbf25daa2564d62280b3bd188a6496](https://github.com/Vulkin-prog/paper-p1-lean/commit/281431eefffbf25daa2564d62280b3bd188a6496).
All 178 distinct ledger declaration names were checked by Lean as well.
