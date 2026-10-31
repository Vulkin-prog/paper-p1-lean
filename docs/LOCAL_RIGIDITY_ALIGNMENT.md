# Article Lemma 2.1: local rigidity

**Status: proved**, full article Lemma 2.1, including the finite Griesmer
inequality, general and critical logarithmic regimes, and exact subcritical
independence under the infinite prime-sign measure. Completed coverage is
14 / 167. The critical-band rank and marginal consequences are also proved.

Original locator: article V1.6, page 11, `p1:limits:local-rigidity`,
`main_sections/exact_setup.tex:27`. The original statement is unchanged.

## Finite code and arithmetic statements

`WindowRelationCode.windowRelationCode U B` is the intersection of the kernels
of the full prime-parity map and the coordinate-sum map on `Fin B → F₂`.
For U>0, `mem_windowRelationCode_iff_even_square` identifies its members with
the literal even selections of `[U,U+B-1]` having rational square product.
The parity map retains every prime coordinate.

`PrivateWindowPrimes.coefficient_zero_of_not_defective` proves that every
relation is supported on actual B-defective vertices. A prime greater than B
cannot divide two distinct window vertices. Evaluating a relation at a
nonzero such parity coordinate therefore forces its coefficient to vanish.
This uses no assumption that the large prime occurs to exponent one.

`LocalRigidityCode.defectCode U B` is the actual augmented small-prime matrix
on the defective values of this window. Its redundancy is at most π(B)+1.
The finite count `primeCount B` is proved equal to `Nat.primeCounting B`,
with the inclusive convention p≤B. The proved T1.1 theorem gives minimum
nonzero weight at least

`rungeDistance U B = ceil(log U / log(64B))`.

The finite hypotheses are B≥1 and U≥2B. They ensure a positive distance and
supply T1.1's base/radius condition. The uniform eventual specialization in the manuscript's macroscopic
logarithmic regime is proved by `UniformLocalRigidity.finite_griesmer_eventually`,
with one threshold before all finite Griesmer orders.

## Griesmer bound proved internally

`BinaryResidual` deletes the support of an attained minimum nonzero word.
It proves that the kernel is its one-dimensional span, the retained length
is the old length minus its weight, and the residual minimum distance is at
least half the old minimum distance, rounded up.

`GriesmerBound.griesmer_with_unused_dimension` iterates this construction
for every t≤r. It retains the unused r−t dimensions, rather than merely
proving the full-rank sum. The resulting redundancy inequality is proved
in both quotient and ceiling notation. The positive-distance ceiling identity
and the fact that the sum is at least t are proved as well.

This is an internal proof of the bound cited in
[Griesmer, Section 2, equation (2.10)](https://bitsavers.trailing-edge.com/pdf/ibm/IBM_Journal_of_Research_and_Development/045/ibmrd0405M.pdf),
not an unproved coding-theory input.

`WindowRelationCode.relationRestriction` injects the full window relation code
into the actual defect code. Injectivity, the dimension comparison and the
concrete image condition are all proved. A bijection is not needed for the
Griesmer obstruction. `window_relation_griesmer` is the exact finite
ceiling-sum bound for the full window relation dimension.
`window_relation_griesmer_real` uses ordinary real subtraction, with the
natural-to-real conversion proved explicitly.

## Effective ranks and actual probabilities

`LocalRunRank.relationEvenEquiv` identifies the window code for
U=x−1, B=L+1 with the kernel of `evenSquareClassMap x L`.
`squareClass_rank_add_relation_rank` proves

`dim S_x + dim(window relation code) = L`.

The finite obstruction at t=2 therefore implies `dim S_x ∈ {L,L−1}`.
`infiniteMarginal_eq_nominal_or_double` gives the exact actual marginal
`p_x ∈ {2^(-L), 2 * 2^(-L)}` under this finite criterion and p_x>0.
The proof uses the actual infinite prime-sign measure, constructs an adequate
finite cylinder, and retains affine incompatibility through the positivity
condition.

## Uniform asymptotic thresholds

The sharp asymptotic comparison of π(B) with B/log B is now proved by
`SharpPrimeCount.prime_counting_ratio_tendsto` and
`SharpPrimeCount.primeCount_upper_eventually`. Its leading constant is essential for
the stated thresholds `c < 2 - 2^(1-t)`, including the critical c=1/log 2.
The exact one-sided input is recorded as proved `P1-ARITH-PNT` in the
[literature inventory](LITERATURE_INPUTS.md), with a selected and recompiled
analytic proof, full provenance and the actual axiom audit. It is not an
unproved assumption of any P1 theorem. See
[PNT statement alignment](PRIME_NUMBER_THEOREM_ALIGNMENT.md).

`PrimeLogBudget.prime_log_budget_ratio_tendsto` proves
`(pi(B)+1+t) log(64B) / B → 1` for each fixed t. The integer cap
`ceil(c log N)` has ratio to log N tending to c and ratio to N tending to
zero. `LogarithmicWindowCap.cap_prime_budget_tendsto` then proves the
normalized prime budget tends to c. The normalized lower base log(aN)
tends to one. A single strict-gap threshold therefore works before every
window base and length.

`WindowRelationMonotone.window_relation_finrank_mono` extends actual even
square relations by zero. It includes the empty code and needs no arithmetic
assumption. Thus every shorter window is controlled by the common cap.
`LocalRigidityThreshold.griesmerFactor_eq_paper` identifies the factor with
`2 - 2^(1-t)`, using integer exponent subtraction.

The source-exact asymptotic declarations are

- `UniformLocalRigidity.finite_griesmer_eventually`: for fixed a>0, D≥0,
  one threshold precedes N,U,B and **every** t in the exact finite inequality;
- `LocalRigidityRegimes.relation_rank_lt_of_length_asymptotic`: literal
  B~c log N and c<2-2^(1-t), with t fixed before the threshold;
- `LocalRigidityRegimes.critical_relation_rank_le_one_of_error`: literal
  B=log N/log 2+o(log N), giving relation rank at most one;
- `LocalRigidityRegimes.critical_band_relation_rank_le_one`: one threshold
  for every L in a fixed real critical band, with B=L+1.

The comparison `1/log 2 < 3/2` is proved using the compiled Mathlib
`Real.log_two_gt_d9` bound at the pinned revision. No prime-count or
logarithmic-comparison estimate is left as a theorem premise.

## Exact independence and critical-band marginals

`Affine/IndependentRows.lean` proves that every output of a full-rank binary
row system has the fair-cube mass, without assuming compatibility of that
output. `RelativeSignIndependence.map_infiniteStartBits_eq_pi` identifies
the **entire** joint law of the relative bits with the product of fair bit
measures under the actual infinite model. `iIndepFun_infiniteStartBits` and
`iIndepFun_relativeSigns` give Mathlib's independence predicate for those
bits and actual multiplicative relative signs.

`RelativeSignIndependence.subcritical_window_relative_signs_independent`
proves the last assertion of Lemma 2.1 for every ε>0, positive vertex count B,
and B≤(1-ε)log N. The common threshold precedes every U and B. The anchor is
the second vertex U+1, and the B−1 indexed vertices are all the other window
vertices. The B=1 family is empty; ε≥1 is handled as well. This is exact
independence, not a dimension-only or marginal-probability surrogate.

`LocalRigidityConsequences.critical_band_marginals` gives one positive
constant and one threshold for every actual admissible start and every
critical-band length. It proves the two effective ranks, exact p or 2p
marginals, and the pointwise bound
`p_x ≤ (2 * 2^C) / N`. The probabilities are actual infinite-model Bochner
marginals; zero-probability incompatible starts are handled by the existing
admissibility convention. The pointwise bound supplies the upper bound for
any finite maximum of admissible marginals.

## Stronger base hypothesis

All these results need only U≥aN for a fixed a>0. The upper comparison in
U≍N is unnecessary. The general rank theorem is also uniform for **all**
B≤c log N with c below the same sharp threshold, rather than only a chosen
sequence B~c log N. Constants and exponents are unchanged.
This confirmed improvement is recorded as `P1-MATH-0004` in the
[change log](MATHEMATICAL_CHANGELOG.md).

The full build and actual kernel audit passed for 1,223 declarations at this
stage. Only `propext`, `Classical.choice` and `Quot.sound` occur. The original
manuscript statement and all source identities are preserved.
