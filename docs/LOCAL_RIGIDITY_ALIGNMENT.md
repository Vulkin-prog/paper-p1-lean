# Article Lemma 2.1: local rigidity

**Status: in progress.** The finite Griesmer inequality is proved for the
actual even square-relation code. The asymptotic conclusions are not yet
claimed, so the completed coverage remains 9 / 167.

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
supply T1.1's base/radius condition. They hold eventually in the manuscript's
macroscopic logarithmic regime; that uniform eventual specialization remains
to be proved.

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

## Remaining obligations

The sharp asymptotic comparison of π(B) with B/log B is not supplied by the
existing elementary Chebyshev bound. Its leading constant is essential for
the stated thresholds `c < 2 - 2^(1-t)`, including the critical c=1/log 2.
The exact one-sided input needed is recorded as `P1-ARITH-PNT` in the
[literature inventory](LITERATURE_INPUTS.md). It is not assumed by any theorem
in this finite development.

Still to formalize: the sharp prime-count input; the simultaneous logarithmic
limits with uniform macroscopic bases; the critical-band rank conclusion;
the embedding/projection argument for every smaller subcritical window; and
the uniform O(N⁻¹) marginal consequence in the critical band.

No new mathematical correction is asserted by this stage. The three confirmed
improvements in the change log are unchanged.
