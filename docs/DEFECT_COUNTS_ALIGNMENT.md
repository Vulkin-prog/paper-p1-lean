# Companion T1.3: defect-count alignment (in progress)

Original locator: companion V1.6, Lemma T1.3, label
`p1:arith:defects`, `companion_sections/arithmetic_appendix.tex:90`.
**This numbered result is not complete.**

## Proved finite local ingredients

`PaperP1.LargeOddKernel.largeOddKernel` is the product of primes above H
whose valuations in n are odd. Its equality to 1 is proved equivalent to
the intrinsic valuation predicate `HDefective H n`.

Every positive integer satisfying that predicate has its canonical
odd-prime-support times square representation. The square part is reconstructed
by halving its prime exponents, and the odd support lies among primes at most H.
These are proved arithmetic statements, not assumed representations of the
actual values.

`PaperP1.LocalDefectBound.defectsInInterval H U R` is the actual finite set
in the inclusive interval [U,U+R]. Membership is proved equivalent to
`U ≤ n ≤ U+R` and `K_H(n)=1`. The cutoff H and width R are separate.

The proved bound `card_defectsInInterval_lt_of_log` states that, for
R ≥ 1, U ≥ 2R and t ≥ 1, the condition

`2t log(64R) < log U`

implies

`#defects < max(π(H)+1, 2t · 2^((π(H)+1)/t+1))`,

where π(H) is the cardinality of the finite prime set up to H and the
quotient in the exponent is natural-number division.

The proof constructs the augmented small-prime parity code. A kernel word
selects an even square product. The proved T1.1 bound rules out every
nonzero word of weight at most 2t under the single endpoint condition
`(64R)^(2t) < U`. The binary sphere-packing count and rank-nullity give
the Hamming volume bound; a proved binomial estimate gives the length bound.
Both small-cardinality cases are handled. The abstract no-short-square
condition in intermediate modules is discharged by T1.1 in the final result.

Finite counts of represented values and interval overlaps have also been
ported as preparation for global estimates. They do not alone establish the
manuscript's asymptotic bounds.

## Proved explicit rate and global asymptotic count

`LocalDefectRate.codingRadius U R` is the direct floor
`floor(log U / (4 log(64R)))`. Its weak and strict logarithmic conditions
and positivity criterion are proved. The elementary finite Chebyshev bound
`floor(log₂ H) · π(H) ≤ 7H` is proved from Mathlib's primorial estimate.
Consequently, the explicit budget

`7H / floor(log₂ H) + 1 ≤ A · codingRadius U R`

gives the real local rate in `LocalDefectRate.card_cast_lt_log_div`.
The budget and the eventual comparisons with B still need to be derived
uniformly from the manuscript's comparison constants.

`GlobalDefectCount.positiveDefectsBelow H X` is the actual positive set
with K_H(n)=1 and n ≤ X. It is proved equal to the represented-value set,
using canonical reconstruction in both directions. The finite bound is

`#defects ≤ sqrt(X) exp(2 sqrt(H))`.

`global_defect_count_le_rpow_eventually` proves that, for fixed real
C,D ≥ 0 and ε > 0, one threshold works for every cutoff and counting height
with H ≤ D log N and X ≤ CN:

`#defects ≤ N^(1/2+ε)`.

This completes the global N^(1/2+o(1)) conclusion of T1.3. It only needs an
upper logarithmic bound on H. The proof includes absorption of the fixed
sqrt(C) factor and the exact positive set, with no additive zero-value loss.

## Remaining conclusions

The two-defect-window bound is now also proved, including the exact left
boundary of V_x and uniformity over all logarithmic cutoffs and lengths. See
[TWO_DEFECT_ALIGNMENT.md](TWO_DEFECT_ALIGNMENT.md). Its actual finite
configuration count uses T1.2 in both square and nonsquare cases; support
counts and polynomial coefficient heights are proved internally.

To complete T1.3, prove and combine:

- The uniform prime budget and parameter comparisons converting the explicit
  local rate to O(B/log B), with fixed comparison constants.
- The stated versions after fixed dilations and translations.

The global and two-defect asymptotic parts are recorded as proved progress inside T1.3.
The full numbered result remains incomplete, so coverage stays 8/167.

## Provenance

The generic Hamming, augmented-parity, representation and translated Runge
bridges are adapted from the exact Paper C blobs in the reuse ledger.
The quantitative application uses P1's stronger degree-uniform constant,
and the actual local set separates the cutoff from the interval width.
The intrinsic kernel product dictionary is a new P1 proof.
All 830 current proved declarations are included in the kernel-axiom audit.

