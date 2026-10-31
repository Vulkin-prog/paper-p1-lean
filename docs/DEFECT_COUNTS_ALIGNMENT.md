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

## Remaining conclusions

To complete T1.3, prove and combine:

- The uniform choice t ≍ log N/log B and prime-count estimate converting the
  finite local bound to O(B/log B), with fixed comparison constants.
- The global N^(1/2+o(1)) count for the actual defective set.
- The N^o(1) count of windows containing two distinct defects, using T1.2 with
  the smooth-support and offset counts.
- The stated versions after fixed dilations and translations.

No asymptotic part above is counted as proved in the coverage ledger.
This work is preparatory to T1.3, and numbered-result coverage remains 8/167.

## Provenance

The generic Hamming, augmented-parity, representation and translated Runge
bridges are adapted from the exact Paper C blobs in the reuse ledger.
The quantitative application uses P1's stronger degree-uniform constant,
and the actual local set separates the cutoff from the interval width.
The intrinsic kernel product dictionary is a new P1 proof.
All 758 current proved declarations are included in the kernel-axiom audit.

