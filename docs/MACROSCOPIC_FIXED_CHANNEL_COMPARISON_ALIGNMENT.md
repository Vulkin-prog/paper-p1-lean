# Actual macroscopic full/rational fixed-channel comparison on every finite subfamily

Companion T21.1, arithmetic_consequences.tex:26 and its fixed-height full/rational comparison. The original sources and statement hashes remain preserved.

The actual fixed-channel full/rational power error is now proved internally on the literal macroscopic interval. For every fixed Q, q>=1 and epsilon>0, its threshold precedes every critical length, every positive coprime coefficient pair of height between q and Q, and EVERY finite subfamily E of the original ordered geometric channel. The result is

  sum_E |2^rho - 2^((#units-1)_Nat)| <= M^(1/2+1/q+epsilon).

Both coefficient orientations are covered. The proof retains the original source and target labels and requires no assumed rank, mass, or comparison estimate.

PrivateNormalizedPairLoss first proves the exact finite equality rho=(#units-1)_Nat whenever the normalized union has a private coordinate at each distinct value. This equality includes zero coincidences, using the vanishing FULL value kernel. No geometric, coprimality or asymptotic hypothesis is needed for this finite equality. For nonempty coincidences, exact normalized intersection and union cardinalities identify the compressed rank.

MacroscopicFixedChannelComparison proves that the literal absolute power error is supported on the actual nonprivate pair set. The previously proved square-root host count and the separately proved actual and rational channel power bounds give the stated exponent. The result holds on every subfamily, so later restrictions to separated roots do not require a new counting assumption.

For the positive weights 2^rho-1, the absolute difference of the actual two total sums obeys the same bound. For EVERY Boolean function eta on pairs, the sum of absolute differences between eta*2^rho-1 and eta*2^sigma-1 also obeys it. This last assertion uses the SAME eta on both sides; it does not identify actual affine compatibility with a rational signed code. That identification and the signed channel translation count remain separate obligations.

At the leading 1:2 channel the full/rational error is at most M^(1+epsilon). The general fixed-height statement also supplies the exponent needed for height-three comparisons. P1-MATH-0204 records this improvement. T21.1 remains in progress: separated height-one bounds, actual positive/signed translation sums, parity equivalents and the dyadic positive assembly are still open. Coverage remains 88 proved and 70 conditional out of 167, with nine incomplete results. There are now 203 improvements and one statement-scope correction. No external input, kernel axiom, compiler change or original manuscript edit is introduced. Palomar remains deferred.
