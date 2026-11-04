# Actual macroscopic leading rational-unit sums and distinct exact parity formulas

Companion T21.1, arithmetic_consequences.tex:26, including p1:consequences:S12 and the leading1:2 translation/selection calculation. Original source and statement hashes remain preserved.

The leading macroscopic rational-channel calculation in T21.1 is now proved for the ACTUAL positive and predecessor-signed unit sums on the original roots, rather than for an abstract channel mass.

IntervalUnitFourierAggregate reindexes the actual nonzero even unit selections by the existing canonical finite words. It proves the positive and signed sums on every arbitrary interval [lo,hi) equal literal pattern/source-pair aggregates. The two orientations are included exactly, using their proved disjointness. A finite weighted translation estimate retains signed cancellation in the main term and bounds the endpoint error by the positive channel sum. No target counting or mass estimate is assumed.

MacroscopicLeadingUnitSums defines the literal leading totals as twice the forward1:2 sum over all original macroscopic roots. For both positive unitWeight and signedUnitSum, it proves the main terms

  (M - 2*M^delta) * U_1,2(L),
  (M - 2*M^delta) * S_1,2(L),

with a common explicit absolute error at most8*B*U_1,2(L). The exact ceiling version has error6*B*U_1,2(L). Ceiling replacement uses the proved signed bound |S|<=U, preserving the actual predecessor sign rather than replacing it by a positive weight. The finite positive channel upper bound and critical power transport then give the sharper endpoint error M^(1/2+epsilon), uniformly over every critical length after the threshold.

OneTwoChannelParity proves the exact printed signed identity, for L=2m+s, s<2 and m>=1:

  S_1,2(L)=2^(m-1)*[(s+1)m+s^2+s+4]-3L+1.

It also proves the exact positive identities with B=L+1=2k+r. For k>=2 and r<2, the full positive sum is

  U_1,2(L)=2^(k-1)*[(2+r)k+6+4r]-3B-2.

The even-B and odd-B cases are verified separately. This is the full finite channel sum, including the nonplateau terms. The distinct parities of B and L are kept explicit throughout.

P1-MATH-0207 records this actual leading rational-unit calculation. The global rational-code partition, comparison with actual signed affine weights and final relative equivalents, and the dyadic positive assembly remain separate work. T21.1 stays in progress. Coverage remains88 proved and70 conditional out of167, with nine incomplete results. There are206 improvements and one statement-scope correction. No external input, new axiom, compiler change or original manuscript edit is introduced. Palomar remains deferred.
