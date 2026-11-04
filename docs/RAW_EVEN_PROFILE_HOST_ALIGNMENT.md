# Actual raw-to-even weighted profile comparison with the genuine host correction

Source: companion T19.16, companion_sections/limits_appendix.tex:1214 and its use of the full-value profile; finite raw/even relation comparison is made on the actual P1 maps. Original source hashes remain preserved.

The finite full-value profile comparison needed for the upper direction of T19.16 is now proved directly for the actual P1 raw and even relation maps. The extra correction is counted only on actual unrestricted raw-relation hosts.

RawEvenProfileComparison restricts the two actual block parity sums to the full raw kernel. Its kernel is explicitly linearly equivalent to the complete even-relation code. Rank-nullity proves fullRank<=pairLoss+2, including all local relations. Pointwise positive weights then satisfy the sharp finite bound with an extra3 only when fullRank is nonzero. For EVERY ordered pair mask F, with no separation or regularity premise,

  sum_F(2^fullRank-1) <=4*sum_F(2^pairLoss-1)+3*#rawHosts(F).

This avoids an artificial correction proportional to the size of the whole ambient pair square.

RawEvenProfileHosts proves that nonzero actual full rank is EQUIVALENT to the literal unrestricted nonempty raw parity relation in the two formal windows. Neither block is required to have even selection. Every raw host in any dyadic submask is therefore covered by the existing actual raw-host population. The internally proved global host count yields #rawHosts(F)<=N^(3/2+epsilon), uniformly before every logarithmic width and every original submask. Local defects, diagonal hosts and incompatible start constraints are retained.

P1-MATH-0226 records this exact comparison and host correction. These are new P1 proofs using the existing actual parity maps and the already proved host count; no additional Paper C code is ported. The sharp lower forcing cost and its power obstruction are complete under EIPInput. The weighted upper profile and actual upper-cost assembly remain open, so T19.16 stays in progress. Coverage remains89 proved and71 conditional out of167, with seven incomplete numbered results. There are225 improvements and one statement-scope correction. No new external input, axiom, dependency download, compiler change or original manuscript edit is introduced. Palomar remains deferred.
