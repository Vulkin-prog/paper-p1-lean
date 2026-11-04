# Quantitative fixed-height macroscopic residual rank with uniform constant order

Companion T21.1, arithmetic_consequences.tex:26 and its fixed-height residual comparison. Original source and statement hashes are preserved.

Companion T21.1 now has the quantitative fixed-height macroscopic
residual bound O(B/log(B)), including the complete enlarged alignment
with zero exact units. The common constant is chosen BEFORE the
critical-band constant C. The actual profile sums remain open and
numbered coverage is unchanged.

MacroscopicRootLogScale proves the exact scale transport for every
source x in [ceil(M^delta),M), with delta>0 and critical L:

  lowerScale*log(x) <= B=L+1 <= (upperScale/delta)*log(x).

This uses both literal endpoint inequalities, log(x)<=log(M) and
log(x)>=delta*log(M). It allows the already proved local defect
count theorem to be applied at N=x itself. No bounded endpoint ratio
or comparability of x with the ambient M is assumed.

MacroscopicFixedHeightResidual.large_kernel_rate fixes Q>=1, delta>0
and D>=0, then chooses K>0 before every C and before the uniform M
threshold. For every actual enlarged aligned pair of height b<=Q,
and every actual cutoff H with 2*radius(b,L)<=H<=D*B, it proves

  dim(largeKernel(actualNormalizedUnion,H)) <= K*B/log(B).

The normalized union is contained in its actual interval with base
U=b*x-3bB and radius R=6bB. The proof discharges R<=H, R<=6Q*B,
x/2<=U<=2Q*x and the transported critical word scales. The original
local defect theorem is then used at the actual source x. A proved
fixed polynomial source bound puts every x past its required threshold
and supplies all geometric positivity and radius conditions.

The full residual value-kernel bound follows by the literal inclusion
in the large-prime row kernel. Its common K depends only on Q and
delta before C. The actual pair-loss consequence is also proved:

  pairLoss <= max(#exactUnits-1,0) + K*B/log(B).

All sources and targets lie in the original macroscopic interval,
all actual normalized units and residual values are retained, and
the zero-unit case uses the exact natural subtraction convention.
No finite-rank, defect-count or profile bound is an unformalized input.

This supplies the quantitative fixed-height strengthening of the
uniform macroscopic o(B) rank extension. To obtain the full positive
and signed profile statements of T21.1, the actual exceptional-host
counts, rational channel translation sums, high-height mass sums,
parity identities and final equivalents still have to be assembled.
The local rank estimate alone is not counted as a profile theorem.

P1-MATH-0200 records this internal strengthening and explicit constant
order. Coverage stays 88 proved and 70 conditional out of 167, with
nine incomplete results. There are 199 improvements and one statement-
scope correction. No new external input, kernel axiom, compiler change
or software dependency is introduced. Original manuscript files remain
byte-identical and Palomar remains deferred.
