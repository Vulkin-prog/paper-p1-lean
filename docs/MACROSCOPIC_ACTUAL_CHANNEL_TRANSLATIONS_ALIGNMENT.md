# Actual interval source translations with exact macroscopic lower endpoint

Companion T21.1, arithmetic_consequences.tex:26 and the leading1:2 translation argument in its proof. Original sources and statement hashes are preserved.

The literal leading-channel translation count in companion T21.1 is now proved for the original complete-vertex source pairs, with both orientations and the exact lower endpoint retained.

IntervalSourceTranslations develops the finite calculation on an arbitrary interval [lo,hi), rather than assuming dyadic endpoints. For positive a<b, sufficiently large lo and offsets u,v of size at most B, the actual source roots x=a*t-u and y=b*t-v belong to the interval exactly when

  ceil((lo+u)/a) <= t < ceil((hi+v)/b).

Under the explicit nonempty-interval condition, the count differs from hi/b-lo/a by at most B/a+B/b+1. The natural-valued source map is proved injective and surjective onto the actual pair set using the original exact unit equation. No abstract or assumed translation count is used. A stronger explicit endpoint condition proves x+L<y for every such unit source, making the two root orientations disjoint; their count is exactly twice the forward count.

MacroscopicChannelTranslations proves that all finite endpoint conditions hold eventually on [ceil(M^delta),M), for every fixed0<delta<1 and all critical lengths. The common threshold precedes every complete-vertex pair i,j. The forward1:2 count differs from M/2-ceil(M^delta) by at most3B; the symmetric count differs from M-2ceil(M^delta) by at most6B. Replacing the ceiling by the real power is also justified, giving errors4B and8B respectively. Every actual pair in this symmetric source set is proved separated by more than L.

P1-MATH-0206 records these literal finite bijections and uniform endpoint bounds. This establishes the translation factor used in the leading macroscopic term, but not yet its full signed or unsigned even-selection enumeration. The global rational-code partition, actual signed affine identification, leading parity equivalents and dyadic positive assembly remain open, so T21.1 stays in progress. Coverage remains88 proved and70 conditional out of167, with nine incomplete results. There are205 improvements and one statement-scope correction. No external input, new axiom, dependency, compiler change or original manuscript edit is introduced. Palomar remains deferred.
