# Actual hard saddle and precise additive second-scale expansion

Source: companion T19.15, companion_sections/limits_appendix.tex:1138 and the preceding implicit scales and pivot-scale display. Original source hashes remain preserved.

The actual implicit hard saddle of companion T19.15 now has internally proved existence, uniqueness and the precise additive square-root expansion at the second scale nu=H/V.

Seven mathematical source modules from Paper C were recovered at immutable commit b9fa9ba490f201b408a302a86f1594ee620b228b. Their source bytes were verified against the exact Git blob hashes; the Apache-2.0 attribution, scope comparison and compiler adaptations are recorded in PAPER_C_REUSE.md. Public module declarations, namespaces and two deprecated dependent-if rewrites were adapted to Lean v4.36.0-rc2. No old compiled artifacts or unproved analytic interface was imported.

ExponentialIntegral constructs the real positive exponential integral with its Euler--Mascheroni anchor and proves its derivative. SaddleBranch constructs the unique upper inverse of exp(u)/u on u>=1. SaddleParameters constructs the actual root of V=a*D(H/V), proves its domain and uniqueness, and includes the a=1 hard scale. ExponentialIntegralAsymptotics proves the two-term expansion and a quantitative remainder by derivative comparison. SaddleAsymptotics, SaddleExpansion and SaddleScales prove the actual root expansions, including the constants -log(2)-2, growth of nu and log(H)=o(nu).

The new P1-only HardSaddleExplicitScale module proves the exact conversion missing between the squared expansion and the manuscript's additive formula. With G(H)=sqrt(2H(log H+log log H-log2-2)), the normalized gap (2V-G(H))/(H/V) tends to zero. A finite factorization bounds its absolute value by twice the squared-expansion error, so neither the displayed additive expansion nor an arbitrary sequence with that expansion is assumed.

P1-MATH-0220 records this internally checked saddle-scale construction. The ordinary reciprocal-prime input, uniform small-square-part comparison and final full/dyadic reciprocal-pivot equivalent remain open, so T19.15 stays in progress. Coverage remains89 proved and70 conditional out of167, with eight incomplete numbered results. There are219 improvements and one statement-scope correction. No new axiom, dependency download, compiler change or original manuscript edit is introduced. Palomar remains deferred.
