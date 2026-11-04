# Uniform small-square-part saddle variation and actual scale monotonicity

Source: companion T19.15, companion_sections/limits_appendix.tex:1138 and the uniform small-a argument in its proof. Original source hashes remain preserved.

The uniform scale comparison needed for the square-part reduction in companion T19.15 is now proved from the actual implicit saddle and explicit logarithmic functions.

ExplicitSaddleVariation proves finite differences of log H and log log H with their correct lower-endpoint denominators. A positive square-root factorization then bounds G(H)-G(t) by3*(H-t)*G(H)/H. This bound does not differentiate an asymptotic remainder.

HardSaddleGrowth deduces eventual H<=V(H)^2<=H*log H, V(H)=o(H), log H=o(V(H)), positive-root growth and G(H)<=3V(H) from the already checked actual-root limits. UniformSaddleVariation combines these finite bounds with log H=o(nu(H)): for every fixed A>=0 and epsilon>0, one threshold precedes EVERY t in [H-A*V(H),H], and |G(H)-G(t)|<=epsilon*nu(H).

SaddleMonotonicity proves monotonicity of the actual implicit parameter, cutoff V and second scale nu on their stated upper-branch domain. Thus ordinary prime-sum remainder bounds at every smaller argument in the square-part range can be compared with the same ambient nu(H), without a new uniformity premise.

P1-MATH-0221 records these internal scale comparisons. The ordinary reciprocal-prime theorem and its final transfer to the actual full/dyadic odd-pivot sums remain to be assembled, so T19.15 stays in progress. Coverage remains89 proved and70 conditional out of167, with eight incomplete numbered results. There are220 improvements and one statement-scope correction. These are new P1 proofs using the already attributed saddle modules; no additional Paper C source port, external input, new axiom, dependency download, compiler change or original manuscript edit is introduced. Palomar remains deferred.
