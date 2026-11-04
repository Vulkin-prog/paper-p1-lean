# Complete finite signed-forcing upper ledger with exact type summation

Source: companion T19.16, companion_sections/limits_appendix.tex:1214 and its upper-bound proof. Original source hashes remain preserved.

The actual finite upper-cost ledger in companion T19.16 is now proved, with no target cost, joint probability, footprint size or profile bound supplied as a premise.

SignedTypeWeightSums sums both signs and every excess using their exact heterogeneous signed probabilities. The total type weight is at most p=2^(-L). A general finite product identity factors the two type sums before any geometric estimate; no factor depending on the number of excesses is introduced.

SignedMaximalFootprint constructs the actual prime pivots of each retained maximal support and a type-independent directed site footprint. Every target affected by the original source forcing lies in this literal footprint. Injective interval counting and the internally proved reciprocal-pivot ledger give its total cardinality bound at the actual source and target sites.

SignedCostEnvelope combines the full original Palm cost ledger, the internally proved close joint bound and the actual raw-kernel joint majorant. Its nonnegative site envelope keeps the diagonal, directed hits, close sites and separated raw-rank deficit explicit. Exact type summation gives the original full signed cost bounded by p^2 times the site envelope sum.

SignedDyadicCostUpper proves the literal retained-boundary interval inclusion, counts all close sites, and injects every remaining ordered site pair into the original maximal separated raw-profile mask. The resulting finite estimate, for maximal width B=L+E+2<=N, is

  cost <= p^2 * (12*N*B^2*(pivotSum(3*N)+1) + rawProfile(N,B-1)).

The reciprocal sum and full-value profile are the actual P1 objects. The estimate is unconditional finite arithmetic and probability; it holds for every E and all exact signed types, not only the prescribed moving cutoff. The profile is not assumed small here, and its separately proved geometric bound remains conditional on its six ordinary inputs.

P1-MATH-0230 records the complete finite upper ledger and the absence of an artificial type-count loss. Only the asymptotic absorption and final two-sided assembly remain for T19.16, which stays in progress. Coverage remains 89 proved and 71 conditional out of 167, with seven incomplete numbered results. There are 229 improvements and one statement-scope correction. No additional external input, axiom, Paper C code port, dependency download, compiler change or original manuscript edit is introduced. Palomar remains deferred.
