# Actual non-axis interval counts from moving real strips and positive divisor fibres

Source: companion T1.4, companion_sections/arithmetic_appendix.tex:139, lattice-coordinate and uniform auxiliary-height steps; T1.5 uses that reduction. Original source hashes remain preserved.

The actual first-lattice non-axis interval count is now proved with a uniform positive-power divisor loss. The proof supplies every finite counting step and reuses the already proved subpolynomial divisor estimate; no interval-count estimate is introduced as an input.

IntegerRealIntervalCount proves literal finite integer counts in arbitrary moving real intervals and strips. Minima and maxima of an actual finite integer set give at most b-a+1 points in [a,b]. Hence a band |n-center|<=B has at most 2B+1 integer points. A finite integer-pair set with |a|<=A and |n-R*a|<=B has at most (2A+1)*(2B+1) points, uniformly for every real coefficient R and center.

IntervalProductDivisorCount applies this to the ACTUAL interval index k and product n=b(k)*k. At a fixed pair (a,n), every positive index k is a positive divisor of |n|. Thus the literal fibre cardinality is at most the usual divisor count; no factor for signs or uniqueness of the chosen lattice vector is needed. Nonzero b and positive k prove n nonzero. If |b(k)|<=N^kappa and k<=2N, the actual product height is at most N^(kappa+2). The existing proved DivisorSubpolynomial theorem then gives one N0 before all moving strips, populations and selected vectors.

RelativeIntervalNonAxisCount.uniform_nonaxis_intervals specializes these counts to the exact source-lattice coordinate and residual bounds. For ANY selected intervals with both vector coordinates nonzero, b-coordinate height at most N^kappa and actual side length at least L>0, it proves

  #I <= 432*N^epsilon*D*E/L^2.

The exponent and threshold precede all moving source scales and vector choices. Nonzero integer coordinates absorb the additive one in both interval counts, so the estimate remains uniform even when D/L or E/L is small. The coefficient M*E/D is an arbitrary real number; no hidden integrality or coefficient-ratio restriction is used. The result is a tail bound for all sides at least L, stronger than requiring a single dyadic side band.

P1-MATH-0259 closes the finite first-lattice non-axis interval divisor count. Summation of these side contributions, the second lattice/regridding, geometric curve counts and remaining primitive scale reductions are still to be assembled. T1.4 and T1.5 stay in progress. Coverage stays89 proved and72 conditional out of167, with six incomplete numbered results. There are258 improvements and one statement-scope correction. No external input, new axiom, dependency download, compiler change or original manuscript edit is introduced. Palomar remains deferred.
