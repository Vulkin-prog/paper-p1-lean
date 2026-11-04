# Complete side summation on the actual quadratic second grid

Source: companion T1.4, companion_sections/arithmetic_appendix.tex:139, second-lattice side summation; T1.5 uses that reduction. Original source hashes remain preserved.

The complete finite side summation now applies to the ACTUAL quadratic grid used by the second lattice, including its lower index range and both primitive axes. This closes the second-grid arithmetic without an assumed lattice-count estimate.

RelativeIntervalGeneralAxis replaces the special lower index condition k>=M/4 by the literal condition M<=A*k, for any nonnegative real A. The primitive first-axis contribution satisfies M*L<=4*A*E and its finite sum is at most8*A*E. The other primitive axis retains its at most8*D sum. RelativeIntervalGeneralSum combines these exact axis bounds with the already proved non-axis divisor/strip and square-tail argument. A common threshold BEFORE N, M, D, E, the actual finite index set, A and the primitive vector choices gives

  sum L(k) <= 60*N^epsilon*sqrt(D*E*M)+8*A*E+8*D.

QuadraticLatticeSideSum applies this to M'=2M and the actual finite grid image q=floor(k^2/M). For M>=32 and the original range M/4<=k<=2M, every actual grid index satisfies M'<=64*q and q<=2M'. The already proved fibre multiplicity TWO transfers the grid side sum back to the original interval indices. For primitive vector choices made consistently per grid index and bounded second coordinate <=N^kappa, with2M<=N,

  sum_original L(grid(k)) <= 120*N^epsilon*sqrt(D*E*(2M))+1024*E+16*D.

This statement concerns the literal sideLength2 of the actual transform matrix at each grid center, not an arbitrary family supplied with a count estimate. Its uniform threshold is chosen before every moving coefficient and source box. P1-MATH-0263 closes the arithmetic side summation for the second grid. The actual second-lattice point box and effective-scale/coordinate assembly, geometric curve counts and remaining primitive scale assembly remain open. T1.4 and T1.5 stay in progress. Coverage stays89 proved and72 conditional out of167, with six incomplete numbered results. There are262 improvements and one statement-scope correction. No new external input, axiom, dependency download, compiler change or original manuscript edit is introduced. Palomar remains deferred.
