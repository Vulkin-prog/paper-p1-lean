# Uniform actual grid coordinates and side sums at the vertical image radius

Source: companion T1.4, companion_sections/arithmetic_appendix.tex:139, second-lattice coordinate boxes and side summation; T1.5 uses that reduction. Original source hashes remain preserved.

The reduced coordinate boxes and quadratic-grid side sums now retain the ACTUAL image radius required by the second lattice. This removes the remaining mismatch between the radius2 first-lattice statements and the fixed radius2*(49+16/rho) of the actual vertical points.

UniformRelativeGridCoordinates constructs actual integer inverse matrices A,B with det(A)=1, globally shortest first column and polynomial entry heights, uniformly for every relative grid with1<=D,E,M, M<=N and D,E<=Q*N. A single kappa,N0 is chosen BEFORE N, M, the grid scales and index, and even before the nonnegative real image radius R. The sides retain their exact definitions in terms of R and the actual basis energies. The proof establishes

  0<=L1<=L0, L0*L1<=4*R^2*D*E/M,
  R^2*D*E/M<=L0^2,
  L0<=2*R*(2*(N^2)^2+1).

Every literal integer point whose real lattice image has both coordinates at most R has inverse integer coordinates bounded by these same L0,L1. No basis, shortest vector, height or point-coordinate bound is assumed; the proof reuses the actual bounded lattice reduction and matrix-height construction.

QuadraticGridRadiusSum proves the exact identity sideLength(R,P)=(R/2)*sideLength(2,P), including P=0 without an extra assumption. It transfers the already proved actual quadratic-grid side sum to EVERY nonnegative R, preserving the uniform threshold and the actual matrix/vector choices. Consequently the actual vertical radius can be carried into the finite original-interval sum as the fixed factor R/2.

P1-MATH-0265 closes arbitrary-radius reduced grid coordinates and radius-aware second-grid summation. Their simultaneous application to the actual effective scales and consistently chosen grid bases, signed-chart assembly, geometric curve counts and remaining primitive scale assembly remain open. T1.4 and T1.5 stay in progress. Coverage stays89 proved and72 conditional out of167, with six incomplete numbered results. There are264 improvements and one statement-scope correction. No new external input, axiom, dependency download, compiler change or original manuscript edit is introduced. Palomar remains deferred.
