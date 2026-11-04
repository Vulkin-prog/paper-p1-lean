# Actual first source-interval lattices with uniform integer coordinates and source-scale boxes

Source: companion T1.4, companion_sections/arithmetic_appendix.tex:139, lattice-coordinate and uniform auxiliary-height steps; T1.5 uses that reduction. Original source hashes remain preserved.

The general reduced-basis construction is now specialized to the ACTUAL first lattice on every original relative interval. Its real matrix, inverse, determinant, image box, coefficient heights and integer coordinate sides are all proved from the source scales.

RelativeIntervalLattice defines the actual matrix and its inverse:

  T = [[M/D,-M*s0/D],[0,1/E]],
  S = [[D/M,s0*E],[0,E]].

Both inverse products are verified and det(T)=M/(D*E). The exact image of an integer pair is ((M/D)*(d-s0*e),e/E). For the original floor-selected relative interval, its first coordinate equals (e/E)*(scaledRatio-floor(scaledRatio)). The actual floor residual and dyadic bounds imply EVERY original pair has both real image coordinates of absolute value at most 2. This uses the actual interval partition; no approximation or extra width premise is supplied.

RelativeIntervalLatticeHeight proves both real matrices have entry height at most 2*Q*N whenever 1<=D,E,M, M<=N, D,E<=Q*N and 0<=s0<=2D/E. One common threshold gives entry height at most N^2. The same center range is proved for EVERY interval index k<=2M, including empty intervals, so the constants do not depend on choosing a representative source point.

UniformRelativeIntervalCoordinates.uniform_interval_coordinates chooses the integer matrix-height exponent and threshold BEFORE N,M,D,E,k. On every original interval it constructs actual inverse unimodular integer matrices, both of uniformly polynomial height, and sides L0,L1 tied explicitly to the actual shortest and reduced image vectors. It proves

  0<=L1<=L0,
  L0*L1<=16*D*E/M,
  4*D*E/M<=L0^2,
  L0<=4*(2*(N^2)^2+1).

EVERY original integer dyadic pair on that interval has its actual inverse integer coordinates bounded by L0,L1. Global minimality of the first basis vector is retained for the later interval summation. The matrix-height exponent is common to all moving intervals and scales; no short-basis, matrix-height or coordinate-box input is introduced.

P1-MATH-0257 closes the actual first source-lattice specialization. Remaining work includes the shortest-vector interval count, the coefficient-uniform vertical regridding and second lattice, geometric curve counts and final sums, together with the relevant primitive reductions. T1.4 and T1.5 stay in progress. Coverage stays89 proved and72 conditional out of167, with six incomplete numbered results. There are256 improvements and one statement-scope correction. No external input, new axiom, dependency download, compiler change or original manuscript edit is introduced. Palomar remains deferred.
