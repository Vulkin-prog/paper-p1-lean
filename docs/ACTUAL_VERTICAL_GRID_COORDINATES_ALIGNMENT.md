# Actual uniformly bounded second-lattice coordinates per quadratic grid index

Source: companion T1.4, companion_sections/arithmetic_appendix.tex:139, uniform second-lattice coordinates; T1.5 uses that reduction. Original source hashes remain preserved.

The ACTUAL second-lattice reduced coordinates are now constructed uniformly and consistently per quadratic GRID index q. VerticalGridMatrices defines the literal matrix with D'=2*C*V', E'=C*U', M'=2M and proves that the actual point transform is exactly this matrix at q=floor(k^2/M). The source comparisons imply1<=D',E', D'<=2*C*N and E'<=C*N. They also give the exact effective pair bound U'*V'<=U*V/rho^2.

UniformVerticalGridCoordinates fixes C,rho>0 and chooses one kappa,N0 BEFORE N, M, the original source Box and q. For M>=32,2M<=N and every q<=4M, it constructs actual integer inverse matrices A,B, det(A)=1, a globally shortest first column and entries bounded by N^kappa. With R=2*(49+16/rho), the actual side lengths are retained as sideLength(R,actual_basis_energy), and satisfy

  0<=L1<=L0,
  L0*L1<=4*R^2*C^2*U*V/(rho^2*M),
  L0<=2*R*(2*(N^2)^2+1),
  R^2*C^2*U'*V'/M<=L0^2.

The constructed SAME matrices and side lengths then bound the inverse integer coordinates of EVERY point of EVERY actual signed population whose original floor index maps to q, whenever M*|h|<=N. Thus neither h, the population nor the point determines a new basis. The proof derives this result from the actual signed point box and the uniform arbitrary-radius grid-coordinate construction. No basis, height, shortest-vector or coordinate bound is supplied as an input.

P1-MATH-0266 closes the actual second-lattice coordinate construction, effective-scale area comparison and consistent indexing needed for the side sum. The global simultaneous basis-family/side-sum assembly, negative auxiliary-chart flip, geometric curve counts and remaining primitive scale assembly remain open. The negative-point statement uses the original d/e chart and does not identify it with the reversed auxiliary chart. T1.4 and T1.5 stay in progress. Coverage stays89 proved and72 conditional out of167, with six incomplete numbered results. There are265 improvements and one statement-scope correction. No new external input, axiom, dependency download, compiler change or original manuscript edit is introduced. Palomar remains deferred.
