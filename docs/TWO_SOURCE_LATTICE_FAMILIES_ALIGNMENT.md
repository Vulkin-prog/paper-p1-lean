# Simultaneous actual source lattice families and both complete side sums

Source: companion T1.4, companion_sections/arithmetic_appendix.tex:139, both lattice-coordinate constructions and Step4 summations; T1.5 uses that reduction. Original source hashes remain preserved.

BOTH actual source lattice families now exist simultaneously for one source box and one determinant scale, with their full coordinate data and complete side sums. The first family is chosen once per original interval index k; the second is chosen once per actual quadratic grid index floor(k^2/M). The choices precede the population and the finite interval set.

HorizontalGridCoordinateData records the exact radius2 side formulas, actual integer inverse matrices, determinant1, polynomial entry heights, shortest first column, side order/product, upper/lower side controls and coordinate bounds for every original dyadic integer pair with the specified floor index. Its uniform existence follows from the actual source coordinate bounds and the already proved source interval construction.

UniformHorizontalLatticeFamily constructs one actual family of those bases and proves its complete sum

  sum L0(k) <=60*N^epsilon*sqrt(D*E*M)+32*E+8*D.

It discharges the primitive-vector and coordinate-height premises using the SAME actual bases whose sides bound the point coordinates. TwoSourceLatticeFamilies then constructs BOTH this family and the complete actual vertical family together. It chooses kappa0,kappa1,N0 BEFORE N, M and all moving source data. For M>=32 and2M<=N, both side sums hold for EVERY SAME finite original index set with M/4<=k<=2M, while all horizontal and vertical coordinate data remain available for these SAME constructed functions.

The vertical sum remains the explicit original-scale bound

  (512*R*C/rho)*N^epsilon*(sqrt(U*V*M)+U+V), R=2*(49+16/rho).

No integer basis, inverse, shortest vector, coordinate height, side weight or weighted counting estimate is assumed. In particular, the coordinates used in the algebraic reduction can now be chosen with the simultaneous arithmetic sums already proved for them.

P1-MATH-0268 closes the joint actual two-orientation lattice-family construction and side summation. The instantiation at the final actual rounded determinant scale, negative auxiliary-chart flip, geometric local curve counts, rounded-scale loss absorption and primitive scale assembly remain open. T1.4 and T1.5 stay in progress. Coverage stays89 proved and72 conditional out of167, with six incomplete numbered results. There are267 improvements and one statement-scope correction. No new external input, axiom, dependency download, compiler change or original manuscript edit is introduced. Palomar remains deferred.
