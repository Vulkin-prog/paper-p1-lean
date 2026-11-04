# Both actual lattice side sums at the ideal paper scale with all rounding losses absorbed

Source: companion T1.4, companion_sections/arithmetic_appendix.tex:139, Step4 final ideal-scale and error-budget passage; T1.5 uses that reduction. Original source hashes remain preserved.

Both complete ACTUAL lattice side sums now have the IDEAL scale and error factor stated in the paper, with the literal rounded scale used to construct the same bases. All rounding, internal summation and fixed-constant losses are absorbed with an explicit nonempty exponent budget.

RoundedScaleSideBudget proves the exact rounded upper bound

  M<=2*N^zeta*exp(logShape).

For every nonnegative weight W it derives sqrt(W*M)<=2*N^(zeta/2)*sqrt(W*exp(logShape)). It gives explicit horizontal and vertical side-cost comparisons, including both axis terms, with the accumulated exponent eta+zeta/2. No estimate for the actual rounded scale is assumed in its application.

IdealSourceLatticeSums fixes eta>0,zeta in(0,7/16) and a final epsilon with eta+zeta/2<epsilon. It chooses kappa0,kappa1,N0 BEFORE N, the nonzero signed polylogarithmic shift and every moving source Box. For the LITERAL rounded M, it constructs both actual basis families with all exact coordinate data, polynomial heights, shortest columns and simultaneous point-coordinate bounds. For EVERY admissible finite original interval set, those SAME exact side lengths satisfy

  sum L0(k)<=N^epsilon*(sqrt(D*E*mathcalM)+D+E),
  sum T0(grid(k))<=N^epsilon*(sqrt(U*V*mathcalM)+U+V),
  mathcalM=exp(logShape(N,D,E,U,V)).

The proof reuses the proved constant-absorption theorem with the strictly positive remaining exponent epsilon-eta-zeta/2. Its two thresholds absorb the horizontal numerical constant and the vertical constant depending only on fixed C,rho. The literal integer bases remain unchanged throughout. The source thresholds M>=32,2M<=N and M*|h|<=N remain available.

P1-MATH-0270 closes the actual two-lattice side-summation and final ideal-scale/error-budget passage. This is not yet the solution-population count: the negative auxiliary-chart assembly, geometric local curve counts and final primitive reductions still remain. T1.4 and T1.5 stay in progress. Coverage stays89 proved and72 conditional out of167, with six incomplete numbered results. There are269 improvements and one statement-scope correction. No new external input, axiom, dependency download, compiler change or original manuscript edit is introduced. Palomar remains deferred.
