# Actual vertical ratio error at the coefficient-scaled quadratic grid

Source: companion T1.4, companion_sections/arithmetic_appendix.tex:139, second lattice normalization; T1.5 uses that reduction. Original source hashes remain preserved.

The ACTUAL original solution quadruples now satisfy a coefficient-uniform error bound relative to the quadratic integer grid. Let r=(c1/c2)*(D/E)^2, k be the actual floor interval index, and q=floor(k^2/M). For M>=4, the dyadic source bounds, the original signed-shift equation and source>=rho*N imply

  |v/u-r*q/M| <= r*(49+16/rho)/M

whenever M*|h|<=N. All moving-coefficient dependence stays in the explicit scale r; the numerical constant depends only on the fixed positive source lower bound rho. No estimate for these actual points is supplied as a premise.

QuadraticRelativeError proves |2*alpha+alpha^2|<=12/M from |alpha|<=4/M, rescales the signed-shift error using M*|h|<=N, bounds the actual quadratic center by 4*r, and combines these estimates with the proved r/M grid-rounding error. ActualVerticalGrid defines the literal coefficient ratio and grid center, proves the exact center identity, and applies the existing exact normalization of the original integer quadruple. It derives positivity, index bounds, alpha control and the source-relative beta bound from the actual dyadic hypotheses and equation.

P1-MATH-0262 closes the actual vertical ratio normalization, including negative shifts through |h|. The actual second-lattice point box, coordinate and side-sum assembly, geometric curve counts and remaining primitive scale assembly remain open. T1.4 and T1.5 stay in progress. Coverage stays89 proved and72 conditional out of167, with six incomplete numbered results. There are261 improvements and one statement-scope correction. No new external input, axiom, dependency download, compiler change or original manuscript edit is introduced. Palomar remains deferred.
