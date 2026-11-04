# Sharp distinct lattice-monomial cost and unconditional normalized determinant decay

Source: companion T1.4, companion_sections/arithmetic_appendix.tex:139, Step2 auxiliary extraction and its coefficient-height/parameter-order ledger; T1.5 uses that extraction. Original source hashes remain preserved.

The distinct weighted monomial-cost obligation from P1-MATH-0238 is now proved, giving an explicit unconditional decay inequality for the normalized relative-chart determinant. The final degree choice and strict integer-denominator comparison remain unfinished.

WeightedLatticeTriangle proves that every finite set of nonnegative lattice points with r1*a+r2*b<=T has cardinality at most (T+r1+r2)^2/(2*r1*r2), for every positive r1,r2 and nonnegative T. The proof counts exact vertical fibres, sums their arithmetic progression, and bounds the resulting quadratic. No limiting lattice-density estimate is assumed.

WeightedLatticeCost orders an arbitrary actual finite lattice set by its weighted cost, retaining ties and distinct indices. The cardinality bound gives the pointwise lower bound sqrt(2*r1*r2)*sqrt(j+1)-(r1+r2) for its j-th point. An elementary telescoping square-root inequality proves the sharp sum lower bound. For H distinct nonnegative lattice points the resulting exact estimate is

  sum(r1*a+r2*b) >= (2/3)*H*sqrt(2*r1*r2*H) - (r1+r2)*H.

The leading coefficient is 2*sqrt(2)/3, with an explicit linear boundary error. Both weights vary arbitrarily over the positive quadrant; no compactness assumption or hidden weight-dependent constant is used in this finite step.

DeterminantExplicitDecay applies this estimate to every injective monomial selection in the exact polynomial expansion. The normalized determinant is now bounded by

  C(A,B)*exp(-(2/3)*H*sqrt(2*r1*r2*H)+(r1+r2)*H),
  H=(A+1)*(B+1),

with the previously explicit degree-only C(A,B), whenever the actual chart errors satisfy |alpha|<=exp(-r1), |beta|<=exp(-r2). The original-variable determinant retains the exact product of column scalings. The former distinct-monomial cost hypothesis has been discharged rather than replaced by an external input.

P1-MATH-0239 closes the sharp weighted lattice-sum part of the determinant method. The remaining fixed-degree choice must dominate the actual row denominators uniformly before N; subsequent factor curve counts and short-vector summations remain open. T1.4 and T1.5 stay in progress. Coverage stays89 proved and72 conditional out of167, with six incomplete numbered results. There are238 improvements and one statement-scope correction. No external input, axiom, Paper C port, dependency download, compiler change or original manuscript edit is introduced. Palomar remains deferred.
