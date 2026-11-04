# Complete actual first-lattice side sum by finite inverse-square tails

Source: companion T1.4, companion_sections/arithmetic_appendix.tex:139, lattice-coordinate and uniform auxiliary-height steps; T1.5 uses that reduction. Original source hashes remain preserved.

The actual first-lattice weighted interval sum is now proved, including both primitive axes. A finite inverse-square-tail argument replaces the dyadic summation and avoids an extra logarithmic loss.

FiniteSquareTail proves the following general finite inequality. If f is nonnegative on a finite set S and every positive threshold L satisfies

  #{x in S : f(x)>=L}*L^2 <= C,

then sum_S f <= 2*sqrt(C)*sqrt(#S). The proof removes a minimum term by strong finite induction. Its size is at most sqrt(C)/sqrt(#S); the already proved reciprocal-square-root increment inequality telescopes the entire sum. The division-form tail variant is also proved. No sorting, limiting argument, infinite sum or tail-sum estimate is supplied as an input.

RelativeIntervalNonAxisSum applies the actual divisor tail count from P1-MATH-0259 with internal exponent 2*epsilon. The literal interval cardinality is at most 2M, and the square-root calculation gives

  sum_nonaxis L(k) <= 60*N^epsilon*sqrt(D*E*M).

The constant follows from 4*432*2=3456<=60^2. The output exponent is the original arbitrarily small epsilon; no extra logarithmic factor or exponent loss remains.

RelativeIntervalSideSum supplies a literal nonnegative three-filter cover and combines this non-axis sum with BOTH actual primitive axis sums. For every finite selected interval set in the original index range, with k>=M/4 and any actual primitive vector choice of b-coordinate height at most N^kappa, it proves

  sum_I L(k) <= 60*N^epsilon*sqrt(D*E*M)+32*E+8*D,

where L(k)=4/|T_k*z(k)| uses the actual source lattice matrix. The threshold precedes N, M, both source scales, the selected intervals and the chosen vectors. The actual constructed shortest-vector bases from P1-MATH-0257 supply the primitive columns and common polynomial heights needed here; no shortest-vector interval-sum premise is introduced.

P1-MATH-0260 completes the actual first-lattice interval arithmetic and its weighted side summation. Remaining work concerns the second lattice and its coefficient-uniform quadratic regridding, the geometric local curve counts, and remaining uniform primitive-scale assembly before the final solution-count theorem. T1.4 and T1.5 stay in progress. Coverage stays89 proved and72 conditional out of167, with six incomplete numbered results. There are259 improvements and one statement-scope correction. No external input, new axiom, dependency download, compiler change or original manuscript edit is introduced. Palomar remains deferred.
