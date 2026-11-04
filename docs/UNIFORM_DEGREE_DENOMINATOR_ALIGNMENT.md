# Uniform bounded degrees and strict actual denominator budget

Source: companion T1.4, companion_sections/arithmetic_appendix.tex:139, Step2 auxiliary extraction and its coefficient-height/parameter-order ledger; T1.5 uses that extraction. Original source hashes remain preserved.

The relative-chart determinant decay is now combined with exact row and column costs and a proved bounded-degree choice. One common threshold precedes all local point families. The original-box hypotheses still need to be shown to supply these normalized logarithmic assumptions.

DeterminantDegreeChoice uses A=ceil(B*b/a), retaining the upper rounding error explicitly. For a,b in a fixed positive compact interval and weights sigma,tau of bounded sum, the product margin sigma*tau >= (9/8)*(1+eta)^2*a*b gives one fixed B and a bounded range 1<=A<=Amax such that

  (A*a+B*b)/2 + sigma+tau+1 <= (2/3)*sqrt(2*(A+1)*(B+1)*sigma*tau).

B and Amax depend only on the fixed interval, weight-sum bound and positive margin; they precede the varying parameters and all point families. The chosen A may depend on the varying logarithmic ratio, while belonging to that one fixed finite range.

DeterminantDenominatorBudget proves the exact sums of exponents over the complete rectangle. The column scaling has logarithm H*(A*log(s0)+B*log(t0))/2. If e<=E and u<=U, multiplying all original integer-row denominators by this column product costs at most

  exp(H*(A*log(E^2*s0)+B*log(U^2*t0))/2).

There is no omitted rounding term or moving original coefficient in the determinant constant. DeterminantStrictMargin proves the exact homogeneity of the sharp cost under weights (sigma*T,tau*T). If log(E^2*s0)=a*T and log(U^2*t0)=b*T, the degree margin bounds the fully cleared determinant by C(A,B)*exp(-H*T), hence by C(A,B)*exp(-T).

DeterminantUniformMargin bounds C(A,B) by one finite sum over 0<=A<=Amax and chooses a common T0 before all varying heights, logarithmic parameters, local centers and point families. Its uniform local theorem proves the strict bound |det|*product(e^A*u^B)<1 directly from the normalized chart-error, logarithmic-size and product-margin hypotheses. This theorem assumes no determinant, rank, kernel or solution-count bound.

P1-MATH-0240 closes the uniform degree/denominator comparison in normalized local coordinates. Remaining work includes deriving these local hypotheses from every actual source box and shift, transporting to the actual rational matrices and bounded auxiliary curves, and the later factor-curve counts and lattice summations. T1.4 and T1.5 remain in progress; coverage stays89 proved and72 conditional out of167, with six incomplete numbered results. There are239 improvements and one statement-scope correction. No external input, axiom, Paper C port, dependency download, compiler change or original manuscript edit is introduced. Palomar remains deferred.
