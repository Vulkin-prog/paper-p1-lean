# Coefficient-uniform primitive heights, relative charts and determinant logarithmic scale

Source: companion T1.4, companion_sections/arithmetic_appendix.tex:139, primitive normalization and the relative coefficient/denominator ledger in Steps1–2; also the determinant use in T1.5. Original source hashes remain preserved.

Three coefficient-uniformity steps of companion T1.4 are now proved directly, including their transport through the actual primitive reduction. The determinant vanishing and final solution count remain unfinished.

PrimitiveDeterminantHeights proves that dividing either original coefficient monomial by the actual gcd scale gives exactly the corresponding reduced monomial. Positivity of the reduced coordinates proves s*c_i is at most the original value. Consequently an original bound value<=C*N gives c_i<=C*(N/s), at the reduced height itself. The coefficients remain unchanged and need no coefficient-dependent or polylogarithmic height correction at this step.

DeterminantRelativeChart proves the exact relative chart for c2*e^2*v=c1*d^2*u+h. Its relative error beta satisfies the exact identity beta=(h/n)*(1+alpha)^2, where n=c1*d^2*u. For |alpha|<=1 this gives |beta|<=4*|h|/n, and hence a bound at every fixed source-height comparison. There is no factor c1/c2 in the relative error. The argument includes signed shifts and keeps all required nonzero or positive denominators explicit.

DeterminantLogScale proves the exact denominator-cost identity after the two relative column scalings. It derives the logarithmic relation for the actual two coefficient monomials, and the ideal-scale identity as a specialization. Actual upper comparisons c_i*D_i^2*U_i<=C*N and c1*c2>=1 yield a coefficient-uniform bound for log(UV). Completing a square gives the quantitative actual determinant-scale bound

  logShape <= (9/16)*log(N)*(1+log(C)/log(N))^2.

The fixed comparison error is retained explicitly, rather than replaced by an unspecified coefficient-dependent o(1). The nine-sixteenths exponent is an upper scale bound; it is not a proof that a determinant vanishes or that an auxiliary curve exists.

P1-MATH-0234 records the exact height transport and relative/logarithmic normalization. T1.4 and T1.5 remain in progress for the auxiliary extraction, remaining local curve arguments and short-vector sums. Coverage stays89 proved and72 conditional out of167, with six incomplete numbered results. There are233 improvements and one statement-scope correction. No new external input, axiom, Paper C code port, dependency download, compiler change or original manuscript edit is introduced. Palomar remains deferred.
