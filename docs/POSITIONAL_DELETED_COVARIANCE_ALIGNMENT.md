# T19.10: all fixed deletion weights and remaining covariances

Source: companion_sections/limits_appendix.tex:659-723. The finer intensity and sharp two-edge conclusions remain open.

CompanionT19.10 now has its full summed factorial covariance assertion,
in addition to the previously checked ordinary field-distance assertion.
Both actual original deleted fields are compared with the intended
independent Poisson background at rate N^(-4/5+epsilon) for EVERY FIXED
polynomial weight. The bundle of geometric inputs is chosen before the
weight degree. Covariance uses degree2 and retains the same geometric
properties, with a smaller numerical accuracy. T19.10 remains IN PROGRESS
for its finer intensity assertion and original sharp O(a_N^2) two-edge,
once/all total variation and Wasserstein consequences. Numbered coverage
stays87/167 unconditional and45 conditional, with156 confirmed improvements.

PolynomialWeightedFieldRate separates the generic cutoff argument from
the model. A SINGLE unweighted estimate with margin epsilon/4 and
subpower moments at all fixed orders suffice for all fixed polynomial
weights. No geometric hypothesis is chosen after the degree. The positive
moment bounds are explicit data; no unproved uniform bound is assumed.

PositionalPoissonPolynomialMoments identifies the empty-edge compound
target with the actual independent field and bounds every fixed moment
when the total intensity is bounded. PositionalBackgroundMoments applies
this unconditionally to the true rates p-iota_x, uniformly over every
real private-prime cutoff. PositionalDeletedBackgroundMoments combines
those bounded reference moments with the unconditional subpower original
deleted moments. PositionalOriginalDeletionWeightedUnderInputs then gives
the actual original once-deleted and isolated fields weighted L1 rate4/5.

FiniteMomentComparison controls the SUM of finitely many absolute test
expectation errors by a single weighted coefficient error. Tests are
nonnegative and their SUM is bounded pointwise by the weight. All moment
series, differences and finite/infinite interchanges are absolutely
summable. This avoids any factor equal to the number of coordinates.

PositionalFactorialCovariance defines actual coefficient means,
second factorial moment entries and K_xy=E[X_x X_y]-1_(x=y)E[X_x]
-E[X_x]E[X_y]. The tests are nonnegative for every natural-valued
configuration, including the diagonal, and their full finite matrix sum
is bounded by (1+totalCount)^2. Exact coordinate and mixed Poisson moments
give K_xy=0 on the intended ground.

PositionalCovarianceComparison proves the finite quantitative inequality

 sum_(x,y in G)|K_xy(nu)| <= (1+2*sum_(x in G)p_x+D)*D,
 D=sum_v(1+totalCount(v))^2*|coeff_v(nu)-coeff_v(Poisson(G,p))|.

It proves both first and second moment measure comparisons and the tensor
mean inequality explicitly, including their summability. No matrix entry
is estimated with an accumulating cardinality factor. In the critical
band, choose eta=min(epsilon/4,1/5); the weighted error is eventually at
most1, sum_x(p-iota_x)<=2^C, and a fixed constant is absorbed into the
remaining margin. PositionalOriginalCovarianceUnderInputs proves the
SUM of the absolute covariance entries of BOTH actual original deleted
fields is <=N^(-4/5+epsilon), as printed in T19.10.

The finite comparison, Poisson identities and moment estimates are
unconditional. Transfer to the actual original fields retains exactly
the existing explicit main20.1 retained-component geometric bundle.
No new external input, mathematical correction, axiom, dependency
download, Paper C port or original manuscript edit is introduced.
Palomar remains a later milestone.

The JSON row records the exact verification and proof commit.
