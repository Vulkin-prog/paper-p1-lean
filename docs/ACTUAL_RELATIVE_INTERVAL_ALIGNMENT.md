# Exact finite source interval partition and coefficient-uniform center scales

Source: companion T1.4, companion_sections/arithmetic_appendix.tex:139, Step2 auxiliary extraction and its coefficient-height/parameter-order ledger; T1.5 uses that extraction. Original source hashes remain preserved.

The relative intervals in the determinant argument are now constructed and counted on every actual source point, with explicit center comparisons independent of the moving coefficients. The normalized weight-product margin from the prescribed M and polylogarithmic shift still needs to be established.

DeterminantRelativeIntervals assigns k=floor(M*(d/e)/(D/E)) to every D<=d<=2D and E<=e<=2E, for positive D,E and integer M>=4. It proves M/4<=k<=2M, so k belongs to the fixed set 1..2M. The actual center is s0=(D/E)*k/M. Exact bounds D/(4E)<=s0<=2D/E and 0<=alpha<=4/M follow from the floor inequalities. The index set has exactly 2M elements.

DeterminantIntervalPartition filters the original finite quadruple population by this actual index. Its cardinality equals the sum of the cluster cardinalities over all 2M centers, with no omitted points and no overlap overcount. Every occupied cluster inherits the same center and alpha bounds. For positive coefficients and source value c1*d^2*u>=rho*N, the actual vertical error is at most 4*|h|/(rho*N). The proof uses only M>=4 and contains no additional coefficient-ratio factor.

DeterminantCenterScales compares the actual quadratic center t0=(c1/c2)*s0^2 to V/U. If both source-box monomials c1*D^2*U and c2*E^2*V lie in [rho*N,C*N], it proves

  (rho/(16*C))*(V/U) <= t0 <= (4*C/rho)*(V/U).

The moving coefficient ratio cancels into the ratio of these two bounded source monomials. Only the fixed source comparison constants remain.

DeterminantEffectiveHeights proves DE<=(2E)^2*s0<=8DE, the analogous product bounds after a fixed enlargement of the U denominator bound, and exact one-sided logarithmic comparison inequalities. These are the finite ingredients for comparing the local effective logarithmic sizes with log(DE) and log(UV), with explicit errors log(K)/log(N).

P1-MATH-0242 closes the actual finite relative interval partition, pointwise relative-error bounds and coefficient-uniform center comparison. Completing the normalized weight/product margin from the actual rounded horizontal scale and polylogarithmic shift, then the factor-curve counts and short-vector summations, remains open. T1.4 and T1.5 stay in progress; coverage stays89 proved and72 conditional out of167, with six incomplete numbered results. There are241 improvements and one statement-scope correction. No external input, axiom, Paper C port, dependency download, compiler change or original manuscript edit is introduced. Palomar remains deferred.
