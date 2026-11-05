# Explicit logarithmic and obstruction budgets for growing degrees

Source: main13.4 quantitative plane preparation, using the exact obstruction expression of PolynomialPrimeAffineCount and the bounded post-shear presentation. Original source bytes are preserved.

DegreeUniformAffineParameters proves concrete parameters for the forthcoming weaker degree-uniform affine bound. For 2<=D<=N, the sheared box height (D+1)*N is at most N^3. If an equation has first partial degree at most D, second partial degree D and height at most N^(32*D^3), its entire denominator-and-derivative obstruction bound is at most N^(64*D^3). Both natural-number and real-valued versions are checked, including every coefficient and box-height factor.

With L=Nat.log2(N)+1, the actual binary inequality N<2^L and log N<=L are proved. The avoidance count m=64*D^3*L+1 makes N^(64*D^3)<P^m for every P>=2, and satisfies m<=128*D^3*L. The chosen auxiliary degree A=3*L+1 is positive, satisfies log((D+1)*N)<=A+1 and has A+(D-1)<=4*D*L. The logarithmic comparison needed by the absolute determinant scale is therefore internally supplied.

The obstruction estimate is a bound for the complete expression used in PolynomialPrimeAffineCount.uniform_bound, rather than a property assumed for the actual point population. It combines with the actual post-shear interpolation presentation from checkpoint405. No prime supply, derivative avoidance or height normalization remains hidden in these parameter lemmas. A chosen prime scale and the final global estimate are still required.

This is preparatory work toward a weaker polynomial dependence on D. It does not prove the D^2 logarithmic BCN bound, the original full growing-degree corollary or the sharp half-window rank consequence. P1-MATH-0406 adds one module, eight theorems and three definitions. Coverage stays93 proved and71 conditional out of167, with164 completed and three in_progress. The ledger records404 improvements and two statement-scope corrections. No new axiom, dependency download, compiler change or original manuscript edit is introduced. Palomar remains deferred.
