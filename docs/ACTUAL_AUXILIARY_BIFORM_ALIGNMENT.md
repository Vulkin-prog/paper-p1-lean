# Actual bounded auxiliary polynomial and bihomogeneous projective equation

Source: companion T1.4, companion_sections/arithmetic_appendix.tex:139, Step2 auxiliary extraction and its coefficient-height/parameter-order ledger; T1.5 uses that extraction. Original source hashes remain preserved.

The bounded common coefficient extraction is now realized as an actual nonzero integer auxiliary polynomial and an actual bihomogeneous equation on the original projective pairs. The analytic normalized small-minor premise is still explicit and unproved.

DeterminantAuxiliaryPolynomial constructs F in Z[X][X] from the extracted coefficient rectangle. Coefficient recovery proves F is nonzero. Its two partial degrees are bounded by the selected A and B, its actual coefficient height is at most N^kappa, and F(d/e,v/u)=0 for every member of the original finite source family. The degree choices and height exponent precede N and the entire source family.

DeterminantAuxiliaryBiform performs both homogenizations explicitly. Its coefficient forms have degree B in (v,u), and its outer form has degree A in (d,e). Dehomogenization recovers the actual rectangle coefficients; nonvanishing is proved by coefficient recovery. Every integer coefficient of the resulting nested multivariate polynomial has absolute value at most the original coefficient bound, hence at most N^kappa. Homogenization therefore costs no additional coefficient-height exponent.

The evaluation on the original integer quadruple equals the exact integer monomial row pairing. Its rational image equals e^A*u^B times the corresponding rational row pairing. The same actual nonzero biform consequently vanishes on every original source quadruple, with no coprimality assumption needed for this algebraic step. A uniform existence theorem bundles nonvanishing, both homogeneities, all coefficient bounds and all point equations after the explicit normalized determinant smallness hypothesis.

P1-MATH-0237 closes the conversion from bounded common coefficients to the actual projective auxiliary equation. It does not establish the required analytic small-minor estimate, irreducible-factor curve count or short-vector summation. T1.4 and T1.5 therefore remain in progress. Coverage stays89 proved and72 conditional out of167, with six incomplete numbered results. There are236 improvements and one statement-scope correction. No external input, axiom, Paper C port, dependency download, compiler change or original manuscript edit is introduced. Palomar remains deferred.
