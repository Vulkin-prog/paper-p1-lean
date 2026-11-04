# Actual first-degree-one coefficient coprimality, full degree and nonzero resultant certificates

Source: companion T1.4, companion_sections/arithmetic_appendix.tex:139, first-degree-one auxiliary-factor elimination in Step3; T1.5 uses that reduction. Original source hashes remain preserved.

For every ACTUAL integer irreducible factor of first bidegree1 and positive second degree, the literal leading/constant coefficient polynomials now have proved rational coprimality, exact degree control, coefficient-height bounds and TWO nonzero resultant certificates. None of these elimination prerequisites is supplied as a nondegeneracy premise.

LinearBivariateCoefficients defines the exact coefficient polynomials by swapping the actual nested bivariate polynomial and taking coefficients1 and0. It proves a partial-degree bound from all row degrees, the exact maximum-row-degree formula for outer degree at most1, individual coefficient degree bounds and attainment of the full second degree. The literal integer coefficient heights are bounded by the original factor height.

A nonconstant irreducible univariate polynomial over a domain is primitive. For a degree1 polynomial, its two coefficient divisibilities therefore force every common divisor to be a unit. Applying this argument AFTER the proved rational coefficient change gives actual coprimality over Q[T] for the two literal coefficient polynomials. No projective or absolute irreducibility hypothesis is needed in this first-degree-one case.

LinearBivariateResultant combines that actual coprimality, full degree and degree bounds with the proved integer padded-resultant criterion. It proves that the literal padded resultant is nonzero, and the already proved reflected-resultant identity then gives a nonzero certificate for the other dehomogenization as well. The degrees used in both certificates are the ACTUAL second degree of the factor.

P1-MATH-0277 closes the actual coefficient, full-degree and resultant nondegeneracy prerequisites for first-degree-one elimination. The exact projective-row reconstruction, numerical local first-degree-one count and its application to the actual source factor populations, the other geometric local cases and primitive reductions remain open. T1.4 and T1.5 stay in progress. Coverage stays89 proved and72 conditional out of167, with six incomplete numbered results. There are276 improvements and one statement-scope correction. No external input, new axiom, dependency download, compiler change or original manuscript edit is introduced. Palomar remains deferred.
