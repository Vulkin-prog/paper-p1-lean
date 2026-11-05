# Unconditional fixed-degree plane counts over arbitrary characteristic-zero fields

Source: main13.4 plane preparation, the internally proved intermediate integer count, denominator clearing, non-geometric point bounds and many-point rational descent. This exponent4/D+epsilon is weaker than the original BCN target.

CoarseFieldPlaneCount.field_count proves the unconditional signed integer-grid estimate K(D,epsilon)*H^(4/D+epsilon) for every irreducible plane equation of exact fixed degree D>=2 over every characteristic-zero field F. The constant is chosen before F, its field instances, the equation and H>2. Neither absolute irreducibility nor an embedding of F into the complex numbers is assumed.

rational_geometric_count first clears denominators, retaining the exact degree, geometric irreducibility and every actual integer grid, and applies the proved coefficient-uniform integer theorem. rational_count handles all other irreducible rational equations by the internally proved non-geometric bound D*(D-1). For arbitrary F, a population of at most D^2 is absorbed directly; every larger population forces a rational equation of the same degree by the proved many-point scalar descent. Its actual integer zeros contain the original population, and rational_count applies without any need to transfer complex irreducibility from F.

bounded_degree_count gives one constant for every degree in any fixed finite interval2<=D<=M, while retaining the exact exponent4/D+epsilon. The choice precedes the field, equation, degree and height. This finite-range uniformity makes no claim on the growth of its constant as M increases.

P1-MATH-0374 adds four theorems. This intermediate estimate remains weaker than the degree-uniform BCN exponent1/D. Main13.4 remains in_progress; coverage stays92 proved and72 conditional out of167, with164 completed and three in_progress. The ledger records372 improvements and two statement-scope corrections. No axiom, unproved literature premise, dependency download, compiler change or original manuscript edit is introduced. Palomar remains deferred.
