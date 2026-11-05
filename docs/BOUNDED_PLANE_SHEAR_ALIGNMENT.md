# A bounded integer direction attains the full outer degree

Source: main13.4 plane preparation, exact triangular coefficient coordinates, integer shears and the internally available finite polynomial root bound. The parameter is bounded solely by the actual total degree.

BoundedPlaneShear.exists_full_outer_degree proves that every nonzero integer plane equation P admits an actual integer shear parameter0<=t<=D, where D is its exact total degree, such that P(x+t*y,y) has outer degree exactly D. The parameter lies in a fixed finite set depending only on D; no coefficient-dependent coordinate magnitude is introduced.

The proof constructs the literal top-direction polynomial from triangular coefficient coordinates. direction_coefficient identifies each top-degree coefficient without cancellation, direction_degree bounds its univariate degree by D, and direction_ne_zero extracts a genuine coefficient attaining the original finite-support total degree. The proved finite root bound then supplies a nonroot among0,...,D. The diagonal specialization of the actual integer shear is computed on every monomial and reconstructed on the whole equation, identifying its coefficient of degree D with evaluation of that top-direction polynomial. This nonzero coefficient forces the exact outer degree; total-degree preservation supplies the reverse inequality.

All finite-direction selection, coefficient identities and degree preservation are now internally proved. Together with the preceding integer coordinate and height budgets, they prepare an improvement of the unconditional intermediate plane exponent from4/D+epsilon to2/D+epsilon. That stronger count is not yet asserted at this checkpoint; the sharper degree-uniform BCN exponent1/D and original all-dimensional main13.4 remain open.

P1-MATH-0376 adds eight theorems and two definitions. Coverage stays92 proved and72 conditional out of167, with164 completed and three in_progress. The ledger records374 improvements and two statement-scope corrections. No axiom, unproved literature premise, dependency download, compiler change or original manuscript edit is introduced. Palomar remains deferred.
