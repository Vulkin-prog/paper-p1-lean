# Actual finite-field smooth-class budget with coefficient drops

Source: companion T1.4 geometric ingredient and the finite-field class-count step in the local determinant method. Reduction uses the actual integer equation and its actual derivative.

FiniteFieldPlaneZeroBound.smooth_integer_classes_card proves that every finite set of affine residue pairs over ZMod p satisfying the actual original integer equation and a nonzero actual second derivative evaluation has cardinality at most(degreeX G+degreeY G)*p. Coefficient reduction may lower either degree or even annihilate the whole equation. In the latter case its derivative also vanishes, so the smooth-class population is empty. No good-reduction or preserved-degree premise is imposed.

multivariate_card derives the finite-field two-variable zero bound from the proved Mathlib Schwartz-Zippel theorem, with exact rational nonnegative arithmetic and cardinality conversion. plane_card transports it through the checked bivariate total-degree chart, retaining the correct coordinate order. coefficient_map_degree_le proves total degree cannot increase under any coefficient ring map, including noninjective reduction modulo p. These combine with the original actual partial-degree sum.

This closes the finite-field class-count budget required by the local determinant method. The actual map from projective points to these smooth classes, the denominator-and-derivative prime avoidance cover, and final numerical scale choices remain to be assembled.

P1-MATH-0354 adds four theorems. Coverage stays89 proved and75 conditional out of167, with164 completed. The ledger records352 improvements and two statement-scope corrections. All dependencies were already available locally. No axiom, unproved literature premise, compiler change or original manuscript edit is introduced. The global sharp b>=2 input and main13.4 remain open; Palomar remains deferred.
