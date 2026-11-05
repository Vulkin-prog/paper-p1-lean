# Scalar components preserve actual base-field points and total degree

Source: main13.4 and the coefficient-field scope of its plane BCN specialization. The reduction is preparatory and does not replace the full original all-dimensional statement.

ScalarComponentPoints.component_evaluation proves that applying any base-field linear coefficient functional to a bivariate polynomial commutes exactly with evaluation at base-field coordinates. components_vanish consequently proves that every actual base-field zero remains a zero of every scalar coefficient component. This works over every field extension K->L and does not assume algebraicity or finite extension degree.

component_degree proves the component total degree cannot exceed the original total degree, including possible coefficient annihilation. exists_nonzero_component constructs a linear functional yielding a nonzero component of every nonzero original polynomial, using the already checked finite basis reconstruction even for infinite extensions. project_monomial, project_evaluation and component_monomial supply the exact elementary projection identities. No point-count, scalar-descent or geometric-bound hypothesis is assumed.

These are preparatory tools for reducing the remaining plane BCN estimate from arbitrary coefficient fields to rational coefficients: sufficiently many base-field points should force a scalar descent via the proved finite plane Bezout theorem. That descent and the rational geometric BCN estimate are not yet proved by this checkpoint. The general all-dimensional main13.4 statement remains in_progress.

P1-MATH-0363 adds seven theorems. Coverage stays92 proved and72 conditional out of167, with164 completed and three in_progress. The ledger records361 improvements and two statement-scope corrections. No axiom, unproved literature premise, dependency download, compiler change or original manuscript edit is introduced. Palomar remains deferred.
