# Many base-field points force irreducible scalar descent with exact degree

Source: main13.4 and the coefficient-field scope of its plane BCN specialization. Actual finite populations and exact total degrees are preserved; the full all-dimensional statement remains open.

ManyPointsScalarDescent.many_points_descent proves that an irreducible plane polynomial over an infinite extension field L with more than degree(P)^2 distinct K-rational zeros is associated to the scalar extension of an irreducible polynomial Q over K. The total degree of Q is exactly degree(P), and every point of the original finite K-population is a zero of Q. The extension K->L need not be finite or algebraic. The infinity hypothesis is automatic in the characteristic-zero application.

components_divide_of_many_points applies the proved finite plane Bezout bound to every scalar component from checkpoint363: if its extension were not divisible by P, the original population would have at most degree(P)^2 points. degree_mul proves exact total-degree additivity for nonzero products through the actual multivariate chart. unit_of_degree_zero identifies every nonzero degree-zero polynomial as a unit. divisor_associated then turns the component degree bound and divisibility into association and exact degree equality. A nonzero component is constructed internally, and irreducibility descends through the field extension.

This is an actual scalar-descent theorem, not a point-count input or a presumed rational equation. It prepares the reduction of the remaining characteristic-zero plane BCN input to its rational geometric subcase. The rational geometric estimate and the general all-dimensional main13.4 remain unproved at this checkpoint.

P1-MATH-0364 adds five theorems. Coverage stays92 proved and72 conditional out of167, with164 completed and three in_progress. The ledger records362 improvements and two statement-scope corrections. No axiom, unproved literature premise, dependency download, compiler change or original manuscript edit is introduced. Palomar remains deferred.
