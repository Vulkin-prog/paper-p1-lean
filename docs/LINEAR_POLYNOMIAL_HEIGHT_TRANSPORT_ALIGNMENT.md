# Finite coefficient-height budget for every fixed integer-linear transformation

Source: main13.4 and coordinate normalization in its geometric plane specialization. Actual total-degree bases and literal integer coefficient heights are retained.

LinearPolynomialHeightTransport.linear_height proves that every fixed integer-linear transformation T of nested integer polynomials satisfies height(T(P))<=height(P)*budget(D,T) whenever the actual total degree of P is at most D. The explicit finite budget is the sum of the actual heights of the transformed triangular basis monomials. It depends only on D and T, not on P or its coefficients.

height_smul and height_sum prove the literal integer scalar and finite sum height inequalities. expansion gives exact scalar expansion in the triangular degree-D basis. finite_family_height bounds every transformation in an arbitrary actual finite family using one finite maximum of these budgets. No continuity, bounded-operator or coefficient-control premise is assumed.

These checked finite coefficient budgets prepare bounded integer coordinate changes in the remaining geometric plane argument. They do not prove the still-open controlled-height geometric BCN count or the full original all-dimensional main13.4 statement.

P1-MATH-0370 adds five theorems and two actual basis/budget definitions. Coverage stays92 proved and72 conditional out of167, with164 completed and three in_progress. The ledger records368 improvements and two statement-scope corrections. No axiom, unproved literature premise, dependency download, compiler change or original manuscript edit is introduced. Palomar remains deferred.
