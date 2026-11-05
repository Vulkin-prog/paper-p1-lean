# Degree-uniform count on each smooth projective residue class

Source: companion T1.4 geometric ingredient and the finite-intersection step of the local determinant method. All original signed primitive pairs are counted.

SmoothClassPointCount.smooth_class_card proves that a finite smooth residue class of signed primitive original projective points has cardinality at most4*(degreeX G+degreeY G)*(H+J), provided G is geometrically irreducible, J<degreeY G, the coordinate bounds are L,Y, and the exact verified determinant inequality holds. The common auxiliary equation is constructed internally by checkpoint349. Its second degree is too small for G to divide it over the rationals.

common_points_card applies the proved finite plane Bezout degree-product bound over the rationals, then retains all signed primitive representatives using the independently proved fibre multiplicity of at most four. degree_rationalize bounds total degree by the sum of the actual two partial degrees, through an injective coefficient map. rationalize_ne_zero ensures the auxiliary remains nonzero. No intersection-count, auxiliary-existence, rank or minor hypothesis is assumed. The resulting local count is independent of coefficient heights and of the number of points in the class.

This closes the per-class count under the literal local smoothness and numerical size conditions. The uniform prime family, residue-class count, second-coordinate height control and final exponent choices remain to be assembled before the global sharp b>=2 Heath-Brown bound is proved.

P1-MATH-0350 adds four theorems. Coverage stays89 proved and75 conditional out of167, with164 completed. The ledger records348 improvements and two statement-scope corrections. No axiom, unproved literature premise, dependency download, compiler change or original manuscript edit is introduced. Main13.4 remains open and Palomar remains deferred.
