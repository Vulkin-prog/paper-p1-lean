# Common integer auxiliary equation on an entire finite smooth class

Source: companion T1.4 geometric ingredient and the common auxiliary equation step of the local determinant method. Original signed projective points and actual coordinate degrees are retained.

SmoothClassAuxiliary.exists_auxiliary constructs a nonzero integer polynomial F with degreeX F<=H and degreeY F<=J that vanishes at every point of an arbitrary finite smooth residue class, both in the affine rational chart and in the actual original projective evaluation. All signed coordinates and all points of the finite family are retained. The literal class data consist only of the original curve equation, the two denominator conditions and the two residue congruences.

minor_vanishing proves every rectangular-basis square minor vanishes from the independently established p-adic divisor and archimedean bound. The monomial matrix is explicitly transposed before passing to the common finite row kernel over the rationals. exists_coefficients applies the checked integer annihilator theorem to the full family, including when its cardinality exceeds the number of monomials. Its finite coefficient bound is chosen internally; no minor, rank, auxiliary-existence or point-count hypothesis is assumed. The coefficient vector is nonzero, so the rectangle polynomial is nonzero by exact coefficient recovery.

The numerical hypothesis is exactly k!*(L^H*Y^J)^k<p^(k*(k-1)/2), k=(H+1)*(J+1). Deriving this inequality from the final prime scale and choosing H,J remains open, as does the global sharp b>=2 count. This is a proved local auxiliary construction, not a completed numbered counting theorem.

P1-MATH-0349 adds three theorems, a literal point-data structure and a monomial-entry definition. Coverage stays89 proved and75 conditional out of167, with164 completed. The ledger records347 improvements and two statement-scope corrections. No new axiom, unproved literature premise, dependency download, compiler change or original manuscript edit is introduced. Main13.4 remains open and Palomar remains deferred.
