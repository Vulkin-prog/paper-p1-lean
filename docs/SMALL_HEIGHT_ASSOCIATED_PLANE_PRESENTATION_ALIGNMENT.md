# Constructed bounded-height presentations retain the actual rational association

Source: main13.4 plane normalization. The finite interpolation, many-point Bezout step, exact degree and absolute irreducibility are reused in a stronger internally constructed presentation.

SmallHeightAssociatedPlanePresentation.exists_presentation constructs a bounded-height integer equation Q and now returns its actual rational association with the original equation F, in addition to rational and complex irreducibility, exact total degree, the proved polynomial coefficient-height bound and all original zeros. The association is a proved conclusion of the finite interpolation and many-point Bezout argument, not an additional hypothesis.

grid_eq_of_associated proves that every pair of rationally associated integer equations has exactly the same actual signed integer grid at every radius. The proof maps the association through the actual rational evaluation homomorphism, identifies both original integer evaluations and reflects zero through the injective integer-to-rational cast. Thus the constructed presentation describes the entire original integer curve, including points outside the finite population used to construct it.

The previous SmallHeightGeometricPlanePointInput.exists_small_presentation remains available as a corollary of the stronger construction. Its proof is refactored to reuse the same core argument while dropping the association from the older conclusion. All ordinary unproved BCN interfaces retain their existing scope; the stronger associated presentation introduces no counting input and asserts no BCN bound.

Together with the proved discriminant-sign transport, this supplies the exact missing bridge for removing coefficient-height restrictions from the hyperbolic conic count. That assembly is the next step. The remaining conic branches, full BCN and original main13.4 remain open; no original numbered result is promoted.

P1-MATH-0388 adds three theorems and refactors the earlier presentation proof into a corollary. Coverage stays92 proved and72 conditional out of167, with164 completed and three in_progress. The ledger records386 improvements and two statement-scope corrections. No axiom, unproved literature premise, dependency download, compiler change or original manuscript edit is introduced. Palomar remains deferred.
