# Primitive homogeneous root divisibility and actual second-pair height

Source: companion T1.4 geometric ingredient and the homogeneous rational-root height step in the local determinant method. Signed primitive pairs and the unrestricted original second pair are preserved.

PrimitiveHomogeneousRootBound.endpoint_divisibility proves the exact homogeneous rational-root divisibilities: for a primitive signed pair(u,v) with P.homogenize(d)(u,v)=0, u divides P.coeff0 and v divides P.coeff d. The proof works for arbitrary d and uses actual coefficient maps to ZMod of the coordinate absolute values; coprimality makes the other coordinate a unit. It includes zero and negative coordinates and does not assume either coordinate positive. coordinate_natAbs_bounds derives the exact coordinate bounds when both endpoint coefficients are nonzero.

evaluation_bound proves |P.homogenize(d)(x)|<=(d+1)*A*L^d from the literal coefficient bound A and absolute coordinate box L. fibre_coordinate_bounds applies the exact divisibilities to the chart of the original projective fibre of G. fibre_height_bound consequently proves |y_i|<=(degreeX G+1)*height(G)*L^(degreeX G) for both original second coordinates whenever the two endpoint evaluations on x are nonzero. No imposed second-coordinate box or rational-root bound is assumed. eval_homogenize_other_axis supplies the complementary exact constant-coefficient axis identity.

The endpoint nonvanishing conditions are retained explicitly. The finite exceptional fibres on which either endpoint vanishes still need to be bounded and separated in the global argument. Prime selection, the finite-field class budget and final exponent choices also remain open.

P1-MATH-0351 adds six theorems. Coverage stays89 proved and75 conditional out of167, with164 completed. The ledger records349 improvements and two statement-scope corrections. No axiom, unproved literature premise, dependency download, compiler change or original manuscript edit is introduced. The global sharp b>=2 input and main13.4 remain open; Palomar remains deferred.
