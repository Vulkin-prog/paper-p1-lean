# Exact integral binary coordinate changes, primitive points and explicit coefficient heights

Source: companion T1.4, companion_sections/arithmetic_appendix.tex:139, lattice-coordinate and uniform auxiliary-height steps; T1.5 uses that reduction. Original source hashes remain preserved.

Integral binary coordinate changes now have a fully proved polynomial substitution, exact evaluation identity, primitive-point transport and explicit coefficient-height bound. These are prerequisites for moving the actual auxiliary curves into lattice coordinates; no short lattice basis or local curve-count theorem is assumed or claimed.

BinaryLinearSubstitution constructs the algebra homomorphism induced by an actual 2 by 2 matrix. Substitution composition is proved with the correct reversed matrix order. Actual inverse integer matrices give an algebra equivalence, so nonzero equations remain nonzero. Every homogeneous degree is preserved, and evaluation of the transformed equation at z equals evaluation of the original equation at the actual vector A*z.

UnimodularBinaryCoordinates proves reconstruction, injectivity and exact finite-population cardinality under an integer left inverse. An explicit Bezout calculation transports coprimality of the two coordinates, hence primitivity of integer pairs in both directions. Primitive pairs are nonzero. If matrix entries have absolute value at most H and source coordinates at most L, each transformed coordinate is bounded by 2*H*L.

BinarySubstitutionHeight proves the stronger linear-factor height estimate without a degree loss at each multiplication. For a degree-d homogeneous integer binary form F of coefficient height at most H and a matrix with entries of absolute value at most M, EVERY coefficient of the actual substituted form is bounded by

  (d+1)*H*(2*M)^d.

The proof derives the actual affine-chart expansion, bounds products of arbitrary powers of two linear forms, and recovers all homogeneous coefficients from the chart. No coefficient-height estimate is supplied as an unproved input.

P1-MATH-0247 records the precise direction of the coordinate/substitution identities and the explicit degree-dependent height factor. Simultaneous transport of both projective pairs, actual short-vector lattice bases, the geometric curve cases and the final interval counts remain to be proved. T1.4 and T1.5 stay in progress. Coverage stays89 proved and72 conditional out of167, with six incomplete numbered results. There are246 improvements and one statement-scope correction. No external input, new axiom, dependency download, compiler change or original manuscript edit is introduced. Palomar remains deferred.
