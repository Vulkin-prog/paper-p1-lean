# Actual short-vector residuals and complete primitive axis interval sums

Source: companion T1.4, companion_sections/arithmetic_appendix.tex:139, lattice-coordinate and uniform auxiliary-height steps; T1.5 uses that reduction. Original source hashes remain preserved.

The actual first-lattice vector now satisfies the coordinate and integer-product residual estimates used in the interval count, and both primitive axis contributions have a complete finite sum bound. No axis case is discarded.

RelativeIntervalShortVectors proves that each real coordinate is bounded by the Euclidean length, then uses the ACTUAL inverse source-lattice matrix. For any nonzero integer vector z and its actual side L=4/|T*z|, it proves

  |z0| <= 12*D/L,
  |z1| <= 4*E/L,
  |z1*k-(M*E/D)*z0| <= 4*E/L.

The last identity comes from an exact equality with -E times the first actual lattice-image coordinate. These bounds hold for the actual shortest vector in the constructed basis, and more generally for every nonzero integer vector with its corresponding side length. No short-vector coordinate or residual bound is supplied as an input.

PrimitiveBinaryColumns derives a Bezout identity from the actual inverse integer matrix, proving EVERY basis column primitive. On either axis, primitivity proves that the nonzero coordinate has absolute value exactly one.

RelativeIntervalAxisBounds applies the actual residual. When z0=0 and k>=M/4 it proves M*L<=16*E. When z1=0 it proves M*L<=4*D. The exact finite cardinality of the interval index set then gives, for ANY actual primitive vector choice on the selected intervals,

  sum_(z0=0) L <= 32*E,
  sum_(z1=0) L <= 8*D.

The theorem treats both signs of the primitive axis vectors and arbitrary finite interval subsets. These are the complete finite side-length costs behind the additional D+E terms; the later local curve-count factor remains separate.

P1-MATH-0258 closes the actual short-vector coordinate/residual estimates and primitive axis interval sums. The remaining first-lattice interval work concerns the two-nonzero-coordinate divisor count and its dyadic sum. The second lattice/regridding, geometric curve counts and relevant primitive reductions also remain. T1.4 and T1.5 stay in progress. Coverage stays89 proved and72 conditional out of167, with six incomplete numbered results. There are257 improvements and one statement-scope correction. No external input, new axiom, dependency download, compiler change or original manuscript edit is introduced. Palomar remains deferred.
