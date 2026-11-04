# Bounded primitive integer basis completion and exact nearest-vector geometry

Source: companion T1.4, companion_sections/arithmetic_appendix.tex:139, lattice-coordinate and uniform auxiliary-height steps; T1.5 uses that reduction. Original source hashes remain preserved.

A primitive integer vector can now be completed to an actual integer basis with an explicit polynomial height bound, and the exact two-dimensional nearest-vector geometry is proved. These supply arithmetic and geometric ingredients for the actual short-vector lattice bases; existence of the shortest vector and full lattice assembly remain separate work.

PrimitiveBinaryBasis first bounds Bezout coefficients. For coprime integers p,q with |p|,|q|<=H, the original Bezout solution is reduced modulo p, with the p=0 axis case treated separately. The constructed r,s satisfy p*r+q*s=1 and |r|,|s|<=H^2+1. The actual integer matrix with columns (p,q),(-s,r) has the explicit integer inverse with rows (r,s),(-q,p). Both matrix products are proved to be the identity, and EVERY entry of the basis and inverse is bounded by H^2+H+1. The resulting existence theorem begins with any actual primitive integer pair and returns both bounded inverse matrices with that vector as the first column.

BinaryEuclideanReduction defines the squared Euclidean length, scalar product and oriented area directly in two real coordinates. It proves positivity for nonzero vectors and the exact Gram identity. Subtracting the nearest integer multiple of the first vector from the second preserves area and makes the absolute scalar product at most half the first squared length. Whenever the first vector is no longer than the reduced second vector, the proved area bound is

  3*|v|^2*|w_reduced|^2 <= 4*area(v,w)^2.

The nearest-integer projection step is constructed explicitly; no reduced-basis theorem is supplied as an external input. The length-order premise in this geometric lemma still has to be discharged using an actual shortest nonzero lattice vector.

P1-MATH-0251 records an explicit polynomial-height primitive basis completion and the exact constants in the nearest-vector calculation. Remaining work includes existence and primitivity of the shortest vector, the full reduced basis and coordinate boxes for the actual lattices, geometric curve counts and interval sums. T1.4 and T1.5 stay in progress. Coverage stays89 proved and72 conditional out of167, with six incomplete numbered results. There are250 improvements and one statement-scope correction. No external input, new axiom, dependency download, compiler change or original manuscript edit is introduced. Palomar remains deferred.
