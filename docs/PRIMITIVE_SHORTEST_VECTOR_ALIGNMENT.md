# Actual primitive shortest vectors from finite lattice sublevels

Source: companion T1.4, companion_sections/arithmetic_appendix.tex:139, lattice-coordinate and uniform auxiliary-height steps; T1.5 uses that reduction. Original source hashes remain preserved.

Every invertible real image of the integer plane now has an actual globally shortest nonzero vector, and that integer vector is proved primitive. The construction also gives an explicit coordinate bound from the inverse matrix; no shortest-vector existence premise remains in this result.

BinaryLatticeMinimum defines the actual real matrix image of an integer vector. An actual real left inverse proves that nonzero integer vectors have positive squared image length. The two-coordinate Gram identity gives a coercive bound on each integer coordinate: its square is at most the inverse row squared norm times the image squared length. With K equal to the maximum inverse row squared norm, every vector of squared image length at most C lies in the finite integer coordinate box

  |z_i| <= ceil(K*C+1).

The finite box is constructed explicitly. A minimum is selected among its nonzero vectors, using the image length of (1,0) as a comparison level. Every nonzero integer vector outside that level is longer than the comparison vector, so the selected vector is globally shortest, not just minimal in the finite box.

PrimitiveShortestVector proves the exact image and squared-length scaling under any integer multiple. Dividing an actual shortest vector by the gcd of its coordinates produces a nonzero primitive vector. Global minimality and strict positivity force this gcd to equal one. The resulting existence theorem returns an actual primitive nonzero global minimizer together with the explicit coordinate bound

  |z_i| <= ceil(K*|T*(1,0)|^2+1).

P1-MATH-0252 discharges existence and primitivity of the shortest vector required by the nearest-vector basis construction. The bounded Bezout completion and nearest-integer geometry from P1-MATH-0251 can now be applied to that actual vector. Remaining work includes assembling the reduced basis and explicit coordinate boxes for the two source lattices, geometric curve counts and final interval sums. T1.4 and T1.5 stay in progress. Coverage stays89 proved and72 conditional out of167, with six incomplete numbered results. There are251 improvements and one statement-scope correction. No external input, new axiom, dependency download, compiler change or original manuscript edit is introduced. Palomar remains deferred.
