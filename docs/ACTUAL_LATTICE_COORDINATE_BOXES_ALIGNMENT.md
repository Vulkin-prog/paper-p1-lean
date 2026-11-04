# Actual lattice coordinate boxes with ordered sides and determinant-controlled area

Source: companion T1.4, companion_sections/arithmetic_appendix.tex:139, lattice-coordinate and uniform auxiliary-height steps; T1.5 uses that reduction. Original source hashes remain preserved.

The actual inverse integer coordinates now lie in explicit reduced lattice boxes. Their sides are ordered, their product is controlled by the reciprocal lattice determinant, and both their upper and lower scales are proved. These properties are assembled with the actual polynomial-height integer bases.

BinaryLatticeCoordinateBounds proves the two-coordinate Cramer identities and combines them with the Gram identity and the reduced-basis area estimate. For x=c*v+d*w it derives

  3*c^2*|v|^2 <= 4*|x|^2,
  3*d^2*|w|^2 <= 4*|x|^2.

If both real coordinates of x have absolute value at most R, with R>=0, the actual coefficients satisfy |c|<=L0 and |d|<=L1, where

  L0 = 2*R/sqrt(|v|^2), L1 = 2*R/sqrt(|w|^2).

The proof derives L1<=L0, L0*L1<=4*R^2/|area(v,w)| and R^2<=L0^2*|area(v,w)|. Inverse-matrix integer coercivity also yields L0<=2*R*(inverseSize(S)+1).

ReducedLatticeCoordinateBoxes proves the exact expansion of T*z in the ACTUAL integer inverse coordinates B*z. Therefore the coefficient bounds apply to every original integer vector whose actual lattice image lies in the real box. The determinant-one integer basis identifies its oriented area with det(T). A primitive coordinate pair in such an ordered box also forces L0>=1; this is proved without dropping either axis case.

UniformLatticeCoordinateBoxes.uniform_coordinate_boxes chooses the common integer matrix-height exponent and threshold BEFORE N,T,S,R. It returns actual inverse integer matrices A,B, determinant one, the globally shortest first vector, the explicit equalities defining L0,L1, their nonnegativity/order, determinant product bound, lower-scale bound and polynomial upper bound. EVERY integer vector with |(T*z)_i|<=R has its actual inverse coordinates bounded by L0,L1. No coordinate box or short-basis premise is supplied; the required bases are constructed internally from the real matrix and its actual left inverse.

P1-MATH-0256 closes the general actual reduced lattice coordinate boxes, retaining the exact side formulas needed for the shortest-vector interval count. Remaining work includes specializing the real lattice matrices and interval populations to the source scales, the geometric curve counts and final interval sums. T1.4 and T1.5 stay in progress. Coverage stays89 proved and72 conditional out of167, with six incomplete numbered results. There are255 improvements and one statement-scope correction. No external input, new axiom, dependency download, compiler change or original manuscript edit is introduced. Palomar remains deferred.
