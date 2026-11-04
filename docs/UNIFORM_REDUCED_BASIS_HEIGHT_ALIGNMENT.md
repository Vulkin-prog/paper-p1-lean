# Actual reduced lattice bases with one uniform polynomial coefficient-height exponent

Source: companion T1.4, companion_sections/arithmetic_appendix.tex:139, lattice-coordinate and uniform auxiliary-height steps; T1.5 uses that reduction. Original source hashes remain preserved.

The actual reduced lattice basis and its actual integer inverse now have a proved common polynomial coefficient height. The exponent is chosen BEFORE N and the moving real lattice matrix, while all shortest-vector, inverse, projection and area properties remain available.

BinaryLatticeEntryBounds derives every needed length bound from actual matrix entries. If T and an actual real left inverse S have entries bounded by J, then the maximum inverse row squared norm and the comparison vector squared length are at most 2*J^2. Every actual global shortest integer vector has coordinates bounded by H=4*J^4+1. Any integer vector of height H0 has image squared length at most 8*J^2*H0^2.

BoundedReducedBinaryBasis uses the BOUNDED Bezout completion of that actual primitive shortest vector, then applies the actual nearest-integer shear. It constructs both inverse integer matrices and retains determinant one, the globally shortest first vector, positive ordered squared lengths, the half-projection bound and the squared area estimate. The basis and inverse entry heights are bounded by the explicit integer polynomial

  H = 4*J^4+1,
  H0 = H^2+H+1,
  R = 2*J^2*(2*J^2+8*J^2*H0^2)+1,
  height(A),height(B) <= 2*H0*(R+1).

The projection coefficient bound is derived from the actual lattice lengths; it is not supplied as a premise.

ReducedBasisPolynomialBound proves the explicit polynomial is at most J^60 for J>=2. UniformReducedBinaryBasis.uniform_reduced_basis therefore chooses kappa=60*(mu+1) and N0=2 BEFORE N,T,S. If every entry of T and S is at most N^mu in absolute value and S*T=1, the theorem constructs actual inverse unimodular integer matrices whose EVERY entry is bounded by N^kappa, with all the proved reduced-basis geometry. Choosing J=N^(mu+1) also covers mu=0 without a special-case hypothesis. The exponent is deliberately coarse; only a fixed common polynomial bound is needed in the later height budget.

P1-MATH-0255 closes uniform polynomial coefficient-height control of the actual reduced basis AND inverse. The remaining lattice work concerns exact coordinate boxes and their source-scale specialization; geometric curve counts and final interval sums also remain. T1.4 and T1.5 stay in progress. Coverage stays89 proved and72 conditional out of167, with six incomplete numbered results. There are254 improvements and one statement-scope correction. No external input, new axiom, dependency download, compiler change or original manuscript edit is introduced. Palomar remains deferred.
