# Explicit nearest-integer coefficient and reduced matrix height bounds

Source: companion T1.4, companion_sections/arithmetic_appendix.tex:139, lattice-coordinate and uniform auxiliary-height steps; T1.5 uses that reduction. Original source hashes remain preserved.

The nearest-integer step in the actual reduced basis now has an explicit coefficient bound, and its effect on BOTH integer basis matrices is controlled. This removes the unquantified nearest-integer coefficient from the forthcoming polynomial-height assembly.

BinaryReductionBounds proves the elementary scalar-product inequality |<v,w>|<=(|v|^2+|w|^2)/2. Integer nonzero vectors and the proved inverse-matrix coercivity give the complementary lower bound

  1 <= K*|T*z|^2,

where K is the maximum squared row norm of an actual real inverse matrix. The rounded projection integer k then satisfies the proved bound

  |k| <= K*(|v|^2+|w|^2)+1.

The argument uses the actual nearest integer and does not assume a bound for it. The lattice specialization applies to every nonzero integer first vector, independently of minimality.

BinaryMatrixProductHeight proves the explicit entry-height bound 2*H*K for products of binary integer matrices. The actual integer shear and its inverse have entry height at most K+1 when |k|<=K. Consequently, if the unreduced integer basis and its inverse both have entry height H, the actual reduced basis AND its actual inverse have entry height at most

  2*H*(K+1).

The final theorem applies this bound directly to the actual reduced matrices defined in P1-MATH-0253. Together with the bounded primitive completion and the inverse-matrix length estimates, these formulas provide all elementary pieces for a common polynomial-height budget.

P1-MATH-0254 closes the quantitative nearest-integer and matrix-product calculations. Assembly of a common power of N for the constructed bases, the exact coordinate boxes and their source-scale specialization remains to be completed, followed by geometric curve counts and interval sums. T1.4 and T1.5 stay in progress. Coverage stays89 proved and72 conditional out of167, with six incomplete numbered results. There are253 improvements and one statement-scope correction. No external input, new axiom, dependency download, compiler change or original manuscript edit is introduced. Palomar remains deferred.
