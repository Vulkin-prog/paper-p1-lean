# Actual two-pair coordinate equations with common polynomial height and exact populations

Source: companion T1.4, companion_sections/arithmetic_appendix.tex:139, lattice-coordinate and uniform auxiliary-height steps; T1.5 uses that reduction. Original source hashes remain preserved.

Simultaneous integral coordinate changes on both projective pairs now produce actual nonzero integer biforms, with exact point transport and a common polynomial coefficient-height exponent chosen before all moving matrices and populations.

BiformLinearCoordinates proves that exchanging the coefficient families twice is exactly the identity for homogeneous rows. Exchanging the pairs preserves coefficient height. Combining the exchange with the proved binary substitutions constructs the actual transformed family. Its evaluation is exactly the original equation evaluated at (A*x,B*y). Actual inverse integer matrices prove that a nonzero family remains nonzero. Both homogeneous degrees are preserved, including degree-zero cases.

BiformCoordinateEquation recovers the finite integer coefficient array from every transformed family, reuses the existing row reconstruction and builds its actual nested homogeneous polynomial. This equation is nonzero for inverse matrix pairs, has outer degree a and inner homogeneous row degree b, and its evaluation equals the original equation after the two matrix changes. Every actual integer coefficient is bounded by

  (b+1)*(a+1)*H*(2*M)^a*(2*T)^b,

where H bounds the source coefficients and M,T bound the two matrices. This is a proved finite coefficient estimate, not a supplied height hypothesis.

BiformCoordinateHeight chooses the common exponent and threshold BEFORE N, both degrees, either matrix and the source family. If a<=Amax, b<=Bmax, source height<=N^kappa and matrix heights<=N^mu,N^nu, the actual transformed equation has height at most N^kappa', with

  kappa' = kappa+(mu+1)*Amax+(nu+1)*Bmax+2.

BiformPointCoordinates constructs the actual map of integer point pairs. Integer inverse matrices give reconstruction, injectivity and exact finite-population cardinality. Primitivity is preserved on both pairs, coordinate growth is explicitly bounded, and every original zero becomes an actual zero of the transformed equation in inverse coordinates. No sign or nonzero-denominator assumption is silently added; affine chart selection still has to handle zeros in transformed coordinates.

P1-MATH-0248 records the full two-pair algebraic and height transport. Actual short-vector bases, projective chart/factor assembly in those coordinates, geometric curve counts and interval sums remain to be established. T1.4 and T1.5 stay in progress. Coverage stays89 proved and72 conditional out of167, with six incomplete numbered results. There are247 improvements and one statement-scope correction. No external input, new axiom, dependency download, compiler change or original manuscript edit is introduced. Palomar remains deferred.
