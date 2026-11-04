# Boundedly many actual integer factor curves with common projective height

Source: companion T1.4, companion_sections/arithmetic_appendix.tex:139, Step2 auxiliary extraction and its coefficient-height/parameter-order ledger; T1.5 uses that extraction. Original source hashes remain preserved.

Every occupied signed source interval is now reduced to boundedly many actual nonconstant integer factor curves, with one common polynomial coefficient-height exponent. This uses the existing proved bivariate factor-height theorem and does not assume absolute irreducibility or a curve-count estimate.

IntegerBivariateFactorCover extends the finite factor-cover argument directly over the integers. The sum of the two partial degrees is additive on nonzero products; a degree-zero nonzero integer polynomial has no rational zero. Induction on irreducible factors therefore discards constant content factors and constructs a finite family of nonconstant integer irreducible divisors covering ALL rational zeros. Its cardinality is at most degreeX(F)+degreeY(F), independently of the integer content and coefficient height.

DeterminantFactorHeight applies the existing proved T9.4 factor-height inequality to every actual integer divisor. If F has partial degrees at most (A,B), then

  height(G) <= 2^(A+B)*(A+1)*(B+1)*height(F).

The square-root coefficient dimension is explicitly enlarged to the integer rectangle dimension. For the fixed degree range and height(F)<=N^kappa, one common threshold gives height(G)<=N^(kappa+1) for every factor, with both partial degrees preserved. No primitive-factor assumption is needed.

IntegerFactorProjectiveCurve uses the existing exact rectangle reconstruction to homogenize each arbitrary integer factor at its OWN partial degrees. The actual projective equation is nonzero, has the stated two homogeneities and coefficient height at most the original factor height. Exact denominator clearing proves equivalence between its vanishing at the original integer point and the factor vanishing at (d/e,v/u), for positive e,u. This also connects the original extracted biform to its actual affine polynomial, including cases in which its true partial degrees are smaller than the auxiliary rectangle.

DeterminantFactorCurveCover constructs the finite factor family, proves all projective point memberships and the literal finite inequality #S<=sum_G #zeros(G,S). DeterminantSignedFactorCover.uniform_factor_covers assembles this on EVERY occupied original interval for either sign of the shift. B,Amax,the factor-height exponent and N0 precede N, the signed shift, moving coefficients, box and entire population. There are at most Amax+B actual nonconstant integer factors per occupied interval, all with common polynomial height and bounded bidegrees; their actual projective zeros cover every original point.

P1-MATH-0246 records this complete finite factor and height reduction. The factors are proved irreducible over Z[X,Y]; no absolute-irreducibility claim is made. Remaining work includes the appropriate geometric factor cases, changes to short-vector lattice coordinates, uniform curve counts and the final interval/lattice summations. T1.4 and T1.5 stay in progress; coverage stays89 proved and72 conditional out of167, with six incomplete numbered results. There are245 improvements and one statement-scope correction. No external input, axiom, Paper C port, dependency download, compiler change or original manuscript edit is introduced. Palomar remains deferred.
