# Actual rounded determinant scale and exact integral monomial-row clearing

Source: companion T1.4, companion_sections/arithmetic_appendix.tex:139, the chosen M=N^zeta*mathcalM, vertical admissibility and monomial denominators in Step2; T1.5 uses these same boxes. Original source hashes remain preserved.

The horizontal/vertical scale compatibility and the exact integer-row bridge in the determinant argument are now proved for the actual chosen parameters. These results do not assume or establish the missing analytic small-determinant estimate.

DeterminantHorizontalScale defines the actual natural parameter M as ceil(N^zeta*exp(logShape)), retaining the exact rounding error. Its lower bound and positivity are proved. Uniformly before every allowed coefficient and box scale, M<=N^(zeta+9/16+eta) for every eta>0. For every fixed0<=zeta<7/16 and every polylogarithmic shift, one common threshold gives M*|h|<=N and M<=N/|h|. No moving-coefficient or shift-dependent threshold is substituted. The actual relative vertical error also satisfies its matching bound at the horizontal scale, using the previously proved ratio-free chart identity.

DeterminantIntegerRows constructs the literal rational monomial row at (d/e,v/u) and its integer row with entries d^a*e^(A-a)*v^b*u^(B-b). The exact row denominator is e^A*u^B. Clearing it is proved for every finite exponent index, including zero degrees, and every integer entry has height at most X^(A+B) when the four coordinates are at most X.

For every square family of actual rows, the rational determinant multiplied by the product of the exact row denominators equals the cast integer determinant. A proved integrality argument shows that a normalized absolute determinant below the reciprocal denominator product must vanish, both over the integers and rationals. That last smallness condition is an explicit premise of this finite bridge: the analytic determinant bound and auxiliary extraction have not been silently discharged.

P1-MATH-0235 records the uniform rounded scale and the complete rational-to-integral monomial bridge. T1.4 and T1.5 stay in progress for the analytic determinant bound, auxiliary extraction, remaining local curve counts and short-vector sums. Coverage stays89 proved and72 conditional out of167, with six incomplete numbered results. There are234 improvements and one statement-scope correction. No new external input, axiom, Paper C code port, dependency download, compiler change or original manuscript edit is introduced. Palomar remains deferred.
