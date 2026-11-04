# Bounded common auxiliary coefficients from all singular actual row minors

Source: companion T1.4, companion_sections/arithmetic_appendix.tex:139, Step2 auxiliary extraction and its coefficient-height/parameter-order ledger; T1.5 uses that extraction. Original source hashes remain preserved.

The algebraic extraction of a common bounded auxiliary coefficient family is now proved for every actual finite point family, with an explicit height exponent selected before N. Its required analytic small-determinant premise remains explicit and unproved.

SmallIntegerKernelRankGap extends the existing pigeonhole argument to EVERY strict row/column dimension gap. For t<n integer rows of entry height H>0, it constructs a nonzero integer kernel vector of coordinate height at most (3*n*H)^t, and hence at most (3*n*H)^(n-1). Finite column reindexing is proved exactly.

FiniteRowKernel selects an actual spanning subfamily of rational rows. If every square row minor vanishes, that subfamily has fewer rows than columns; the rank gap is derived, not assumed. The bounded integer kernel of the selected rows then annihilates the entire original row family by a proved rational-span argument. The coefficient bound depends on the number of columns and entry height, with no dependence on the total number of source points.

DeterminantAuxiliaryCoefficients applies this construction to the actual integer monomial rows. The exact normalized determinant clearing proves the required vanishing minors from the finite smallness premise. One nonzero integer coefficient family annihilates every actual rational monomial row in the source population. Its explicit bound is

  (3*H*(X^(A+B)+1))^(H-1), H=(A+1)*(B+1).

DeterminantAuxiliaryHeight proves that at every fixed source height multiple Q*N this is at most N^kappa after an explicit threshold, with kappa=(A+B+1)*(H-1). Fixed degrees and Q precede kappa and the threshold, which in turn precede N, the source population and all its point data. The original-variable coefficient height is therefore fully uniform.

P1-MATH-0236 records this common coefficient extraction and explicit height exponent. The analytic normalized determinant bound, conversion to the actual auxiliary polynomial, remaining local curve counts and short-vector sums remain unfinished, so T1.4 and T1.5 stay in progress. Coverage stays89 proved and72 conditional out of167, with six incomplete numbered results. There are235 improvements and one statement-scope correction. No new external input, axiom, Paper C code port, dependency download, compiler change or original manuscript edit is introduced. Palomar remains deferred.
