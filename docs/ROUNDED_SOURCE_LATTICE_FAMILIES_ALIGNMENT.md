# Actual two-lattice families at the rounded determinant scale for signed polylogarithmic shifts

Source: companion T1.4, companion_sections/arithmetic_appendix.tex:139, literal determinant scale and signed-shift uniformity in Steps1-4; T1.5 uses that reduction. Original source hashes remain preserved.

The simultaneous ACTUAL source lattice families and both complete side sums now hold at the LITERAL rounded determinant scale specified by the paper, uniformly for every nonzero signed polylogarithmic shift. No scale-admissibility or minimum-grid-size premise remains in this construction.

RoundedScaleLower proves that for every fixed positive integer L and zeta>0, a threshold chosen BEFORE all moving scales gives

  L <= ceil(N^zeta*exp(logShape(N,D,E,U,V)))

whenever D,E,U,V>=1. It proves logShape>=0 from these actual scale hypotheses and reuses the existing fixed-log-error theorem to derive L<=N^zeta. Thus the actual rounded M eventually satisfies the grid threshold M>=32, without a new asymptotic input.

RoundedSourceLatticeFamilies combines this result with the proved doubled-scale admissibility at the absolute value of the original signed shift. For fixed source constants, epsilon, zeta in(0,7/16) and shift envelope, one kappa0,kappa1,N0 is chosen BEFORE N, the signed h and all source-box data. For every actual source Box and |h|<=K*(log N)^A, it proves M>=32,2M<=N and M*|h|<=N for the literal rounded M. It then constructs the SAME actual horizontal/vertical basis functions with all exact coordinate data, polynomial heights and both complete side sums for every admissible finite original interval set.

The passage from h to h.natAbs uses an explicit cast identity, so neither sign is silently discarded. Point-coordinate data remains in the original d/e chart; the separate reversed auxiliary chart used for negative shifts still needs its explicit flip at the later curve assembly.

P1-MATH-0269 closes instantiation of the complete actual two-lattice construction at the final rounded determinant scale and signed shift envelope. The negative auxiliary-chart flip, geometric local curve counts, removal of the N^zeta rounding margin from the final side bounds and primitive scale assembly remain open. T1.4 and T1.5 stay in progress. Coverage stays89 proved and72 conditional out of167, with six incomplete numbered results. There are268 improvements and one statement-scope correction. No new external input, axiom, dependency download, compiler change or original manuscript edit is introduced. Palomar remains deferred.
