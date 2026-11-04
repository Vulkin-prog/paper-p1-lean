# Actual quadratic regridding with multiplicity two and admissible doubled scale

Source: companion T1.4, companion_sections/arithmetic_appendix.tex:139, lattice-coordinate and uniform auxiliary-height steps; T1.5 uses that reduction. Original source hashes remain preserved.

The actual quadratic grid needed for the second lattice now has a proved coefficient-independent multiplicity bound, range, rounding error and weighted transfer. The doubled determinant scale remains uniformly admissible by direct reuse of the existing scale theorem.

QuadraticIntervalGrid defines the actual integer grid q=floor(k^2/M). Exact integer quotient/remainder identities show that equal grid values have squared indices differing by less than M. When both indices satisfy k>=M/4, equal grid values force the indices to differ by at most one. Consequently EVERY finite grid fibre has cardinality at most TWO, independently of M or the moving coefficients.

For M>=32 and M/4<=k<=2M, the actual grid lies in the range

  M<=32*q, q<=4*M.

The exact remainder proves 0<=k^2/M-q<1, hence

  0<=(k/M)^2-q/M<=1/M.

Multiplying by any nonnegative real coefficient r gives the actual quadratic-center error at most r/M. This is precisely the form needed to retain coefficient uniformity in the vertical lattice normalization.

QuadraticGridWeights gives the literal finite image range and proves that every nonnegative weight sum over original interval indices is at most twice the corresponding sum over actual grid indices. This uses the proved fibre cardinality; no bounded-multiplicity estimate is supplied as an input.

DoubledDeterminantScale reuses the already proved DeterminantHorizontalScale.uniform_admissible theorem with the doubled shift bound. A single threshold BEFORE N, the shift, moving coefficients and source box gives 2*M*|h|<=N and 2*M<=N for the ACTUAL rounded determinant scale, without changing that scale. Thus the second-lattice reparametrization M'=2M remains admissible. No new asymptotic scale theorem is assumed.

P1-MATH-0261 closes the arithmetic quadratic regridding, its multiplicity/weight transfer and the doubled-scale admissibility required by the second lattice. The actual vertical point normalization and second-lattice coordinate/sum assembly, geometric curve counts and remaining primitive scale assembly remain open. T1.4 and T1.5 stay in progress. Coverage stays89 proved and72 conditional out of167, with six incomplete numbered results. There are260 improvements and one statement-scope correction. No external input, new axiom, dependency download, compiler change or original manuscript edit is introduced. Palomar remains deferred.
