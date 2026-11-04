# Actual factor curves in all signed projective coordinate charts

Source: companion T1.4, companion_sections/arithmetic_appendix.tex:139, lattice-coordinate and uniform auxiliary-height steps; T1.5 uses that reduction. Original source hashes remain preserved.

Every finite primitive population on an actual auxiliary biform is now covered by uniformly bounded integer factor curves AFTER the four projective coordinate-chart changes. Signed coordinates and projective boundary points are retained throughout the finite count reduction.

IntegerPairFactorCharts proves exact denominator clearing for arbitrary signed integer pairs with nonzero last coordinates. The proof expands the actual biform, clears both homogeneous powers in a field, and derives an equivalence between its integer projective zero and the rational affine zero. The projective equation of every arbitrary integer factor is treated at its own partial degrees. Positivity of either denominator is not required.

IntegerPairFactorCover reuses the already proved finite integer irreducible factor selection and factor-height bound. Every actual affine-chart population is covered by at most Amax+Bmax nonconstant integer irreducible factors. All factors have bounded bidegrees, one common polynomial height, nonzero actual projective equations and bounded projective coefficients. Literal finite population cardinalities are bounded by the sum of the corresponding actual factor-zero populations. No injectivity of the rational-coordinate map is assumed; signed primitive representatives are counted as supplied.

FourChartFactorCover.uniform_factor_covers assembles this in all four charts. A single final coefficient-height exponent and threshold precede N, both degrees, the source family and the full primitive population. Each actual chart has its own finite factor family, and every original point is retained in one chart and covered by one of its actual projective factors. The exact chart partition gives

  #S <= sum_chart sum_factor #actual_factor_zeros_in_chart.

Every family contains at most Amax+Bmax actual nonconstant factors and obeys the same degree and coefficient-height bounds. Integer irreducibility is the proved property; absolute irreducibility is neither assumed nor claimed.

P1-MATH-0250 completes the signed affine/projective factor assembly after the coordinate-chart changes. Actual short-vector lattice bases, geometric factor cases, uniform curve counts and final interval sums remain to be proved. T1.4 and T1.5 stay in progress. Coverage stays89 proved and72 conditional out of167, with six incomplete numbered results. There are249 improvements and one statement-scope correction. No external input, new axiom, dependency download, compiler change or original manuscript edit is introduced. Palomar remains deferred.
