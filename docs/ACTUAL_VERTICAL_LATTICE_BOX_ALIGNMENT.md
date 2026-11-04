# Actual second-lattice box for the original signed source populations

Source: companion T1.4, companion_sections/arithmetic_appendix.tex:139, actual vertical lattice normalization; T1.5 uses that reduction. Original source hashes remain preserved.

Every ACTUAL signed source solution now lies in a uniformly bounded second-lattice image box, with all moving coefficient dependence explicit in the lattice itself. EffectiveSourceCoordinates defines U'=N/(c1*D^2) and V'=N/(c2*E^2). From the original source comparisons alone it proves 0<U'<=N, U<=C*U', rho*U'<=U and1<=C*U', and similarly for V'. It proves the exact identity V'/U'=(c1/c2)*(D/E)^2.

VerticalGridLattice uses the literal first-lattice transform with D'=2*C*V', E'=C*U', M'=2M and q=floor(k^2/M). Its rational center is exactly (V'/U')*q/M. The coefficient-scaled ratio approximation from P1-MATH-0262 and u<=2*C*U' give the actual image box

  |T(v,u)_i| <= 2*(49+16/rho), i=0,1.

The proof carries the divisions and cancellations explicitly, so no moving coefficient enters this fixed box radius. ActualVerticalLattice constructs the literal transform from the original Box, proves its exact grid-center identity, and derives that box bound for EVERY point of the actual SignedPopulation. It obtains the dyadic bounds, denominator positivity, source lower bound and signed equation from the population itself. No transformed-point estimate is assumed.

P1-MATH-0264 closes the actual second-lattice point box and effective-scale comparison. The population theorem is valid for either sign in the original d/e chart. Existing negative-shift auxiliary curves use a reversed chart: their eventual joint assembly must explicitly use the already proved coordinate flip and swapped source box; no alignment of these different interval labels is claimed here. Uniform second-lattice reduced coordinates and side/scale assembly, geometric curve counts and remaining primitive scale assembly remain open. T1.4 and T1.5 stay in progress. Coverage stays89 proved and72 conditional out of167, with six incomplete numbered results. There are263 improvements and one statement-scope correction. No new external input, axiom, dependency download, compiler change or original manuscript edit is introduced. Palomar remains deferred.
