# Full actual reciprocal odd-pivot scale from the ordinary classical theorem

Source: companion T19.15, companion_sections/limits_appendix.tex:1138, full reciprocal-pivot sum and its square-part proof. Original source hashes remain preserved.

The full-population logarithmic equivalent in companion T19.15 is now proved conditional solely on the explicitly named ordinary largest-prime-factor theorem. The dyadic equivalent remains to be assembled.

SquarePartLogGeometry proves positive natural quotient bounds and the actual logarithmic range for floor(X/a^2). Every small square part has log(floor(X/a^2)) between log X-9V and log X, including the integer-floor loss. OrdinaryReciprocalPrimeInput defines EIPInput for the actual ordinary sum of1/P+(n). It states the classical two-sided logarithmic precision around the explicit square-root function G; it says nothing about the target odd-valuation pivot sum. It is an unformalized literature theorem supplied as an explicit argument, not an axiom or a proved declaration.

The uniform upper estimate for every small quotient is DEDUCED from that ordinary theorem, the internally proved finite quotient geometry, actual nu monotonicity and uniform G variation. No uniform square-part estimate is added as a premise. ReciprocalOddPivotUpper sums the actual square-part weights using their bounded reciprocal-square sum, rather than charging the number of parts as a prefactor. The large square-part tail is bounded internally, giving the explicit6X*exp(-G+epsilon*nu) upper bound.

ReciprocalOddPivotFullScale combines this actual upper bound, the ordinary lower bound and the proved odd-pivot comparison. The factor6 is absorbed at the diverging second scale and the internally proved additive saddle expansion replaces G by2V. Thus for every epsilon>0 a threshold gives BOTH

  X*exp(-2V_X-epsilon*nu_X) <= sum_{n<=X}1/kappa(n)
  <= X*exp(-2V_X+epsilon*nu_X).

P1-MATH-0222 records this complete full-population transfer under EIPInput. The separate dyadic transfer still remains, so T19.15 stays in progress. Coverage remains89 proved and70 conditional out of167, with eight incomplete numbered results. There are221 improvements and one statement-scope correction. No target odd-pivot estimate, unproved uniformity premise, new axiom, additional Paper C port, dependency download, compiler change or original manuscript edit is introduced. Palomar remains deferred.
