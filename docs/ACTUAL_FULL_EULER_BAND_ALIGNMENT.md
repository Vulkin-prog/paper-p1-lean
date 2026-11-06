# Actual full Euler prime-band estimate from quantitative analytic factors

Source: companion T19.17 and the actual full Euler triple/Perron route. Literal band factors, integrals, errors and uniform cutoff order are explicit.

ActualEulerBand defines the literal frequency cutoff ceil(log(X)^10) and the explicit positive band constant bandConstant/(2*pi). The completed actual q prime band has q<=X, and the finite-height interval lies inside the same unit-frequency grid used by the full Euler budget.

The proved prime-band Cauchy estimate applies to the ACTUAL unweighted full-Euler integrand whenever p is prime, p>=log(X)^20, and U<=log(X/p)<=2*U with U>=log(2). Its finite-height integral is <=bandConstant*sqrt(the literal FULL Euler frequencyBudget). Combining the actual full Euler Perron theorem and uniform Gaussian truncation yields: for each epsilon>0 ONE X0 precedes ALL X>=X0, real complete monoid coefficients bounded by one on primes, and actual admissible P, and the literal triple norm is <=constant*X*sqrt(fullBudget)+epsilon*X. Five theorems and two definitions are added in one module.

This is an actual per-band estimate. Its qualitative epsilon error must be strengthened quantitatively before summing a growing number of bands.

Weighted quantitative global band/Halasz assembly and final logarithmic short averages remain unfinished. T19.17 conditional; original T1.7 unconditional. Coverage: 164 proved, 1 conditional, 2 in_progress /167; all 73 main proved. Original corrections, sources, pinned Lean and axioms unchanged. About 53.9 GiB is free on Ubuntu. No dependency download or Palomar registration.
