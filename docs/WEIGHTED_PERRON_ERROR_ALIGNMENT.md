# Weighted quantitative Perron error remains negligible for growing band sums

Source: companion T19.17 and the actual full Euler triple/Perron route. Literal coefficients, products, error rates, shifts and quantifier order are explicit.

The actual smoothing error is nonnegative. After multiplication by log(X)^2/X it is eventually bounded by the explicit smoothingMajorant D*(log(X)^(-4)+log(X)^(-6)+(log(X)^4+log(X)^2)/X), which tends to zero. The same logarithmic-square weight times the actual scaled Gaussian tail tends to zero, using the proved log(X)^13/X bound.

combinedError(X) is the literal smoothing error plus X/(2*pi) times the literal scaled tail. It is nonnegative and weightedNormalized(X)=log(X)^2*combinedError(X)/X tends to zero. One threshold gives any requested bound. Eight theorems and four definitions preserve the quantitative rate needed by growing finite band sums.

The actual geometric band partition, global Halasz assembly and final logarithmic short-average theorem remain unfinished. T19.17 conditional; original T1.7 unconditional. Coverage: 164 proved, 1 conditional, 2 in_progress /167; all 73 main proved. Original false scopes/corrections, sources, pinned Lean and axioms unchanged. About 53.8 GiB is free on Ubuntu. No dependency download or Palomar registration.
