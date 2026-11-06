# Actual full Euler triple integral truncated uniformly at logarithmic height

Source: companion T19.17 and the actual full Euler triple/Perron frequency route. Literal integrals, parameters, coefficients and cutoff quantifier order are explicit.

EulerFrequencyTruncation identifies the actual sum of log(p)/p over all primes <=X with the existing Mertens prefix and bounds every actual prime subset by log(X)+log(4)+4. Literal prime coefficient masses inherit this bound. If 2*p<=X, the actual coefficient f(p)/log(X/p) has norm <=1/log(2), for real prime-bounded f.

The actual unweighted two-prime/full-Euler integrand base is continuous and nonnegative. Its global bound is (eulerConstant/log(2))*log(X)*(log(X)+log(4)+4)^2, uniformly before ALL real prime-bounded functions and actual prime supports P,Q with 2*p<=X and q<=X. The whole-frequency Gaussian integral therefore is <=the ACTUAL integral over [-log(X)^10,log(X)^10] of base plus scaledTail(X), where scaledTail=(eulerConstant/log(2))*the proved literal tail envelope.

The actual scaled tail is nonnegative and tends to zero. For each epsilon>0 ONE X0 precedes ALL X>=X0, real prime-bounded coefficient functions and admissible prime supports, and the error is <=epsilon. Eleven theorems and two definitions are added in one module.

The quantitative global band/Halasz estimate and final logarithmic short-average assembly remain unfinished. T19.17 conditional; original T1.7 unconditional. Coverage: 164 proved, 1 conditional, 2 in_progress /167; all 73 main proved. Original false scopes/corrections, preserved sources, pinned Lean and allowed axioms unchanged. About 53.9 GiB is free on Ubuntu. No dependency download or Palomar registration.
