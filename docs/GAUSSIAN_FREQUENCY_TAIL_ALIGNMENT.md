# Actual whole-line Gaussian integral truncated with an explicit tail

Source: companion T19.17 and the actual full Euler triple/Perron frequency route. Literal integrals, parameters, coefficients and cutoff quantifier order are explicit.

GaussianFrequencyTail defines the ACTUAL complement of (-T,T] and proves that every outside point satisfies t^2>=T^2 for T>=0. The pointwise Gaussian split exp(-b*t^2)<=exp(-b*T^2/2)*exp(-(b/2)*t^2) gives the ACTUAL tail integral <=tailBound(b,T)=exp(-b*T^2/2)*sqrt(pi/(b/2)) for b>0.

For ANY continuous real function with 0<=F<=M, the literal Gaussian product is integrable and its actual tail integral is <=M*tailBound. Splitting the WHOLE real-line integral at (-T,T], with exact endpoint conventions, and using exp(-b*t^2)<=1 on the retained interval proves wholeIntegral(Gaussian*F)<=integral_{-T}^T(F)+M*tailBound. Seven theorems and two definitions are added in one module.

The quantitative global band/Halasz estimate and final logarithmic short-average assembly remain unfinished. T19.17 conditional; original T1.7 unconditional. Coverage: 164 proved, 1 conditional, 2 in_progress /167; all 73 main proved. Original false scopes/corrections, preserved sources, pinned Lean and allowed axioms unchanged. About 53.9 GiB is free on Ubuntu. No dependency download or Palomar registration.
