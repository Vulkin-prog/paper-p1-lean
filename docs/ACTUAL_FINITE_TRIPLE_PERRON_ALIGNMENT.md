# Uniform actual finite triple Perron estimate with negligible smoothing error

Source: companion T19.17 and the actual internal triple/Perron route. The final finite estimate has no assumed fibre or aggregate error bound. The subsequent Euler-series limit is not claimed here.

GaussianFibreError groups the ACTUAL finite coefficients by their positive integer levels. A proved log(m)^2 fibre bound controls both the sharp side mass and the whole Gaussian error, using the internal uniform integer Gaussian sums. The explicit errorBound includes (exp(delta^2)-1) times the sharp mass and the actual reciprocal-log Gaussian contribution; no infinite sharp mass is introduced.

For width(X)=1/log(X)^8 the error is <=epsilon*X after ONE threshold, uniform before EVERY finite positive support and EVERY coefficient family satisfying its stated fibre bound. The scalar convergence follows from the proved scaledBound limit, the elementary exponential remainder bound, and the exact dependence on X, width and logarithms.

The final actual_triple_cutoff_small_uniform theorem substitutes the LITERAL triple coefficients, primes P with 2*p<=X, actual primes Q and any finite positive-integer set S. Its only coefficient restriction is |f(n)|<=1 on positive integers. The actual coefficient-fibre estimate is internal, including p=q and repeated products. ONE X0 precedes ALL X, f, P, Q and S. The ACTUAL sharp triple sum differs from its Gaussian smoothing by <=epsilon*X.

The actual_finite_triple_perron theorem combines this result, the exact finite Gaussian Perron formula and the exact prime-prime-integer factorization. It bounds the norm of the actual sharp triple sum by X/(2*pi) times the WHOLE real-frequency Gaussian integral of the two literal prime factors and the literal finite integer factor divided by sqrt(1+t^2), plus epsilon*X. No Perron input, aggregate error bound or hidden fibre estimate is assumed in this final theorem. One module adds eight theorems and two definitions.

This closes the finite triple Perron estimate with an error uniform in the integer truncation. Passage to the full relevant Euler series, the full Euler frequency budget, and the final Halasz/short-average assembly remain unfinished. T19.17 remains conditional, original complete T1.7 unconditional. Coverage stays 164 proved, 1 conditional, 2 in_progress /167; all 73 main results proved. Original false scopes/corrections, source hashes, pinned Lean and allowed axioms remain unchanged. About 54.0 GiB is free on Ubuntu; no dependency download or Palomar registration.
