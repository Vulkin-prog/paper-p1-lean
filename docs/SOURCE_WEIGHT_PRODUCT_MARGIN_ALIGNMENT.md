# Prescribed-scale logarithmic errors and polylogarithmic shifts give the determinant margin

Source: companion T1.4, companion_sections/arithmetic_appendix.tex:139, Step2 auxiliary extraction and its coefficient-height/parameter-order ledger; T1.5 uses that extraction. Original source hashes remain preserved.

The positive weight-product margin required by the uniform local auxiliary construction is now proved from the prescribed determinant scale, fixed effective-height comparisons and the polylogarithmic shift. No determinant estimate is an input to this margin theorem.

DeterminantWeightMargin proves finite stability inequalities: changing each nonnegative normalized logarithmic size by at most epsilon changes their product by at most 2*C*epsilon. If the horizontal weight sigma lies in [0,1] and the vertical weight is at least 1-theta, their product loses at most theta. Explicit positive epsilon,theta,eta, chosen from the fixed height upper bound and positive horizontal slack zeta, turn the remaining additive slack into the required factor (1+eta)^2.

DeterminantNormalizedWeights defines the actual weights

  sigma=log(M/4)/log(N), tau=log(rho*N/(4*h))/log(N).

Their exponential errors are exactly 4/M and 4*h/(rho*N). The horizontal lower bound M>=N^zeta*exp(logShape) gives sigma>=9/8*a0*b0+zeta-log(4)/log(N), with a0=log(DE)/log(N), b0=log(UV)/log(N). M<=N gives sigma<=1. For rho<=1 and h>=1, tau<=1; the uniform polylogarithmic-to-power estimate proves tau>=1-theta after one threshold preceding every allowed h. Every fixed logarithmic comparison error is likewise absorbed uniformly.

DeterminantSourceWeightMargin.uniform_margin chooses eta>0 and one threshold before N, M, h, all source scales and both effective-height products. Suppose the two base logarithmic sizes lie in [delta,C], the effective products X,Y lie respectively in [DE,K*DE] and [UV,K*UV], M is between the prescribed lower scale and N, and h is between1 and the fixed polylogarithmic bound. Then the actual normalized effective sizes a,b lie in [delta,C+1], sigma,tau are positive with sum at most2, and

  sigma*tau >= (9/8)*(1+eta)^2*a*b.

This is the local product-margin condition from the original scale and shift, including both fixed chart constants. The former product-margin premise is derived rather than supplied as an external fact. The already proved actual interval and center bounds provide the intended effective products; their remaining fixed-inflation and full-box assembly is still to be completed.

P1-MATH-0243 closes prescribed-scale and polylogarithmic-error absorption in the local determinant degree argument. Final global-box auxiliary assembly, factor-curve counting and short-vector summation remain open. T1.4 and T1.5 stay in progress; coverage stays89 proved and72 conditional out of167, with six incomplete numbered results. There are242 improvements and one statement-scope correction. No external input, axiom, Paper C port, dependency download, compiler change or original manuscript edit is introduced. Palomar remains deferred.
