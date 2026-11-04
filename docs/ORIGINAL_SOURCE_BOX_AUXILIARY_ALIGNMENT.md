# Uniform actual auxiliary curves on every occupied original source-box interval

Source: companion T1.4, companion_sections/arithmetic_appendix.tex:139, Step2 auxiliary extraction and its coefficient-height/parameter-order ledger; T1.5 uses that extraction. Original source hashes remain preserved.

For positive integer shifts, the actual original source boxes are now assembled into uniformly bounded auxiliary projective curves on every occupied relative interval. The construction assumes no determinant, rank, kernel or solution-count bound. The later curve counts and lattice summations are still unfinished.

DeterminantBoxScales derives all four coordinate bounds from the actual source monomials and the lower bounds c1,c2,D,E,U,V>=1. It proves log(DE)<=log(N)+log(C), and eventually both base logarithmic sizes are at most 3*log(N), with one threshold before every varying box and coefficient. All actual points in the doubled box have coordinates at most 2*C*N.

DeterminantFixedInflation uses the single fixed constant K=16*C/rho. The original source comparisons imply K>=16. At each occupied center s0, the effective products satisfy

  DE <= (2E)^2*s0 <= K^3*DE,
  UV <= (K*U)^2*t0 <= K^3*UV,
  t0=(c1/c2)*s0^2.

Thus the same fixed logarithmic comparison constant serves every occupied center, with no moving-coefficient factor. DeterminantSourceBox.Box and Population record only the literal source parameters, box bounds, logarithmic lower bounds and original equation. Their actual coordinate-height, positive-denominator and source-value lower bounds are proved.

DeterminantBoxAuxiliary.uniform_biforms now chooses B,Amax,kappa,N0 before N, the positive integer shift h, the moving coefficients, every box and its entire source population. For the actual rounded M=ceil(N^zeta*exp(logShape)), with fixed 0<zeta<7/16, it proves M>=4 and the exact partition into at most 2M relative intervals. For EACH occupied interval it constructs A in 1..Amax and an actual nonzero integer bihomogeneous equation with bidegrees (A,B), all coefficients bounded by N^kappa, and vanishing at every original integer point in that interval.

All normalized chart assumptions and small-minor inequalities are derived internally from the original source-box comparisons, positive-shift polylogarithmic bound and lower logarithmic size conditions. The coefficient height and degree range are common to all occupied intervals. Coprimality is unnecessary for this auxiliary-construction step. This closes the positive-shift source-box auxiliary construction, not the full solution-count estimate.

P1-MATH-0244 records this completed assembly. General signed-shift transport, factor-height and irreducibility handling, local curve counts and short-vector summations remain open. T1.4 and T1.5 stay in progress; coverage stays89 proved and72 conditional out of167, with six incomplete numbered results. There are243 improvements and one statement-scope correction. No external input, axiom, Paper C port, dependency download, compiler change or original manuscript edit is introduced. Palomar remains deferred.
