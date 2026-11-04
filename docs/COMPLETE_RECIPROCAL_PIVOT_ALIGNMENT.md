# Complete full and dyadic reciprocal odd-pivot lemma under the ordinary classical input

Source: companion T19.15, companion_sections/limits_appendix.tex:1138, both the full and dyadic reciprocal-pivot assertions and the preceding scale convention. Original source hashes remain preserved.

Companion T19.15 is now completely proved conditionally on the single explicitly unformalized ordinary largest-prime-factor input EIPInput. Both the full and dyadic assertions use the actual odd-valuation pivot kappa(n), with kappa(square)=1 and the prime2 included.

DyadicReciprocalScaleBounds proves that the logarithmic preimage multiplicity Nat.clog2N+1 is absorbed by exp(eta*nu_N) for every eta>0. It also proves that the exact2*(floor(sqrt N)+1) exceptional contribution is negligible against the reciprocal lower main term. Both results follow from actual-root growth and the proved log log=o(nu) estimate; neither loss is supplied as an input.

ReciprocalOddPivotDyadicScale combines the earlier exact finite doubling transfer with the proved full-population sandwich. The lower bound subtracts the actual small-pivot contribution and divides by the actual logarithmic multiplicity. The upper bound uses the full sum at2N, monotonicity of the actual saddle and a proved second-scale comparison. The theorem companion_T19_15 gives a single threshold for BOTH original populations and every prescribed epsilon>0:

  N*exp(-2V_N-epsilon*nu_N) <= fullSum(N), dyadicSum(N)
  <= N*exp(-2V_N+epsilon*nu_N).

The cutoff and second scale are the actual uniquely defined implicit roots. Their precise explicit square-root expansion and log log=o(nu) property are internally proved. The only unformalized input is EIPInput, concerning the ordinary sum of1/P+(n) in the cited classical theorem. No target odd-pivot, dyadic, saddle or uniform square-part estimate is assumed.

P1-MATH-0223 records the complete conditional assembly. T19.15 advances from in_progress to conditional after the full pinned-compiler checks and direct axiom audit pass. Coverage becomes89 proved and71 conditional out of167:160 complete and seven incomplete numbered results. There are222 improvements and one statement-scope correction. The remaining incomplete results are main13.4 and companion T1.4,T1.5,T1.10,T1.13,T5.1,T19.16. Neither document is fully formalized; conditional results retain their external inputs. No new axiom, additional Paper C port, dependency download, compiler change or original manuscript edit is introduced. Palomar remains deferred.
