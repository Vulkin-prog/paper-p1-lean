# Complete prescribed signed saddle cost and nonpower obstruction under explicit ordinary inputs

Source: companion T19.16, companion_sections/limits_appendix.tex:1214, its precise logarithmic cost and consequent nonpower upper-bound obstruction. Original source hashes remain preserved.

Companion T19.16 is now completely assembled for the literal prescribed signed private-pivot forcing, conditionally on ordinary EIPInput and the six previously explicit ordinary geometric inputs. No target cost, profile or joint-probability bound is supplied in the final theorem.

SaddleLogPrefactors proves that every fixed logarithmic polynomial is absorbed by exp(eta*nu_N), and that every fixed logarithmic width is eventually at most N. ReciprocalOddPivotTripleScale transports the actual reciprocal-pivot bound at 3N to the original actual saddle at N, retaining the endpoint +1. Its only external dependency is the ordinary EIPInput already used for T19.15.

SignedSaddleCostUpper applies the complete actual finite ledger. The reciprocal term and every logarithmic factor are absorbed at the precise second saddle scale. The raw profile contribution has a smaller fixed power and is negligible at that same scale. The intermediate theorem exposes its actual raw-profile premise; the final theorem discharges it with the already proved enlarged actual profile under the six ordinary surface/curve inputs.

SignedSaddleCostTheorem defines the literal specified cost at E=ceil(3V_N/log2), and proves companion_T19_16. A single finite geometric bundle is selected before EVERY requested epsilon>0. Then one threshold precedes every actual critical length, and

  exp(-2V_N-epsilon*nu_N) <= specifiedCost(N,L)
  <= exp(-2V_N+epsilon*nu_N).

The exact logarithmic error bound is proved. For EVERY eventually admissible critical length sequence, the normalized error (log(cost)+2V_N)/nu_N tends to zero. The literal negation of IsBigO(N^(-alpha)) is also proved for every alpha>0; this obstruction uses only EIPInput and does not require the geometric upper-profile assumptions. It concerns this specified positive coordinate cost, and gives no lower bound for dependence, total variation or a cancelled scalar cost.

P1-MATH-0231 records the complete conditional assembly and the dependency distinction between its two directions. T19.16 advances from in_progress to conditional after the full pinned-compiler checks and direct axiom audit pass. Coverage becomes 89 proved and 72 conditional out of 167: 161 complete and six incomplete numbered results. There are 230 improvements and one statement-scope correction. The remaining incomplete results are main 13.4 and companion T1.4, T1.5, T1.10, T1.13 and T5.1. Neither document is fully formalized; many conditional results retain unformalized ordinary inputs. No additional external input, axiom, Paper C code port, dependency download, compiler change or original manuscript edit is introduced. Palomar remains deferred.
