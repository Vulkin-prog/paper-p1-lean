# Unconditional dense weighted sector including the full value kernel

Source: companionT1.8, companion_sections/arithmetic_appendix.tex lines745-777, both the relative-kernel and full-value-kernel assertions. The actual dense-component cutoff, criticalB=L+1, nonalignment, dyadic population, ranks and uniform quantifier order were checked against preserved V1.6 sources.

Companion LemmaT1.8 now has an unconditional canonical proof of both printed kernel bounds. DenseWeightedSector.uniform_kernels proves the actual relative-kernel sum and the full value-kernel sum, without block-parity rows, at rateN^(1+epsilon). The original dense-component hypothesis eta*(L+1)<=c(x,y), enlarged nonalignment convention, actual dyadic values and exact kernel ranks are retained. The conclusion holds for every finite qualifying population, including a larger population than the printed separated pairs. The statement and complete proof in companion_sections/arithmetic_appendix.tex lines745-777 were rechecked.

DenseComponentPairHosts.uniform_rank uses the already proved literal component/intersection comparison, whose error is at mostK*(L+1)/log(L+1), withK preceding the critical-band constant. An explicit logarithmic threshold makes this error at most(eta/2)*(L+1). Every dense-component pair therefore has actual even-space intersection rank at least(eta/2)*L, including irregular windows and local defects.

The internally proved dense nonaligned pair confinement then yields the stronger host countN^epsilon for the entire dense-component population. No separate small-component graph count or unproved surface/curve count is used. DenseWeightedSector.uniform_full_weight combines that subpower cardinality with the internally proved pointwise full value-kernel weight boundN^(1+epsilon) to bound the larger positive sum of2^fullRank itself. Subtracting one and applying the exact relative/full rank comparison gives both printed conclusions on one threshold.

DenseSourcePairKernel also proves the corresponding arithmetic pairLoss weighted sum with all local kernels retained. Its exact finite comparison to the full value-kernel sum is already proved. This supports the original arithmetic source bookkeeping without replacing full value kernels by parity-restricted kernels.

Only the former chosen-source/ordinary surface-cover and normalized-curve uses in this dense sector are discharged. General surface/curve properties, arbitrary graph host estimates and the sharp growing-degree BCN theorem remain separate. Original manuscript bytes and earlier conditional proof history remain preserved.

P1-MATH-0430 adds three modules and five theorems. CompanionT1.8 moves from conditional to proved. Coverage becomes114 proved,50 conditional and3 in_progress out of167, with164 completed. The project records428 improvements and two statement-scope corrections. No new axiom, dependency download, compiler change or Palomar submission is introduced.
