# Unconditional all-cardinality pair-extension deficit

Source: main15.9, main_sections/exact_transfer.tex lines520-555. Actual D_2(u), all cardinalities, independent target weights, source non-directness and quantifier order were checked against unchanged V1.6 bytes.

Main Proposition 15.9 now has an unconditional canonical proof of the literal all-cardinality pair-extension deficit D_2(u) <= N^(-3/2+epsilon), for each fixed u>0. AllPairDeficit.article_15_9 returns one threshold before every N and critical L, with the actual dyadic pair covariance weight and products of actual independent target marginals. The exact source/target non-directness condition and all finite extension cardinalities are retained.

PairDeficitBounds supplies the fixed-order theorem directly from checkpoint416, the simultaneous finite-order sum by a finite maximum of thresholds, and the actual weak/exceptional partition estimates from checkpoint415. The finite channel height Q and tail cutoff s are chosen internally, before N. For large minimal seeds the already proved GoodPairSeedTail.uniform_large_seeds provides a genuinely uniform tail bound; no fixed-order asymptotic constant is extrapolated to growing order. The independent free complements are summed using the actual bounded mean. The weak and exceptional classes use the internally proved UniformPairClassDeficit bound.

The complete original statement and proof in main_sections/exact_transfer.tex lines520-555 were rechecked. The canonical theorem exposes no surface-cover, normalized-curve-count or BCN premise. This closes the particular former pair-partition dependencies without proving any of those general geometric properties. Original manuscript bytes and all previous conditional proof history remain preserved.

P1-MATH-0417 adds two modules and four theorems. Main15.9 moves from conditional to proved. Coverage becomes107 proved,57 conditional and3 in_progress out of167, with164 completed. The project records415 improvements and two statement-scope corrections. No new axiom, dependency download, compiler change or Palomar submission is introduced.
