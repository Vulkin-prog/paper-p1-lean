# Complete second-degree-one Heath-Brown bound and reduced remaining input

Source: companion T1.4 and Heath-Brown arXiv:1010.6217v3 Lemma2, printedp9, proofSection6. All signed primitive pairs, original real scales and the absence of a second-pair height bound are retained. Original manuscript hashes are unchanged.

GeometricBiformCoarseCount.finite_count bounds the exact signed primitive biform point set by the number of first-pair projections times2*(b+1). bounded_first_projection proves at most9*L^2 first pairs for every original real L>=1. Their combination gives the unconditional coefficient-uniform bound18*(b+1)*L^2, retaining no bound on the height of the second pair. Nonzero integer polynomial height is proved positive from literal coefficient recovery.

When the actual second partial degree b is one, second_degree_one proves the exact published Heath-Brown form with the explicit constant36: card(S)<=36*L^(2+epsilon)*height(G)^epsilon for every epsilon>0. The proof uses only the checked projective fibre bound, real-to-integer box counting and height>=1. It is uniform in all coefficients and in the first degree, includes both signs and projective axes, and preserves the original real L and unbounded second pair.

HeathBrownHigherDegreeBiformInput.Input is the strict restriction of the existing ordinary Heath-Brown input to b>=2. full_input recovers the exact original Input by combining that remaining unproved argument with the internally proved b=1 branch; restriction_of_full_input checks the converse restriction. The new property is an ordinary argument, not an axiom or a proved sharp point count. The sharp b>=2 estimate remains open.

The two modules add seven theorems and one definition. No numbered conditional result is promoted: companionT1.4,T1.5,T1.13 still depend on the sharp geometric estimate, now reducible to b>=2. Main13.4 and the other recorded geometric inputs remain open. Coverage stays89 proved and75 conditional out of167, with164 completed. The ledger records339 improvements and two statement-scope corrections. No dependency, axiom, compiler change or original manuscript edit is introduced; Palomar remains deferred.
