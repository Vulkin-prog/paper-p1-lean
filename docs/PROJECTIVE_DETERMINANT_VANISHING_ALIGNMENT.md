# Actual projective minor vanishing from the exact size inequality

Source: companion T1.4's geometric ingredient and the archimedean-versus-prime-power comparison in the local determinant method. Original homogeneous rows and signed coordinate bounds are preserved.

ProjectiveDeterminantVanishing.vanishing proves that the original projective monomial determinant is zero whenever its verified real size bound is strictly smaller than the verified prime-power divisor. The size condition is exactly k!*(L^H*Y^J)^k<p^(k*(k-1)/2), where k is the actual cardinality of the arbitrary finite row index type. Every original coordinate is bounded in absolute value, with possibly different nonnegative real bounds L and Y for the two pairs. All residue, denominator, curve and derivative hypotheses are retained literally from the projective divisor theorem.

indexed_divisor transports the exact divisor from Fin k to every finite index type by determinant reindexing. entry_bound proves the literal monomial bound L^H*Y^J using only the actual row inequalities r(i)<=H and s(i)<=J. determinant_bound combines this with the signed determinant expansion to give k!*(L^H*Y^J)^k. zero_of_dvd_small provides the exact integer-versus-real smallness criterion, including arbitrary signs. The row and column orientations remain explicit for later auxiliary-kernel construction.

The numerical size inequality is an ordinary algebraic hypothesis here and has not yet been derived from the final prime scale or degree choices. No minor-vanishing or point-count hypothesis is assumed. This module proves the minor vanishing from the independently checked divisor and size bound; construction of the common auxiliary equation and the global count remains open.

P1-MATH-0348 adds five theorems and one indexed matrix definition. Coverage stays89 proved and75 conditional out of167, with164 completed. The ledger records346 improvements and two statement-scope corrections. No dependency download, axiom, unproved literature premise, compiler change or original manuscript edit is introduced. Main13.4 and the sharp b>=2 Heath-Brown input remain open. Palomar remains deferred.
