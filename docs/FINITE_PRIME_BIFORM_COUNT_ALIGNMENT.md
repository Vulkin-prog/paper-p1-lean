# Global finite-prime count on the full original biform population

Source: companion T1.4 geometric ingredient and the full local-determinant finite-prime counting argument. Only the original first-pair box is imposed, and all signed primitive points are retained.

FinitePrimeBiformCount.unrestricted_second_pair_count proves the full original signed primitive population is bounded by8*(a+1)*(b+1)+4*(b+1)+4*(a+1)+8*a*b^2+4*(a+b)^2*(H+J)*(m*2^m*P), where a,b are the actual positive partial degrees. Only the first pair is restricted by the source box L>=1; the second pair is unrestricted. The prime base P>0, degrees H,J with J<b, and m enter through two explicit numerical comparisons: k!*(L^H*Y^J)^k<P^(k*(k-1)/2), k=(H+1)*(J+1), and(a+1)*(b+1)*b*height(G)*L^(a+1)*Y^b<P^m, with Y=(a+1)*height(G)*L^a constructed internally.

bounded_count constructs the fixed dyadic prime family, proves avoidance for each actual nonzero obstruction using its checked height bound, covers the population by the actual good-prime subsets, applies the proved fixed-prime count internally, and sums the explicit prime budget. It separately counts every zero-obstruction point. unrestricted_second_pair_count then invokes the checked endpoint-exception height split, counts all endpoint exceptions, and applies bounded_count to the remainder. No prime-family, avoidance, residue-count, auxiliary, minor or point-count hypothesis is assumed.

This closes the global algebraic and finite-prime counting argument with exact original point scope. What remains for the sharp b>=2 Heath-Brown theorem is a uniform choice of H,m and P satisfying both numerical comparisons at the required height exponents, with constants depending only on the two degrees and epsilon. That numerical choice is not assumed to exist here.

P1-MATH-0358 adds two theorems. Coverage stays89 proved and75 conditional out of167, with164 completed. The ledger records356 improvements and two statement-scope corrections. No axiom, unproved literature premise, dependency download, compiler change or original manuscript edit is introduced. Main13.4 remains open and Palomar remains deferred.
