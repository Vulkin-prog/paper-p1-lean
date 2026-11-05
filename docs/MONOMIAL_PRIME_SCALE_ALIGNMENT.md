# Exact monomial prime scale and rounding for both strict comparisons

Source: companion T1.4 geometric ingredient and the numerical monomial scale step of the local determinant method. Strict determinant and obstruction comparisons remain exact.

MonomialPrimeScale.strict_power_domination proves that a prime base at scale C*L^alpha*V^beta forces the strict comparison D*L^A*V^B<P^N whenever C>=1,D<C,L,V>=1,N>=1 and the two explicit exponent inequalities A<=alpha*N,B<=beta*N hold. The proof retains exact real powers and strictness; no asymptotic estimate or existence of suitable parameters is assumed.

determinant_monomial rewrites the actual determinant size at the root-height box Y=(a+1)*V*L^a as the coefficient constant k!*(a+1)^(J*k) times L^(H*k+a*J*k)*V^(J*k). obstruction_monomial rewrites the actual obstruction bound as the constant(a+1)*(b+1)*b*(a+1)^b times L^(a*b+a+1)*V^(b+1). determinant_small and obstruction_small apply the proved domination criterion to these exact expressions. rounded_base constructs a positive integer base at the scale and at most twice the scale.

This reduces both remaining strict numerical comparisons to elementary uniform exponent choices for H and m, plus choosing a constant C larger than two explicit degree-only constants. Existence of those sharp exponent choices is the remaining step and is not silently assumed here.

P1-MATH-0359 adds six theorems. Coverage stays89 proved and75 conditional out of167, with164 completed. The ledger records357 improvements and two statement-scope corrections. Selective imports use locally available Mathlib artifacts. No axiom, unproved literature premise, dependency download, compiler change or original manuscript edit is introduced. The global sharp b>=2 input and main13.4 remain open; Palomar remains deferred.
