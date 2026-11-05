# Fixed dyadic prime family with uniform integer avoidance

Source: companion T1.4 geometric ingredient and the prime-selection step in the local determinant method. A fixed dyadic family replaces the original interval-prime supply with explicit constant-factor enlargement.

DyadicPrimeCover.uniform_pool proves that for every positive integer P and fixed m there is one finite family T of exactly m distinct primes, all in(P,2^m*P], with sum at most m*2^m*P, such that every nonzero signed integer n with |n|<P^m is avoided by at least one prime of T. The same family works simultaneously for every such n. No prime-density, interval-supply, prime-family or coverage premise is assumed.

exists_pool constructs the family by choosing one Bertrand prime in each successive dyadic interval and proves distinctness, the exact cardinality and product>=P^m. pool_sum_bound gives the explicit sum budget. exists_nondividing proves that if all distinct primes divided n, their product would divide |n| and contradict its strict size bound. The only new Mathlib module is the already proved Bertrand theorem, compiled locally under the pinned compiler; no dependency download is needed.

This is a checked alternative to the interval prime supply in the local determinant method: fixed m allows a larger constant interval(P,2^m*P] without changing the final power of P. Applying it to the actual product of projective denominators and derivative, proving that product nonzero outside controlled exceptions, and deriving its size bound remain open. The final smooth-class cover and sharp exponent assembly are not claimed.

P1-MATH-0353 adds four theorems. Coverage stays89 proved and75 conditional out of167, with164 completed. The ledger records351 improvements and two statement-scope corrections. No axiom, unproved literature premise, compiler change or original manuscript edit is introduced. The global sharp b>=2 input and main13.4 remain open; Palomar remains deferred.
