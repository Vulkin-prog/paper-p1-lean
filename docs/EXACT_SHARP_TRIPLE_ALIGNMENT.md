# Exact actual sharp triple identity with prime band completion

Source: companion T19.17 and the internal literal triple convolution route. These are exact finite identities, including repeated primes and quotient boundaries; no asymptotic replacement is assumed.

TripleSharpIdentity proves the literal finite-set identity S intersect {n:d*n<=X} = [1,floor(X/d)] for any positive d, whenever S contains every integer from 1 to X and contains only positive integers. Both membership directions, positivity and the integer quotient endpoint are internal.

Expanding the ACTUAL sharp triple Perron sum over (P x Q) x S therefore gives the literal three nested sums with n<=X/(p*q). If Q contains every prime <=X/p for every actual p in P, the sharp sum equals RealTripleConvolution.triple EXACTLY. Extra primes in Q contribute zero because their integer quotient is zero. No analytic estimate or asymptotic identity is used.

The ACTUAL bandPrimes(X,U) consists of all primes q<=X with log(q)<=2*U. Whenever log(X/p)<=2*U, this set contains every prime q<=floor(X/p). Its primality and logarithmic bound are proved directly. Thus the exact sharp identity holds with the same completed prime band required by the checked analytic band estimate. Repeated primes p=q and all integer product multiplicities are retained. Seven theorems and one definition are added in one module.

This closes the literal sharp-triple identification, including the natural quotient boundary and completion of the q prime band. Passage of the full Euler series through the whole frequency integral, the full Euler frequency budget and final short-average assembly remain unfinished. T19.17 remains conditional, original complete T1.7 unconditional. Coverage remains 164 proved, 1 conditional, 2 in_progress /167; all 73 main results proved. Original false scopes/corrections, preserved sources, pinned Lean and allowed axioms remain unchanged. Ubuntu has about 54.0 GiB free; no dependency download or Palomar registration.
