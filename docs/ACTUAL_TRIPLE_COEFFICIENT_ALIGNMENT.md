# Actual triple coefficient fibres and exact Dirichlet factorization

Source: companion T19.17 and the internal actual triple convolution/Perron route. The bounds concern literal finite coefficients; no assumed fibre budget replaces the target estimate.

TripleCoefficientFibre defines the ACTUAL finite triple set (P x Q) x S, the integer level p*q*n and the literal coefficient (log(p)*log(q)/log(X/p))*f(p)*f(q)*f(n). Here f is ANY complex function bounded by one on positive integers; multiplicativity is not assumed for this finite factorization. P and Q consist of actual primes, S of actual positive integers, and 2*p<=X on P supplies log(X/p)>=log(2)>0.

At each integer m the projection of its actual triple fibre to (p,q) is injective: once p and q are fixed, the positive product p*q determines n uniquely. Both primes divide m. The von Mangoldt divisor identity proves sum_{p prime dividing m}log(p)<=log(m). The ACTUAL fibre weight is therefore <=log(m)^2, INCLUDING repeated primes p=q. The literal coefficients satisfy sum_{p*q*n=m}|a(p,q,n)|<=log(m)^2/log(2). No fibre population or coefficient budget is an input to the final actual theorem.

The actual Dirichlet polynomial of these triples factors EXACTLY as the P prime polynomial with coefficient f(p)/log(X/p), times the Q prime polynomial with coefficient f(q), times the S integer polynomial. All real logarithms, phases, denominators, finite sum permutations and repeated products are checked. Seven theorems and four definitions are added in one module.

This closes the actual coefficient-fibre and finite product factorization needed by the internal Perron route. The aggregate Perron error assembly, full relevant Euler-series limit, frequency budget and final short-average assembly remain unfinished. T19.17 remains conditional; original complete T1.7 unconditional. Coverage remains 164 proved, 1 conditional, 2 in_progress /167; all 73 main results proved. Original false scopes/corrections, source hashes, pinned Lean and allowed axioms remain unchanged. Ubuntu has about 54.0 GiB free, with no dependency download or Palomar registration.
