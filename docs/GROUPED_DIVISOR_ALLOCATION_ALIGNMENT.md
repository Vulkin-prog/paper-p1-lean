# Actual prescribed-divisor removal and allocation

This extends the arbitrary-block finite arithmetic of P1-MATH-0056
inside companion T5.2. The selected quadratic counting application is
still open. Coverage stays 56/167, with 56 confirmed improvements.

## Exact removal of resultant primes

`SquarefreeOutsideDivisor.outside e D` is the product of the actual
prime factors of e which do not divide D. It is positive, squarefree,
divides e and is coprime to D. The complementary inside prime product
divides D. For squarefree e their product is exactly e, and the inside
product is gcd(e,D). For D>0, the proof also identifies the outside
product exactly with the source expression

    e' = e/gcd(e,rad(D)).

Here rad(D) is the product of D.primeFactors. The exact decomposition
gives log e<=log e'+log D. The factor 2 is included like every other prime.

## Constructed factors for arbitrary disjoint blocks

For a finite family P of pairwise disjoint finite integer-offset blocks,
let A be their union. Every actual linear value is assumed nonzero.
For each B in P define e_B as the product of prime factors of e' which
divide the actual kernel of the B-product.

These explicit positive e_B divide both their block kernel and e'.
If a prime divides two distinct block kernels, it divides two distinct
linear factors, hence an actual difference and D_A. Since e' is coprime
to D_A, the allocated prime supports are pairwise disjoint. Their
products are therefore pairwise coprime.

If e divides the total kernel q, the exact grouped decomposition q|M
puts every prime of e' in at least one block kernel. The finite support
union is exactly e'.primeFactors. The checked disjoint union product
and squarefreeness of e' prove product_B e_B=e'. No allocation function
or product/coprimality conclusion is assumed as a premise.

## The actual enumeration budget

For a source family N<=n<=2N with offsets |a|<=W and
W<=D(log N)^A0, d<=c loglogN, a common threshold gives 2W<=N.
The actual remaining prescribed divisor satisfies

    e' <= q <= P_A(n) <= (3N)^d.

The proved growing-degree squarefree divisor budget then gives
card(divisors(e'))<=N^(c log2+epsilon), uniformly before n,W,e,A.
This count is deduced for the actual e'; it is not an enumeration premise.

The remaining T5.2 proof must construct/use the quadratic pairing, choose
a quadratic by its averaged exponent, count its shifted actual values
and complete the finite enumeration. Those steps are not yet claimed.

The later [selected-quadratic checkpoint](SELECTED_QUADRATIC_BUDGET_ALIGNMENT.md)
constructs the pairing and proves the uniform averaged exponent with its
explicit resultant error. Shifted counting and final enumeration remain open.

No new unproved literature input, Paper C port, original manuscript-byte
change or Palomar registration is introduced.
