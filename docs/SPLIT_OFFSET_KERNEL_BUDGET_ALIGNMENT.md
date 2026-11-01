# Actual split-offset kernels, resultant heights and supports

This closes further ingredients of companion T5.2 (`p13:short:split`).
The full count remains open. Coverage stays 56/167 and the mathematical
improvement count stays 54; verifying these source ingredients adds no
new improvement entry.

## Literal values with signed offsets

For a finite set A of integer offsets and natural n,
`SplitOffsetProducts.product` is the product of the natural absolute
values of n+a. If every |a|<=W<n, each n+a is positive and the natural
product, cast to integers, equals the actual signed product in the paper.
Empty products and sets are included; the results do not require even
degree. The actual kernel q is its canonical squarefree part, proved
positive, squarefree and a divisor of the product.

`resultant A` is exactly the product of |a-b| over a,b in A with a<b.
It is positive, and its number of factors is at most d^2. Thus

    D_A <= (2W)^(d^2),
    P_A(n) <= (3N)^d     if n<=2N and W<=N.

## The actual height and prime budget

For fixed c>=0,D>=1 and real A0, take W>0 with W<=D(log N)^A0,
N<=n<=2N, d=card(A)<=c loglogN, and |a|<=W. One threshold before all
W,n,A gives 2W<=N, so positivity and every finite bound apply. The proof
derives

    log(q*D_A) <= c loglogN log(3N) + E(loglogN)^3,
    E = c^2*(log(2D)+A0).

The previously proved budget with a cubic-loglog error now gives

    omega(q*D_A) <= (c+epsilon)log N,
    a^omega(q*D_A) <= N^(c log(a)+epsilon)   for each fixed a>1.

These estimates concern the actual q*D_A, with its height derived in
the proof. No bounded-degree assumption is silently imposed on q.

## Linear kernels lie in rad(q*D_A)

If a prime divides both n+a and n+b for distinct offsets, it divides
|a-b| and hence D_A. For a prime not dividing D_A, at most one linear
factor is divisible by it. The checked parity-vector product identity
therefore identifies its exponent parity in that factor and the whole
product. Every odd-exponent prime in a linear factor consequently
divides q or D_A.

This proves an actual support inclusion in (q*D_A).primeFactors, and
the exact divisibility of each linear kernel by the product of those
distinct primes. Factor 2 is included; odd exponent does not mean odd
prime. The support proof only needs all linear factors nonzero and
therefore also holds outside the positive counting range.

## Remaining T5.2 scope

The quantitative quotient of the paired quadratic kernels by q,
its divisibility into D_A^2, the prescribed-divisor allocation, the
selected quadratic enumeration, and the complete fixed-kernel count
remain open. This checkpoint does not infer a solution count from the
prime budget alone.

The subsequent [fixed-kernel checkpoint](SPLIT_OFFSET_FIXED_KERNEL_ALIGNMENT.md)
proves the full fixed-kernel count using actual injective quadratic fibres;
the other prescribed-divisor assertion remains open.

The later [grouped-resultant checkpoint](GROUPED_KERNEL_RESULTANT_ALIGNMENT.md)
also closes the quantitative quotient relation, in stronger exact square form.
Divisor allocation and selected quadratic enumeration still remain open.

No new unproved literature input, Paper C port, manuscript-byte change
or Palomar registration is introduced.

Verification: Lean v4.36.0-rc2 full build passed (9,579 jobs), actual
audit passed for all 3,950 declarations using only the three permitted
kernel axioms, and all 1,665 distinct ledger/finding names were checked.
