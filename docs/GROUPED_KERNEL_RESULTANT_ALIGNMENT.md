# The exact grouped-kernel resultant identity

This closes the quantitative resultant ingredient in companion T5.2
(`p13:short:split`). It strengthens the finite identity and its grouping
scope, P1-MATH-0056. It does not complete the prescribed-divisor count;
T5.2 remains in progress. Coverage stays 56/167, with 56 improvements.

## Exact kernel multiplication

For nonzero natural values a,b, the actual odd-exponent prime support
of ab is the symmetric difference of their supports. With O equal to
the product of their intersection, the checked finite product identity is

    sf(a)*sf(b) = sf(ab)*O^2.

Square multiplication leaves the kernel unchanged. Finite products have
the exact canonical kernel/square-part decomposition, and replacing every
factor by its own kernel preserves the kernel of the whole product.
Zero-input exceptions are excluded explicitly where needed; the support
of a square, including zero, is empty under the canonical definitions.

## Linear product and the actual difference resultant

For the actual nonzero linear values n+a, over a finite integer offset
set A, the product of their individual kernels is

    product_a sf(n+a) = q*R^2,    R | D_A.

The proof inducts over the offsets in increasing order. A prime in the
new overlap divides the new factor and at least one old factor, and hence
the corresponding difference. Distinct overlap primes have product
dividing the product of all new differences. The checked recurrence of
the actual unordered difference resultant completes the induction.
No estimate on the number of prime occurrences or pair valuations is
assumed. Negative linear values are represented by natural absolute
values; only nonvanishing is required for this finite identity.

## Arbitrary disjoint grouping

Let P be any finite family of pairwise disjoint finite offset blocks,
with union A. No block-size restriction is imposed. Define M to be
the product of the actual kernels of the block products. The checked
finite union product and kernel-product identities prove sf(M)=q.
Each block kernel divides its product of linear kernels, so

    M | product_a sf(n+a) | q*D_A^2.

The canonical square decomposition of M and cancellation of q>0 give

    M = q*R^2,    R | D_A.

In particular the exact natural quotient M/q is a square and divides
D_A^2. Two-element blocks recover the source paired-quadratic relation.
Empty blocks and the empty total family are included; no even total
degree, positive counting range or coprimality of block kernels is assumed.
Prime 2 is included throughout.

The source counting exponent still needs quadratic blocks, allocation
of the prescribed divisor away from D_A, and selected quadratic
enumeration. The algebraic grouping extension alone does not establish
that count for arbitrary blocks.

No new unproved literature input, Paper C port, source-byte change or
Palomar registration is introduced.
