# Exact rank of the retained N=18, q=3 example

Checkpoint P1-MATH-0999 discharges optional item S07 of the
[independent review](reviews/2026-11-07/review.json).
The [Lean certificate](../PaperP1/Model/ExactRankPrimeCylinderExample.lean)
proves rank exactly 10, a one-dimensional homogeneous kernel, exactly two
compatible forcing samples, and forcing probability exactly 2^-10.

The five retained starts are 22, 25, 28, 31 and 34. Their negative
predecessor and two positive-word equations observe the fifteen integers
21 through 35. The supported cutoff is 36, containing eleven primes:
2, 3, 5, 7, 11, 13, 17, 19, 23, 29 and 31.

In the homogeneous system the following ten rows successively determine
the ten indicated bits. The coordinate of prime 19 occurs in none of the
fifteen observed integers.

| Observed integer | Parity row | Newly determined prime |
|---|---|---|
| 27 | sigma(3) | 3 |
| 32 | sigma(2) | 2 |
| 30 | sigma(2)+sigma(3)+sigma(5) | 5 |
| 28 | sigma(7) | 7 |
| 22 | sigma(2)+sigma(11) | 11 |
| 26 | sigma(2)+sigma(13) | 13 |
| 34 | sigma(2)+sigma(17) | 17 |
| 23 | sigma(23) | 23 |
| 29 | sigma(29) | 29 |
| 31 | sigma(31) | 31 |

Evaluation at prime 19 is injective on the homogeneous kernel. The existing
unused-prime sample is a nonzero kernel vector, so the kernel dimension is
one. Rank-nullity gives rank 11-1=10. Compatibility was already proved for
the actual retained affine forcing system. Its fiber therefore has two
samples out of 2^11 equally likely prime-sign samples, giving mass 2^-10.

The exact compiled endpoints are:

- `PaperP1.ExactRankPrimeCylinderExample.kernel_dimension`
- `PaperP1.ExactRankPrimeCylinderExample.exact_rank`
- `PaperP1.ExactRankPrimeCylinderExample.forcing_solution_count`
- `PaperP1.ExactRankPrimeCylinderExample.exact_forcing_probability`

The [complete replay](validation/checkpoint-0999/validation.json) passed
18,619 build jobs, 19,965 theorem axiom checks and 19,888 distinct reference
checks, all with actual exit zero. The eight new compiled theorem types
and their individual axiom reports are preserved in
[the scope report](validation/checkpoint-0999/scope/compiled-types.json).
The existing 528 compared manuscript types were replayed and remained
byte-identical.

The already delivered version 1.8 sources and PDFs retain their valid
rank<=10 text. Optional replacement prose for its existing unnumbered example:

> In this example the rank is exactly 10: the observed values
> 27,32,30,28,22,26,34,23,29,31 successively determine every prime bit except
> that of 19. Thus the compatible forcing event consists of exactly two
> prime-sign samples and has probability 2^-10.

This refines the finite example. It does not change the proved exponential
moment lower bound, establish an exact value of either full moment, give
a general rank formula, or improve the asymptotic threshold t>2. The 167
numbered statements and all six planned registration scopes are preserved.
Palomar submissions remain on hold at the user's request.
