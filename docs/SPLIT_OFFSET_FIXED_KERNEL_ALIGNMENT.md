# The full actual fixed-kernel part of T5.2

The fixed-kernel assertion of companion T5.2 (`p13:short:split`) is proved.
The other assertion, with prescribed divisor and selected quadratic count,
remains open; the numbered result stays in progress. Coverage stays 56/167.
P1-MATH-0055 records the broader degree and width scope of the fixed-kernel
conclusion. There are 55 confirmed improvements.

## Actual family and quantifier order

For every c>=0, D>=1, fixed real A0 and epsilon>0, one threshold N0
precedes all N>=N0, positive natural W, natural q and finite integer
offset set A with

    2 <= card(A) <= c loglogN,
    W <= D(log N)^A0,
    |a| <= W for every a in A.

The literal finite family `values A N q` consists of N<=n<=2N with
the actual canonical squarefree kernel of P_A(n) equal to q. Its
cardinality is at most N^(2c log2+epsilon). No even-degree assumption
is used. The same estimate holds for every finite subset of that family.
No independent polynomial-height assumption is made on the product kernel q.

## Finite support coding

Choose two distinct a,b in A. Every linear kernel divides rad(q*D_A),
as proved in the actual-offset checkpoint. The pair of actual odd-exponent
prime supports therefore belongs to the product of two powersets of
(q*D_A).primeFactors. There are at most 4^omega(q*D_A) codes. Equal codes
give exactly equal linear kernels by their canonical product formulas.

## Actual quadratic fibres

Write n+a=u*s^2 and n+b=v*t^2 with actual canonical square parts.
The map n to (t,s) satisfies

    v*t^2-u*s^2=b-a.

It is injective on each fixed-(u,v) fibre: its first coordinate and
n+b=v*t^2 recover n. All linear values are positive and at most 3N
after the common width threshold. Thus u,v and both square parts are
at most 3N, while 0<|b-a|<=2W<=N. The uniform positive quadratic theorem
applies at height N^3. Its factorizable case includes u=v and square
coefficient products. No nonsquare exception or zero shift is omitted.

Each code contributes at most N^(epsilon/2), uniformly before all
varying coefficients and offsets. The derived actual q*D_A prime budget
gives 4^omega(q*D_A)<=N^(c log4+epsilon/2). Their product is the claimed
N^(2c log2+epsilon). Empty solution families, including impossible q=0,
are handled without assuming a representative.

## Scope of the extension

The fixed-kernel proof needs two distinct offsets and positive actual
linear values; it does not use a pairing of all factors. It therefore
extends to odd d>=3. The cubic-loglog resultant error also permits any
fixed power of log N as offset width. These extensions concern only
the fixed-kernel assertion. The prescribed-divisor part still needs its
paired-quadratic quotient and allocation/counting arguments.

The subsequent [grouped-resultant checkpoint](GROUPED_KERNEL_RESULTANT_ALIGNMENT.md)
closes the quotient argument in exact square form. The remaining allocation
and selected quadratic count are still not claimed.

The later [complete T5.2 checkpoint](PRESCRIBED_SPLIT_PRODUCT_ALIGNMENT.md)
closes the prescribed-divisor count as well. The odd-degree extension remains
specific to the fixed-kernel assertion; both assertions have broader widths.

No new unproved literature input, Paper C port, original manuscript-byte
change or Palomar registration is introduced.

The [complete T5.2 alignment](PRESCRIBED_SPLIT_PRODUCT_ALIGNMENT.md) now
closes the final selected count and all fixed comparable positive intervals.
