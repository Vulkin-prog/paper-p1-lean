# Actual selected quadratic and its uniform resultant error

This closes the partition and exponent-averaging ingredients inside
companion T5.2. It extends the finite precision of P1-MATH-0056 without
adding an improvement identifier. The final count remains open; coverage
stays 56/167, with 56 confirmed improvements.

## A real pair partition

`FinitePairPartition.exists_pair_partition` constructs, for every even
finite set A, a finite family P of pairwise disjoint two-element blocks
with union A. Its cardinality identity is d=2*card(P). The proof removes
two distinct elements and inducts on the actual smaller even set. No
pairing witness or union/cardinality identity is assumed.

This partition depends only on A. It may be fixed once before varying
the counted integer n. The uniform selection theorem below accepts every
prescribed such partition and does not incur a fresh partition choice
for each solution.

## The exact finite average

Use the previously constructed e'=e/gcd(e,rad(D_A)) and the actual
allocated factors e_B. Write q_B for the actual kernel of the B-product.
Their product identities and the exact grouped overlap give

    sum_B (log(q_B)-2log(e_B))
      <= log(q)-2log(e)+4log(D_A).

The two contributions to the error are 2log(D_A) from the square-overlap
factor and 2log(D_A) from removing resultant primes from e. This is a
proved finite error bound; no optimality is claimed.

For nonempty P, a finite minimum supplies B in P with

    log(q_B)-2log(e_B)
      <= (log(q)-2log(e)+4log(D_A))/(d/2).

The supplied prescribed divisor e need only divide q. Its squarefreeness
is derived from the actual total kernel when applying the logarithmic
removal identity. All actual linear factors are required nonzero.

## Uniform absorption at growing degree

For fixed c>=0,D>=1,A0 and epsilon>0, under the actual width and degree
bounds W<=D(log N)^A0, d<=c loglogN, |a|<=W, d>=2, the proof gives

    4log(D_A)/(d/2) <= epsilon*log N

after one common threshold. It uses D_A<=(2W)^(d^2) and the proved
(loglogN)^2/logN limit, keeping all constants fixed before the varying
set, degree and width.

`source_fixed_pair_selection` has that threshold before every n,W,e,A
and prescribed pair partition P. For n>=N the width threshold also
makes all linear values positive. The selected block consequently has

    (log(q_B)-2log(e_B))/logN
      <= (log(q)/logN-2log(e)/logN)/(d/2)+epsilon.

The corresponding existential-partition theorem is a wrapper. Counting
can use the stronger theorem with P fixed for all solutions, so no count
of all partitions is hidden in the argument.

## Remaining count

The source main bound still needs the shifted actual quadratic count
for n+a, and the final enumeration over the fixed pair blocks, divisors
of the actual e' and dyadic kernel ranges. The fixed-kernel conclusion
was already completed separately. This exponent-selection checkpoint
does not claim the remaining prescribed-divisor count.

The subsequent [shifted-count checkpoint](SHIFTED_QUADRATIC_COUNT_ALIGNMENT.md)
closes the actual shifted quadratic count. The final enumeration remains open.

No new unproved literature input, Paper C port, original manuscript-byte
change or Palomar registration is introduced.
