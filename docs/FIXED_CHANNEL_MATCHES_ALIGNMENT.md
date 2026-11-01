# Fixed-channel matching classes — finite arithmetic checkpoint

Primary source: the proof of companion T2.6, page 22,
`p1:arith:fixed-channel-rank`,
`companion_sections/supplemental_arithmetic.tex:209`, statement hash
`8dd614c19e50df20ed1eb9f3ab37c07386f1ce3665c3499e26d83211ceab60b9`.
The same arithmetic appears at `p1:arith:matchdensity` in the proof
of T1.11. Both numbered rank results remain **in progress** and are
not counted complete. Original source bytes are preserved.

## Literal counted set

For natural coprime a,b and c>0, gcd(c,d)=1, let g=gcd(c,a), j=gcd(c,b).
`UnionMatchDensity.matchOffsets` is the union, over integer k in an
arbitrary half-open interval [lo,hi), of the two conditions

    c/g divides h+d*k,  or  c/j divides h+d*k.

Here h is any integer. It counts distinct offsets, not two copies of
the overlap. Every constraint is an actual divisibility predicate.

`UnionMatchDensity.abs_match_error` proves the two-sided finite bound

    |card(matchOffsets) - (hi-lo)*(g+j-1)/c| <= 3.

It is uniform in every integer parameter and requires no upper height
bound on c,d,h or the interval. A real-valued form is proved by
`FixedChannelMatches.real_abs_match_error`. In the source window
[-1,L) the length is exactly B=L+1. This explicit finite remainder
and two-sided formulation are P1-MATH-0037.

## Checked proof chain

1. `IntervalResidueError` proves both sides of the one-class count,
   using the exact difference of two integer ceilings. Its absolute
   error from length/modulus is at most one.
2. `AffineResidueClasses` constructs a solution of h+d*k=0 modulo a
   modulus coprime to d, by the actual integer Bezout coefficients.
   It identifies the entire solution set with one residue class.
3. Coprimality of a,b implies gcd(g,j)=1, so
   lcm(c/g,c/j)=c. The intersection of the two counted classes is
   exactly the class modulo c. This includes negative h and negative
   interval endpoints.
4. The exact finite inclusion-exclusion cardinality identity combines
   the three one-class errors. The reciprocal identity
   1/(c/g)+1/(c/j)-1/c=(g+j-1)/c gives the stated coefficient.

## Global numerator range and physical fractions

`FixedChannelMatches.large_numerator_density_lt_base` proves that for
c>b*(a+b-1) the density is less than 1/b. Thus
`density_le_gamma_all` controls every nonphysical interior fraction,
including numerators beyond the finite enumeration in gamma.
`window_match_gamma` gives the uniform bound B*gamma+3. In particular
the two leading channels have bounds B/3+3 and B/2+3.

`physical_fraction_of_divisor` proves that a fraction in the strict
dyadic interior with c dividing a or b has d=1 and c=a or c=b.
It does not treat these fractions as nonphysical classes.

## Scope of this initial checkpoint

This checkpoint proves the exact **divisibility-class count**. The
bridge from actual target/old-value coincidences into these classes,
the true-window treatment of physical fractions, the residual
normalized rank and the endpoint-source count were separate work at this checkpoint. The actual-value and physical-window
bridges are now proved in the [later checkpoint](ACTUAL_TARGET_MATCHES_ALIGNMENT.md).
Residual normalized rank and endpoint estimates remain open.
Consequently it supplies no complete target rank-loss bound, no Palm
mean estimate and no extra completed numbered result. In particular,
the class count is not assumed to equal an actual rank loss.

No external mathematical premise, new Paper C port, manuscript revision
or Palomar registration is introduced.

Validated finite matching checkpoint for T2.6/T1.11 and P1-MATH-0037:
[84c4c9a4016ce9f1c4ab9f7828675f3495eced85](https://github.com/Vulkin-prog/paper-p1-lean/commit/84c4c9a4016ce9f1c4ab9f7828675f3495eced85).
