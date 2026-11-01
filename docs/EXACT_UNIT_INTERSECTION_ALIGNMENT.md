# Exact unit coefficients for a private pair intersection

This is an algebraic extension of P1-MATH-0035 and preparation for article
3.3 and companion T2.5. It does not complete their probability/mass claims.
The already proved article Lemma 3.5 retains its original shared-value
premise for full union-image compression. All manuscript bytes are preserved.

## Actual private finite values

For finite sets S,T of actual positive integer values, write space(S)
for the image of their zero-sum prime-parity coefficient map. A private
coordinate on every distinct value in S union T makes the full value
map injective. `PrivateEvenIntersection.space_inter` proves

    space(S) intersect space(T) = space(S intersect T).

If a coefficient in S lies outside T, its private coordinate forces it
to vanish whenever the two value combinations agree. The literal
restriction to S intersect T preserves the total sum and combination.
`FiniteIntersectionSums.restrict_sum` proves this finite restriction
step on actual subtypes. There is no dimension assumption in the proof.

`intersectionMap` is the actual even prime-parity map into the common
space. Its injectivity and surjectivity are proved, yielding an explicit
linear equivalence from zero-sum coefficients on S intersect T to the
common class space. The rank is exactly card(S intersect T)-1, with
natural subtraction, including the empty and singleton cases.

## Actual normalized units and their coefficients

Set S=b*V_x and T=a*V_y. For positive a,b and centres at least two,
`UnitIntersectionEquiv.unitValue` sends an actual exact unit (i,j) to
b*label_x(i)=a*label_y(j). The target is the deduplicated set S intersect T.
Its injectivity and surjectivity are proved on the actual window indices.
No coprimality, height cutoff, separation or event premise is required.

`EvenReindex.reindex` explicitly transports zero-sum coefficient vectors
through a finite equivalence and preserves their actual value combinations.
Composing this with the private intersection equivalence gives

    {w : exactUnits -> F_2 | sum w=0}  equiv_linear  S_x intersect S_y.

The forward common class is exactly

    sum_u w(u)*parityVec(b*label_x(u.first)).

`unitIntersectionEquiv_apply` identifies this actual formula, and
`unitClassMap_injective` proves uniqueness of its coefficients. This is
an explicit parameterization, rather than a rank-only comparison.

## Exact actual ranks, including zero units

Under the private normalized-union hypothesis, both local ranks equal L.
The two exact identities are

    dim(S_x intersect S_y) = (u-1)_+,
    2L-dim(S_x+S_y)        = (u-1)_+.

They are `actual_intersection_rank` and `actual_pair_loss`. Empty and
singleton exact-unit sets give zero. Repeated formal copies of the two
windows cause no problem: actual equal values are deduplicated and
actual index projections are injective within each positive window.

The zero-unit classification does not identify the whole even image of
S union T with S_x+S_y. That full union-image identity still needs a
shared value, as in the earlier compression theorem. The new result
concerns the intersection and full pair deficiency.

## Character and probability bridge completed at the next checkpoint

The actual affine characters are now identified with the literal
predecessor-coordinate signs, and the actual private pair covariance is
proved to equal p^2 times the signed nonzero even-unit sum, including
jointly incompatible pairs. See the
[actual probability bridge](PRIVATE_UNIT_COVARIANCE_ALIGNMENT.md).
Selected-unit words must still be enumerated by the
[canonical patterns](CHANNEL_WORD_HOSTS_ALIGNMENT.md).
Defective-normalization removal and mass/profile asymptotics also remain
open. There is no new external mathematical hypothesis, Paper C port,
manuscript revision or Palomar registration.

Validated exact unit-coefficient checkpoint (9,337 build jobs;
3,425 audited declarations; 1,140 directly checked coverage/finding names):
[4461d6bdcc7e19648377fe47703c3bd0d14d21ee](https://github.com/Vulkin-prog/paper-p1-lean/commit/4461d6bdcc7e19648377fe47703c3bd0d14d21ee).
