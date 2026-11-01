# Actual private pair covariance and predecessor signs

This preparatory checkpoint now feeds the complete
[companion T2.5 proof](FIXED_CHANNEL_MASS_ALIGNMENT.md), including both
actual mass assertions and the literal real-cutoff separated family.
Statements of remaining fixed-channel work below describe this earlier
checkpoint. The complete main article 3.3 pair profile remains in progress.

This extends P1-MATH-0035 and prepares article 3.3 and companion T2.5.
It identifies an actual probability contribution, while the complete
selected-word enumeration and normalization error estimates remain open.
No numbered result is newly counted complete.

## Actual affine signs

Let L>0 and let a finite prime-sign assignment solve the actual run-start
system at x. `StartVertexSign.vertex_bit` proves that every true window
vertex has bit

    valueBit(label_x(v)) = valueBit(x) + [v=0].

Consequently, an even vertex coefficient vector has actual character
equal to the sign of its predecessor coefficient. The common offset
valueBit(x) cancels by its zero-sum condition. This step requires neither
privacy nor local regularity or a prime cutoff premise.

For an actual exact unit u=(i,j), b*label_x(i)=a*label_y(j). Complete
multiplicativity and zero-sum coefficients cancel the additional constant
prime bits of a,b. Thus the common class of an even unit coefficient
vector w has the paired affine character

    (-1)^(sum_u w(u)*[u.first=0] + sum_u w(u)*[u.second=0]).

Both sums inside the sign are in F_2. `UnitAffineSigns.paired_real_character`
uses separate actual local solutions. It does not assume a common solution
of both start systems.

## Actual Fourier sum

`PairFourierIntersection.full_support_family_sum` explicitly reindexes
full-support relations of two binary subspaces by their nonzero common
vectors. The relation is a diagonal pair, since u+v=0 implies u=v over
F_2. No dimension argument substitutes for the finite bijection.

`PairSquareClassFourier.full_support_at` allows any actual local affine
witnesses in the existing full-support formula. `pair_common_formula`
then expresses the actual infinite-measure centered pair moment as

    p_x*p_y * sum_(0 != z in S_x intersect S_y) chi_z(omega_x)*chi_z(omega_y).

The exact heterogeneous marginals are retained. For distinct centres,
`pair_moment_covariance` identifies that actual Bochner moment with
q_{x,y}-p_x*p_y. The finite-set joint probability uses actual Boolean
indicators; no assumed probability bound appears in the statement.

## Actual private-pair probability

For positive coefficients a,b, centres x,y>=2 and private coordinates
on every distinct value in b*V_x union a*V_y, the preceding
[unit coefficient equivalence](EXACT_UNIT_INTERSECTION_ALIGNMENT.md)
identifies the actual common classes with even exact-unit coefficients.
`PrivateUnitCovariance.common_sum_eq_unit_sum` transports the literal
Fourier sum through that equivalence and the actual character calculation.

The private coordinates imply both local ranks equal L.
`private_marginals` derives p_x=p_y=p=2^-L; positivity is proved from
this value before extracting the separate local solutions. Hence

    q_{x,y}-p^2 = p^2 * signedUnitSum,
    q_{x,y}     = p^2 * (1+signedUnitSum).

These are `private_pair_covariance` and `private_pair_mass`. The sum
ranges over every nonzero zero-sum coefficient vector on the actual
finite exact-unit set, with the literal predecessor sign above. No
coprimality, height restriction, dyadic membership, separation, dependence
or positive joint mass is required. Probability-zero pairs are included
and their sign cancellations are preserved. Empty and singleton unit
sets remain valid instances of the same finite formula.

The centered moment formula also holds when the two centres agree.
The displayed finite-set covariance and joint-mass formulas require
distinct centres, so that the two-element event is represented correctly.

## Remaining channel work

The signed sum on actual unit coefficients is now enumerated, for each
fixed pair, by its unique canonical gap, placements and endpoint-selected
interior word. See the
[complete local word bijection](SELECTED_UNIT_WORDS_ALIGNMENT.md).
These actual pair-specific shapes must still be summed over all dyadic
hosts into [the weighted host calculation](CHANNEL_WORD_HOSTS_ALIGNMENT.md).
Defective normalized hosts, the baseline p^2 term, and the full uniform
mass/profile asymptotics and phase equivalents remain unfinished.
Neither article 3.3 nor companion T2.5 is declared proved.

There is no new external mathematical input or Paper C port. The
original manuscript bytes are unchanged. No manuscript revision or
Palomar registration is made.

Validated actual private pair covariance checkpoint (9,347 build jobs;
3,446 audited declarations; 1,161 directly checked coverage/finding names):
[c4d65eee4e0d0efc81a7e16fcc17538546ba5cdd](https://github.com/Vulkin-prog/paper-p1-lean/commit/c4d65eee4e0d0efc81a7e16fcc17538546ba5cdd).
