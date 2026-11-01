# Actual unit selections and canonical endpoint words

This extends P1-MATH-0043 and prepares article 3.3 and companion T2.5.
The local enumeration for each fixed pair is proved. Summation over all
actual dyadic hosts and the exceptional-normalization estimates remain open.
Neither numbered statement is newly counted complete.

## Literal selected subsets

`BinaryEvenSelections.evenEquiv` identifies zero-sum binary coefficient
vectors on a finite actual index set with its even selected subsets.
`nonemptyEvenEquiv` restricts this to nonzero vectors and nonempty even
subsets. The coefficient and support maps are inverse explicitly, and
weighted parity sums are preserved. A nonzero even vector selects at
least two actual units.

## Primitive exact-unit geometry

For positive coprime a,b, x>=2 and y>0, actual exact units satisfy

    b*label_x(i) = a*label_y(j).

`ExactUnitProgression.ordered_difference` proves that ordered units differ
by (a*d,b*d) for a natural d; a strict difference has d>0. The proof
extracts the actual positive common integer parameter using coprimality.
The left projection is injective. `stepUnit` constructs every actual
intermediate unit whose two indices still fit inside the windows.

`SelectedUnitExtrema.Bounds` specifies actual first and last selected
units, with their finite membership and extremality properties. Such
bounds exist for every nonempty selected set and are unique. A set with
at least two units has a unique positive primitive gap d. It satisfies

    1 <= d <= L/b,
    i_first in placements(L,a*d),
    j_first in placements(L,b*d).

Every selected unit has a unique intermediate primitive position k<=d.
The extremal units are selected units, rather than arbitrary endpoints
of an enclosing interval.

## Full finite bijection

`SelectedUnitWords.Shapes` consists of the literal positive gap d and
an actual first exact unit with both placements fitting the windows.
`ChannelGapWords.Words d` is a binary word on k=0,...,d with both
endpoints selected and even total parity.

`selection` maps a word to the image of its selected intermediate units.
The step map is injective, both endpoints belong to the image, and its
selected cardinality is even. The original coefficient at every step
is recovered from the image.

`SelectedUnitWordBijection.represent_selection` constructs a word for
every actual nonempty even selected subset. The minimum and maximum
units determine the first unit and gap; membership determines all word
bits. `encode_injective` proves that two encodings of the same subset
are equal. `canonicalEquiv` packages the resulting actual finite bijection.
There is no assumption that the chosen pair has private coordinates,
positive joint probability, separated windows or a height bound.

## Exact count and actual predecessor sign

For d>0, the existing endpoint-selection equivalence gives

    #Words(d) = 2^(d-2),
    A_d = #Words(d).

Natural subtraction includes d=1, where there is one word. An endpoint
at diameter exactly L remains a valid placement. There is no omission
of this boundary term.

For positive steps, i+a*k=0 forces i=0 and k=0. Since the first word
bit is one, its predecessor parity is precisely [i=0]. Therefore every
word at a fixed shape has the same actual sign

    placementSign(i_first) * placementSign(j_first).

`ChannelGapWords.word_sign` and `total_word_sign` prove this calculation.
`SelectedUnitFourierEnumeration.kernelEquiv` composes the canonical
word bijection with the actual nonzero even coefficient equivalence.
Its sign is identified with the actual `UnitAffineSigns` predecessor
parities. Finally `signed_unit_enumeration` proves the exact fixed-pair
identity

    signedUnitSum(a,b,x,y,L)
      = sum_(actual fitting shapes) A_d * sign(i_first) * sign(j_first).

The equality is in the reals, with the right side cast from its literal
integer finite sum. Empty and singleton unit sets are included. This is
the same actual signed unit sum in the
[private covariance formula](PRIVATE_UNIT_COVARIANCE_ALIGNMENT.md).
For an actual probability interpretation, that formula retains privacy
of every distinct normalized value and positive length.

## Remaining global step

The fixed-pair actual shapes must still be reindexed over all dyadic
pairs by the global patterns and the actual source-pair sets in
[the weighted translation aggregate](CHANNEL_WORD_HOSTS_ALIGNMENT.md).
Then defective normalizations must be removed, the p^2 baseline added,
and the full mass/profile estimates and phase equivalents proved.
Those global and asymptotic claims are not supplied by this local bijection.

No new literature premise or Paper C port is introduced. Existing primitive
channel geometry and source-parameter results are reused within P1.
The preserved manuscripts are unchanged and no Palomar registration is made.
