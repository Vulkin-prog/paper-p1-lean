# Two-witness auxiliary: exact finite kernel budget

Source: companion Proposition T9.5, `p13:rig:two-witnesses`,
`companion_sections/pair_rigidity.tex:277`. Status: **in progress**.
Coverage remains 72/167; no complete two-witness polynomial is claimed.

## Explicit integer pigeonhole theorem

`SmallIntegerKernel` constructs the actual boxes of integer vectors
[0,M]^n and [-nHM,nHM]^t. Their exact cardinalities are proved, and
every matrix of entry height H maps the first box into the second.
A strict cardinal inequality gives two distinct vectors with the same
image; their difference is a nonzero integer kernel vector with every
coordinate at most M in absolute value.

`power_capacity` proves the cardinal inequality with M=(3nH)^7
whenever n,H>0 and 8t<=7n. Thus `exists_small_kernel` proves the exact
height bound without invoking an external Siegel lemma. This condition
is weaker than the source's t/(n-t)<6 requirement; the source dimension
budget is explicitly proved to satisfy both. The same height power 7
is retained. No improvement to the source final polynomial bound is
asserted from this observation alone.

## Actual coefficient slots and equation indices

`BiquadraticAuxiliaryCoordinates.CoefficientIndex` is the disjoint union
of the A0 rectangle of side 3q+1 and the three rectangles of respective
sides 3q-r_i+1 and 3q-s_i+1. Its exact cardinality is

    n=(3q+1)^2+sum_i (3q-r_i+1)(3q-s_i+1).

`EquationIndex` has the exponent pairs (a,b) with a+b<=6q. Its exact
cardinality is t=(6q+1)(6q+2)/2, with the total-degree bound proved
for every actual index. `BiquadraticAuxiliaryBudget` proves

    21q^2+18q+4 <=n <=4(3q+1)^2,
    t=18q^2+9q+1,   7t<6n,   8t<=7n.

The lower bounds assume only 0<=r_i,s_i<=q. A finite equivalence
transports the proved integer kernel vector back to the actual slot
set, and every original indexed equation vanishes.

## Height absorption

For 1<=q<=B, the upper dimension bound gives
3n<=(B+1)^(10q). If the matrix entry height H is at most
(B+1)^(cq), the actual kernel vector height is consequently at most
(B+1)^[7(10+c)q]. Both inequalities are explicit natural-number
statements, with no asymptotic premise left as an argument.

## Remaining obligations

The bounded integer matrix on these slots is still an arbitrary matrix.
Its actual construction from the two-variable Runge coefficients, common
denominator and height bound remain to be proved. Polynomial assembly,
vanishing order after primitive gcd division, integer separation and the
nonzero biquadratic norm with all degree and height bounds also remain
open. The generic finite kernel statement is not counted as the target
polynomial conclusion. No external theorem, new Paper C source or
Palomar registration is introduced.
