# Concrete degree-zero auxiliary counts in the original positive coordinates

This checkpoint proves the two elementary counts used for degree-zero
auxiliary factors in T1.4 Step 3. It records proof progress rather than
a new mathematical correction. Numbered coverage remains 54/167 and
the mathematical-change ledger retains 50 confirmed improvements.

Source: `p1:arith:reuss`, companion page 6,
`companion_sections/arithmetic_appendix.tex:139`; statement hash
`fb662a1d5ab5e605f53d3e8c90093d96c77b1157614bf68fc134d4487283c89b`.
Full T1.4 remains in progress.

## Primitive zero directions, including infinity

`PrimitiveDirections` proves that primitive integer pairs with the same
rational direction differ by at most a sign. A canonical integer
Bezout scale and the primitive gcd prove its absolute value is one.
Each finite rational-slope fibre consequently contains at most two
pairs. The primitive axis has at most the two representatives (1,0)
and (-1,0).

`PrimitiveHomogeneousZeros` constructs the actual univariate chart of
a nonzero homogeneous degree-k form and proves it nonzero. A zero
with nonzero second coordinate gives an actual rational root, by
homogenization and injective coefficient/evaluation transport to Q.
The proved root-degree bound and the signed fibre count give

    #finite family of primitive zeros <= 2*(k+1).

This coarse bound includes infinity, zero coordinates and both signs.
It requires no coefficient height or coordinate box.

## Fixing (u,v), then counting the quadratic equation

`ZeroDegreeQuadraticFibres.Valid` uses the literal equation

    c2*e^2*v - c1*d^2*u = h

with all four coordinates positive and primitive (v,u). A nonzero
homogeneous auxiliary form in (v,u) leaves at most 2*(k+1) pairs.
Each actual fibre injects into the previously proved positive quadratic
equation count, with coefficients c2*v and c1*u. Fixed polynomial
height of c1,c2,h and all coordinates gives the required uniform
polynomial heights of these actual coefficients. No quadratic bound
is assumed. A common threshold before all forms, coefficients,
nonzero shifts and finite solution sets gives #solutions<=N^epsilon.
The auxiliary form itself requires no coefficient-height bound.

## Fixing (d,e), then counting the linear equation

`IntegerLinearFibres` proves the exact progression step B/gcd(B,A)
for actual solutions B*v-A*u=h, with B>0. The first coordinate
determines the second. The proved residue-class interval estimate
gives #solutions<=U*gcd(B,A)/B+1 for 1<=u<=U. Solvability proves
gcd(B,A)|h; h!=0 therefore bounds this gcd by |h|.

For fixed nonnegative comparison constants C0,C1 and real N>=0,

    A*u <= C1*N,       N <= C0*A*B,

the actual linear fibre has size at most C0*C1*|h|+1. A real floor
constructs the coordinate interval, so no separate integral box or
upper height for v is assumed.

`ZeroDegreeLinearFibres` uses the actual positive original equation,
primitive (d,e), and A=c1*d^2, B=c2*e^2. A nonzero homogeneous
auxiliary form in (d,e), together with the displayed pointwise scale
comparisons, gives the explicit finite bound

    #solutions <= 2*(k+1)*(C0*C1*|h|+1).

`ZeroDegreeAuxiliaryCounts` proves the source polylogarithmic-shift
budget from the pinned Mathlib logarithm/power asymptotic theorem.
For fixed A0>=0 and |h|<=(log N)^A0 this is <=N^epsilon, with one
threshold before all c1,c2,h, auxiliary coefficients and finite sets.
Neither c1,c2 nor the coordinates need an additional polynomial-height
bound in this linear local case; their actual scale comparisons suffice.

## Scope still open

The theorems count literal equations and primitive pairs in the
original positive coordinates. They do not yet construct the source
auxiliary polynomial, factor it, or transport its factors through the
source unimodular lattice changes. The determinant/lattice height
control, the complementary Heath-Brown count for the remaining
bidegrees, conjugate intersections and short-vector sums remain open.
No full T1.4 completion, manuscript revision or Palomar registration
is claimed. The already audited quadratic count and interval-residue
proofs are reused within P1; no new Paper C port or unproved
literature input is added.

The full build passed (9,527 jobs), the actual axiom audit passed for
all 3,795 declarations, and Lean checked all 1,510 distinct
coverage/finding names. Only propext, Classical.choice and Quot.sound
occur; original manuscript bytes are unchanged.
