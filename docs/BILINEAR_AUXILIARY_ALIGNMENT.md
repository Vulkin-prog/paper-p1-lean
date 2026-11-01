# Both height bounds for an auxiliary factor of bidegree (1,1)

The actual irreducible (1,1) auxiliary case of T1.4 Step 3 is now proved
in both orientations, with a bound in the minimum of the two real box
heights. This extends P1-MATH-0049. Full T1.4 remains in progress and
numbered coverage remains 54/167.

Source: `p1:arith:reuss`, companion page 6,
`companion_sections/arithmetic_appendix.tex:139`; original statement hash
`fb662a1d5ab5e605f53d3e8c90093d96c77b1157614bf68fc134d4487283c89b`.

## Exact exchange of the original equation

`BihomogeneousSwap.binary_expansion` proves the full coefficient
expansion of every homogeneous binary form, including zero forms.
`coefficients` constructs the transposed coefficient array for an
original equation of any bidegree (ell,k). Its coefficients are
homogeneous of degree ell. `original_swap` proves that evaluating
the new original equation on (tau,lambda) equals evaluating the old
one on (lambda,tau). The integer shift is unchanged.

For the bilinear auxiliary equation

    lambda0*(a*tau0+b*tau1) + lambda1*(c*tau0+e*tau1) = 0,

transposition replaces the coefficient matrix [[a,b],[c,e]] by its
transpose. `BilinearAuxiliary.auxiliary_transpose` is an equality
under the actual polynomial-ring equivalence which exchanges the
two variable groups. This equivalence preserves irreducibility over Q.
Every homogeneous linear form has the required two-coefficient
representation, and its coefficient height is preserved.

## Literal primitive points and real boxes

The two good-point predicates are proved equivalent. `solutions_swap`
identifies the actual finite solution sets by exchanging the pairs,
including their primitive conditions, auxiliary equation, original
equation and real absolute-value boxes. `solutions_swap_card` proves
the exact cardinality equality, without an assumed count.

Apply the already proved elementary projective curve count once in
each orientation. For fixed ell,k with ell+k>0, fixed real auxiliary
coefficient exponent and every epsilon>0, one threshold before all
forms, original coefficients, nonzero integer shifts and real A,H>=1
gives

    #solutions <= N^epsilon * min(A,H).

`actual_homogeneous_minimum_height_count` is stated on the actual
homogeneous forms, with irreducibility of their actual auxiliary
polynomial over Q. There are no separately assumed chart resultants
and no height restrictions on the original equation or shift.
The source original bidegrees (2,1) and (1,2) are included.

## Remaining scope

This closes both elementary orientations for bidegree (1,1). For an
auxiliary factor (1,b) with b>=2 or (a,1) with a>=2, the previous
elementary bound supplies only one of the two height estimates;
the complementary Heath-Brown estimate is still open. Source
determinant/lattice extraction and coefficient height, other curve
cases and short-vector sums remain unproved. No full T1.4 completion
is claimed, and no new unproved literature input, Paper C port,
manuscript revision or Palomar registration is introduced.

The full build passed (9,515 jobs), the actual axiom audit passed for
all 3,772 declarations, and Lean checked all 1,487 distinct
coverage/finding names. Only propext, Classical.choice and Quot.sound
occur; original manuscript bytes are unchanged.

Validated bilinear minimum-height checkpoint (9,515 build jobs;
3,772 audited declarations; 1,487 directly checked names):
[b6cfffa06c97f77d6cdf3ec017a3c9af3e5902bd](https://github.com/Vulkin-prog/paper-p1-lean/commit/b6cfffa06c97f77d6cdf3ec017a3c9af3e5902bd).
