# One homogeneous resultant suffices for the primitive denominator

The two padded chart resultants have the same absolute value. Primitive
coordinate cancellation therefore proves that every actual denominator
divides one homogeneous resultant, and the second nonvanishing condition
is redundant. This improvement is P1-MATH-0050 in T1.4 Step 3.

Source: `p1:arith:reuss`, `companion_sections/arithmetic_appendix.tex:139`,
original statement hash
`fb662a1d5ab5e605f53d3e8c90093d96c77b1157614bf68fc134d4487283c89b`.
Full T1.4 remains in progress.

## Actual matrix symmetry

For integer polynomials f,g and common padded degree d, put

    R  = resultant(f,g,d,d),
    R' = resultant(reflect(d,f),reflect(d,g),d,d).

`ReflectedResultants.sylvester_reflect` proves an exact equality between
the actual Sylvester matrices: reverse all rows and reverse the columns
inside each of the two degree-d blocks. The coordinate intervals and
reflected coefficient indices are proved to agree, including every
zero entry. The matrix identity holds over an arbitrary semiring and
requires no degree assumption on f,g.

Row and column permutations preserve the absolute value of an integer
determinant. Thus `resultant_abs_reflect` and `resultant_eq_or_neg` prove
|R'|=|R| and R'=R or R'=-R. No choice of the sign is needed for the
denominator argument.

## Primitive cancellation with a common coefficient

The preceding homogeneous Bezout identities give q dividing R*b^(2d)
and q dividing R'*a^(2d). Their natural absolute values now have the
same coefficient |R|. If gcd(|a|,|b|)=1, the gcd of these two multiples
is exactly |R|. `primitive_resultant_divisor` proves

    q divides R.

This uses d>0, degree(f),degree(g)<=d and the actual homogeneous form
divisibilities. It permits zero coordinates and both signs of q, and
does not assume the resultant nonzero for the divisibility identity.

For R!=0, the actual signed scale set therefore has size at most
2*tau(|R|). `SingleResultantFibreCount.finite_count` refines the previous
two-padded-chart-product count to

    #solutions <= 2*tau(|R|)*(k+d*ell)*(2H+1).

The previous padded product has absolute value |R|^2. The new count
uses divisors of |R| itself. The manuscript's native chart resultants
are replaced here by the explicitly constructed common-degree
homogeneous resultant; no unproved comparison with a differently
normalized native resultant is needed.

## Simpler actual asymptotic hypotheses

Nonzero R automatically implies nonzero R'. The actual real-box
N^epsilon*H count now requires only the first condition.
`coprime_actual_real_solutions_count` derives it from univariate
coprimality over Q and the condition that at least one polynomial
attains the padded degree. The second chart needs no separate
coprimality or full-degree hypothesis.

The earlier coefficient-uniform and real-height scope is retained:
auxiliary coefficients have fixed polynomial height, the original
coefficient forms and nonzero shift have no height bound, and both
real box heights may vary arbitrarily after the common threshold.

This remains the elementary elimination estimate in the remaining
pair height. The complementary Heath-Brown estimate in the eliminated
pair height, source auxiliary extraction/nondegeneracy/coefficient
height from determinant/lattice steps, other curve cases and the full
T1.4 estimate remain unproved. Numbered coverage stays 54/167.

These are new P1 proofs using the pinned Mathlib determinant/permutation
facts and previously audited homogeneous Bezout and primitive-coordinate
identities. No Paper C port, unproved literature input, manuscript
revision or Palomar registration is added.

The full build passed (9,503 jobs); all 3,733 declarations passed the
actual axiom audit, permitting only propext, Classical.choice and
Quot.sound. All 1,448 distinct coverage/finding names were checked
directly by Lean. Original manuscript bytes are unchanged.

Validated single-resultant checkpoint (9,503 build jobs; 3,733 audited
declarations; 1,448 directly checked coverage/finding names):
[a1ed70f2f336473fa51b6e345409308f78b78873](https://github.com/Vulkin-prog/paper-p1-lean/commit/a1ed70f2f336473fa51b6e345409308f78b78873).

The later [projective bridge](PROJECTIVE_NONDEGENERACY_ALIGNMENT.md)
derives all chart nondegeneracy conditions directly from homogeneous
common-factor coprimality or irreducibility of the actual auxiliary factor.
