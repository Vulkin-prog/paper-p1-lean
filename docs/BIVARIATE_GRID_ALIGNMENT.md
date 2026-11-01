# Coefficient-independent bivariate grid counts for T1.4

The elementary bivariate level-set count needed in Step 3 of companion
T1.4 is proved. T1.4 remains **in progress**: its auxiliary determinant,
lattice changes, eliminant construction, other curve cases and lattice
summations are not proved by this checkpoint.

Source: `companion_sections/arithmetic_appendix.tex:139`, page 6,
`p1:arith:reuss`, statement hash
`fb662a1d5ab5e605f53d3e8c90093d96c77b1157614bf68fc134d4487283c89b`.
The applicable proof passage is Step 3, after the bidegree-one elimination
produces a positive-degree homogeneous polynomial F_3 and a nonzero
right-hand side h*q^2 or h*q.

## Finite theorem

For a nonzero bivariate polynomial p over any commutative integral domain
and a finite set S, `BivariateGridCount.zero_grid_bound` proves

    #{(x,y) in S^2 : p(x,y)=0} <= totalDegree(p)*#S.

The proof uses the pinned Mathlib Schwartz-Zippel theorem and explicitly
clears its nonnegative rational denominator. The empty grid is included.

If the constant coefficient of p is zero and c is nonzero, p-C(c) is
proved nonzero and has total degree at most that of p. Exact evaluation
identifies its zeros with the literal level set p=c. Consequently

    #{(x,y) in S^2 : p(x,y)=c} <= totalDegree(p)*#S.

A positive-degree homogeneous polynomial has zero constant coefficient
and total degree at most its homogeneous degree d, including p=0.
`homogeneous_grid_degree_bound` therefore gives d*#S. The integer
interval [-H,H] has exactly 2H+1 elements, and
`homogeneous_integer_box_bound` proves

    #{(x,y) in [-H,H]^2 : p(x,y)=c} <= d*(2H+1).

There is no coefficient-height, irreducibility, primitivity or nonzero-p
condition in this homogeneous level-set theorem. Only d>0 and c!=0
are required in addition to homogeneity. It includes powers of linear
forms and the zero polynomial. A rectangular source box with second
height at most the first is contained in this square box.

## Source role and remaining work

This gives a direct coefficient-independent alternative to Step 3's
manual exceptional-full-fibre argument once the eliminant and its
positive degree have been constructed. The source's integer RHS is
nonzero when h and q are nonzero. The actual resultant and eliminant construction
is not assumed to establish completed T1.4 coverage: this
checkpoint only proves the independent algebraic ingredient.

P1-MATH-0048 records the proof simplification and explicit finite bound.
Numbered coverage remains 54/167.

## Provenance

Mathlib commit `9d581dfff2e41de989072ea63abf3daf69311520` supplies
`MvPolynomial.schwartz_zippel_totalDegree`,
`MvPolynomial.IsHomogeneous.coeff_eq_zero` and `totalDegree_le`.
Their actual use is compiled and included through the P1 theorem axiom
audit under Lean v4.36.0-rc2. Only the selected Schwartz-Zippel and
homogeneous-polynomial dependencies were fetched; no complete Mathlib
cache, new Paper C port or unproved literature input is introduced.

The full build passed (9,477 jobs); all 3,677 declarations passed the
actual axiom audit, permitting only propext, Classical.choice and
Quot.sound. All 1,392 distinct coverage/finding names were checked
directly by Lean. Available Ubuntu-root space is 17.75 GiB after the
selected dependency downloads. Original manuscript bytes are unchanged.

Validated bivariate grid checkpoint (9,477 build jobs; 3,677 audited
declarations; 1,392 directly checked coverage/finding names):
[227b402575302cfdd178e7820c980874611a57c5](https://github.com/Vulkin-prog/paper-p1-lean/commit/227b402575302cfdd178e7820c980874611a57c5).

## Proved primitive denominator arithmetic

`PrimitiveDenominators.dvd_product_int` proves the exact arithmetic
implication from gcd(|a|,|b|)=1, q dividing R*a^m and q dividing
Rprime*b^n to q dividing R*Rprime. Multiplying each divisibility by the
other resultant and taking a gcd proves it directly; arbitrary natural
exponents are allowed. This replaces the source's prime-by-prime step.

The explicit signed divisor set contains every actual denominator; its
cardinality is at most 2*tau(|R*Rprime|). Nonzero R,Rprime are explicit.
`polynomial_height_count` uses the already proved elementary divisor
bound to obtain a common N^epsilon threshold whenever the product has
fixed polynomial height. It precedes every primitive coordinate pair,
every exponent and every finite family satisfying the divisibilities.
No coordinate height bound is required for this arithmetic ingredient.

The nonzero resultants, their two concrete divisibility identities and
the eliminant polynomial are still to be constructed. These remain
separate open steps of T1.4. This extension belongs to P1-MATH-0048;
numbered coverage remains 54/167.

The full build passed (9,479 jobs); all 3,683 declarations passed the
actual axiom audit, permitting only propext, Classical.choice and
Quot.sound. All 1,398 distinct coverage/finding names were checked
directly by Lean. Original manuscript bytes are unchanged.
