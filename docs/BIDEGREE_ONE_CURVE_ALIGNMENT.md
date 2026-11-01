# Elementary elimination bound on a bidegree-one auxiliary curve

The elementary elimination estimate for an auxiliary curve linear in one primitive pair is proved for
explicit integer forms and actual bounded solution sets. It includes
the two orientations used in T1.4 Step 3. Full T1.4 remains **in
progress**: extraction and nondegeneracy of its auxiliary chart forms,
the determinant/lattice construction, other curve cases and short-vector
summations are separate tasks.

Source: companion T1.4, page 6, `p1:arith:reuss`,
`companion_sections/arithmetic_appendix.tex:139`, statement hash
`fb662a1d5ab5e605f53d3e8c90093d96c77b1157614bf68fc134d4487283c89b`.
This strengthens the local algebraic count, as P1-MATH-0049.

## Exact coefficient and resultant height

For integer polynomials whose coefficients have absolute value at most B,
`ResultantHeight.resultant_bound` bounds their actual padded Sylvester
determinant by

    |resultant(f,g,m,n)| <= (m+n)! * B^(m+n).

Padded coefficient reflection preserves this coefficient bound. For the
two common-degree-d chart resultants R,R',

    |R*R'| <= ((2d)! * B^(2d))^2.

For coefficients at most N^a, fixed natural a,d, this gives
|R*R'|<=N^(4ad+1) once N>=((2d)!)^2. The actual polynomial-height
denominator bound therefore follows from the input coefficient height;
it is no longer an assumed resultant-height premise.

## Actual primitive elimination

Let F=homogenize(f,d), G=homogenize(g,d). Both actual chart resultants
are required nonzero. The previous checkpoint proves their identities
and supplies explicit coprimality/full-degree sufficient conditions.

For primitive integer lambda=(lambda_0,lambda_1) and tau, the auxiliary
equation is

    lambda_0*F(tau)+lambda_1*G(tau)=0.

The canonical integer Bezout coefficients of lambda define the actual
signed scale q. `scale_equations` proves

    q*lambda_0=G(tau),      q*lambda_1=-F(tau).

The scale is nonzero because tau is primitive and R*R' is nonzero.
Every actual q divides R*R', with both signs retained. The scale set
has size at most 2*tau(|R*R'|), even when each scale comes from a
different primitive pair tau.

Take an original bihomogeneous equation of degrees (ell,k), written
with homogeneous coefficient forms C_i of degree k in tau:

    sum_i C_i(tau)*lambda_0^i*lambda_1^(ell-i)=h,   h!=0.

`BidegreeOneElimination` constructs its actual homogeneous eliminant

    E = sum_i C_i * G^i * (-F)^(ell-i).

It has homogeneous degree D=k+d*ell and satisfies exactly E(tau)=q^ell*h.
For D>0, the nonzero-level grid theorem gives at most D*(2H+1) integer
tau values in [-H,H]^2 for each scale. The eliminant may be zero or
reducible. No irreducibility or coefficient-height premise is used in
this level-set argument.

At a fixed nonzero scale, tau determines both lambda coordinates
uniquely. An actual injective map and finite fibre sum therefore give

    #primitive solutions <= 2*tau(|R*R'|)*D*(2H+1).

The source orientations have (ell,k)=(2,1) and (1,2), giving eliminant
degrees 2d+1 and d+2. The generic theorem proves both elementary elimination orientations.
It bounds the remaining pair's height. The complementary bound in the
eliminated pair's height, when the other auxiliary degree is at least
two, still requires the separate Heath-Brown curve estimate. That
complementary estimate is not proved by this checkpoint.

## Uniform actual solution sets and stronger local scope

`BidegreeOneCurveCount.solutions` is the literal finite family of
primitive lambda,tau in their integer boxes satisfying both equations.
`realSolutions` uses the natural floors of real box heights, and
`mem_realSolutions` proves exact equality with the original real
absolute-value inequalities. Real coefficient exponents are transported
by a proved natural-ceiling bound.

For fixed ell,k,d and auxiliary coefficient exponent a, and every
epsilon>0, `actual_real_solutions_count` supplies one threshold N0
before all integer f,g with coefficient height <=N^a, all homogeneous
original coefficient forms C_i, every nonzero integer h, and every
real lambda height A>=0 and tau height H>=1. Its conclusion is

    #actual primitive solutions <= N^epsilon * H.

There is no height bound on the original coefficient forms, h, A or H.
Only the auxiliary f,g require fixed polynomial coefficient height.
The uncounted pair may be arbitrarily large; actual fixed-scale
injectivity proves the bound. This strengthens the local bidegree-one
argument without changing restrictions needed by other determinant
cases. No Thue or geometric curve estimate is used for this case.

## Remaining scope and provenance

Nonzero chart resultants and the two equations are explicit algebraic
hypotheses. The source's auxiliary-curve construction still has to
provide these forms, their nondegeneracy and their polynomial coefficient
height. No target counting bound is a premise. No completed T1.4
coverage is claimed: numbered coverage remains 54/167.

These are new P1 proofs using the pinned, proved Mathlib determinant,
resultant, homogeneous-polynomial and finite-grid results at
`9d581dfff2e41de989072ea63abf3daf69311520`, together with the already
audited elementary divisor bound. No new Paper C port or unproved
literature input is introduced. All original manuscript bytes are kept.

The full build passed (9,499 jobs); all 3,720 declarations passed the
actual axiom audit, permitting only propext, Classical.choice and
Quot.sound. All 1,435 distinct coverage/finding names were checked
directly by Lean. Original manuscript bytes are unchanged.
