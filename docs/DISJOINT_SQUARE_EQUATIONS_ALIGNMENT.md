# Companion T4.1 — Two equations suffice, with arbitrary coefficients

Source: Lemma T4.1, page 26, `p1:fixed:curve`,
`companion_sections/fixed_moments.tex:16`. Statement SHA-256:
`541205f707e088c00ac965f0b54abb3d30a14b550bc2e9575a3940e438666784`.
The complete numbered result is **proved**. P1-MATH-0069 records a
stronger statement and a simpler arithmetic proof.

## A fixed kernel from an actual square equation

For a finite set A of distinct integer offsets, the literal product is

    P_A(z)=prod_{u in A}(z+u).

The formalization uses integer coefficients c and actual integer squares.
Once z is in a fixed positive comparable interval and the offset width
is polylogarithmic, all factors are positive and nonzero. Taking integer
absolute values in c*P_A(z)=w^2 gives a natural square equation. The
odd-prime support identity for a product then proves

    sf(P_A(z))=sf(abs(c))

for every nonzero c. This is `SquareEquationKernel.integer_square_to_kernel`.
The actual square root is unrestricted. No compatibility, smoothness,
squarefreeness or coefficient-height bound is assumed.

## Uniform fixed-degree fibres

`FixedDegreeKernelCount.uniform_count` specializes the complete growing-
degree fixed-kernel count to any fixed degree cap d. Choose a positive
degree coefficient c0 depending on epsilon. Eventually d<=c0*loglog(N),
and the existing count gives exponent 2*c0*log(2)+epsilon/2<=epsilon.
All choices precede N; one threshold precedes every offset set and every
prescribed kernel q. The comparable-interval version follows by the
already proved finite dyadic cover.

This uses only the complete fixed-kernel proof chain: actual prime
supports lie in rad(q*resultant(A)), a subpolynomial number of two-linear-
kernel codes covers the fibre, and each code has the internally proved
uniform quadratic/Pell count. A nonempty fibre supplies its own effective
kernel heights. An arbitrarily large input coefficient cannot enlarge
this height budget. There is no Pila premise or circular dense-target
input.

`DisjointSquareEquations.single_equation` consequently proves a count
at most N^epsilon for one equation whenever 2<=card(A)<=d. Odd degrees
are included. Its threshold is independent of the nonzero coefficient.

## Two nonconstant equations and the exact integer population

For nonempty disjoint A and B, multiply the two actual equations. Their
product is

    (c*e)*P_(A union B)(z) = (w_A*w_B)^2.

The union has between two and 2d distinct roots. The previous result
applies with no size restriction on c or e. `integer_two_equations`
counts arbitrary finite integer populations, using an explicitly
injective passage to nonnegative natural coordinates. All square
equations, positions and cardinalities are transported exactly.

`DisjointSquareTheorem.solutions` is the full literal finite set of
integer solutions in [ceil(aN),floor(bN)] for arbitrary fixed a>0 and b.
`companion_T4_1` chooses j=2, independently of K and epsilon, and counts
that actual set. It covers every critical-band length with B=L+1 and
every offset satisfying |u|<=D0*B. The natural ceiling used for the
radius and its additive one are included in the uniform logarithmic
width bound. A single threshold precedes all root lists and coefficients.

Thus the source polynomial-height restriction 0<|D_i|<=N^A is
unnecessary, and its many-equation geometric proof can be replaced by
this arithmetic argument. The more general intermediate statements
permit every fixed polylogarithmic width.

## Scope and subsequent obligations

The same single- and two-equation theorems prove the complete one-variable
assertion in T1.7, including arbitrary nonzero coefficients. Its two-
variable surface estimates and graph consequences remain open, so
T1.7 is only in progress. The source dense-target classification and
conditional propagation are still separate obligations; completing this
one-variable input does not count them as proved.

Coverage is 69/167 (main 23/73, companion 46/94); confirmed improvements
are 69. No new external assumption, Paper C port, manuscript edit or
Palomar registration is introduced.

Disjoint-square verification: Lean v4.36.0-rc2 full build passed (9923 jobs); actual axiom audit passed for all 4740 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 2455 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records are intact. Ubuntu available space: 16.68 GiB. Full T4.1 is complete with j=2, arbitrary nonzero integer coefficients and actual integer solution sets. The one-variable part of T1.7 is complete; its two-variable and graph conclusions remain open. Coverage is 69/167 (main 23/73, companion 46/94); confirmed improvements are 69. No Pila or target-count hypothesis, new external assumption, Paper C port, manuscript-byte change or Palomar registration.

Validated complete proof checkpoint: [a870737a5c2bac6f352bf92984c80f7e30fa1dba](https://github.com/Vulkin-prog/paper-p1-lean/commit/a870737a5c2bac6f352bf92984c80f7e30fa1dba).


## P1-MATH-0096: counts for moving split roots

The one-variable split-product count now permits arbitrary moving
integer offsets. For fixed natural K,d and epsilon>0, one threshold
precedes every offset set A, nonzero integer coefficient c and finite
solution population S. If 2<=|A|<=d, every actual value n+a is positive
and at most N^K, and

    c * product_(a in A)(n+a) is an integer square,

then |S|<=N^epsilon. The variable n is natural but has no required
comparison with N. The offsets can be arbitrarily far from zero;
only the actual positive values are bounded. The coefficient c has
no height restriction. Two equations with disjoint nonempty offset
sets satisfy the same count. Fixed product-kernel fibres also have
the same bound, uniformly in their squarefree kernel.

The argument is internal. Two fixed individual squarefree kernels give
an injective positive Pell representation, with coefficients, square
parts and offset difference bounded by N^K. The full product kernel
and pairwise offset resultant have height at most N^(K(d+d^2)), using
one actual solution and the positive value cap. Individual prime
supports lie in that fixed kernel-resultant support. The number of
support codes is at most 4^omega(m)<=tau(m)^2=N^o(1), and every code
fibre is bounded by the checked uniform positive quadratic theorem.
Both square and nonsquare coefficient ratios are included.

This strengthens the previously checked one-variable portions of T1.7
and T4.1 beyond logarithmic offset windows, without Pila or another
external curve-counting premise. It provides an input for moving line
substitutions in later planar arguments; those substitutions and the
full planar population count T20.6 are NOT yet proved here. T20.6
stays not started. The two-variable geometric counts in T1.7 and the
dense weighted sector remain open. T1.7 stays in progress; T4.1 stays
proved. Coverage stays 78/167 (main 28/73, companion 50/94).
The relaxation of the offset hypotheses is confirmed improvement
P1-MATH-0096. Confirmed improvements become 96. No new external input,
kernel axiom, dependency download, original manuscript edit or Palomar
registration is introduced.

Verified under Lean v4.36.0-rc2: full lake build (11063 jobs), source and ledger checks, actual axiom audit of 7100 declarations (only propext, Classical.choice and Quot.sound), and 4817 direct ledger/evidence declaration checks; Ubuntu root free space 14.98 GiB. Original manuscript bytes and all 167 statement hashes preserved.
