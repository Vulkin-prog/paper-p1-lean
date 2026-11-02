# One-variable moving roots with a polynomial positive-value cap

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


## P1-MATH-0097: three fixed planar motifs

The fixed-plane, fixed-motif arithmetic in T20.6 is now proved
internally, using the checked positive quadratic and moving-root counts.
On a positive rational line b*y=a*x+c, positive integer a,b allow the
integer variable n=a*x and offset lists a*u and c+b*v. Exact product
scaling multiplies the original square prescription by a square, and
the resulting nonzero coefficient has no height restriction. The map
from a pair on the line to n is injective.

For each fixed polynomial value exponent and degree bound, a single
nondegenerate split equation on this line has at most N^epsilon
solutions, uniformly in the rational line and its integer coefficients.
The actual root-separation theorem removes at most two coordinates.
Three pairwise disjoint equation supports therefore leave one equation
with injective integer root shifts. All products and source events are
transported exactly; no affine independence surrogate or curve count
is assumed.

The resulting three-equation line count has one threshold before L,
all slopes, shifts, supports, coefficients and the solution population.
It needs one actual positive regular/direct pair on the line to establish
root separation. All other points are then counted by the same fixed
nondegenerate equation.

For a fixed plane b*y=a*x+g*z-h with 0<a,b<=N, L<=N, fixed triples
of offset motifs P,Q,R and fixed nonzero coefficients D_i, the number
of actual dyadic center triples satisfying all three transverse square
products is at most N^(1+epsilon). P and Q are nonempty and pairwise
disjoint among the three equations, and |P_i|+|Q_i| has a fixed degree
bound. R_i can have any size for this fixed-motif statement. The first
two windows have the actual injective/direct square-class hypotheses.
Neither g,h nor D_i has a height restriction. Fixing z gives positive
scaled values at most N^3, so the checked line estimate applies; summing
over its N dyadic values proves the bound. The proof includes an exact
finite fibre cardinality decomposition.

This replaces the source's per-fixed-motif Pila argument, which chooses
k+2 transverse products, by an internal three-product argument. It is
confirmed improvement P1-MATH-0097. The complete T20.6 still requires
orienting general planes and summing the admissible offset/small-prime
coefficient motifs, as well as selecting bounded-size motifs from its
macroscopic component population. Those steps are not asserted here.
T20.6 moves from not started to in progress. Coverage stays 78/167
(main 28/73, companion 50/94), confirmed improvements become 97.
The dense weighted sector remains open. No new external premise, axiom,
dependency download, original manuscript edit or Palomar registration
is introduced.

Verified under Lean v4.36.0-rc2: full lake build (11073 jobs), source and ledger checks, actual axiom audit of 7125 declarations (only propext, Classical.choice and Quot.sound), and 4842 direct ledger/evidence declaration checks; Ubuntu root free space 14.97 GiB. Original manuscript bytes and all 167 statement hashes preserved.
