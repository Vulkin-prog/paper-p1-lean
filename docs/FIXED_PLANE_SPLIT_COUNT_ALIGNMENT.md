# Fixed-plane counts from three transverse motifs

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
