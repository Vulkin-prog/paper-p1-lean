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
