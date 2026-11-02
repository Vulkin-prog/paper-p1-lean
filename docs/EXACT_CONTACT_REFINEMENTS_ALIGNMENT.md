# Exact-contact activation and centered covariance refinements

The literal dyadic exact-contact edge family is now constructed as
{x,x+L} with both starts in I_N. If the full union window of length 2L
is regular, every prescribed pair atom is exactly 2^(-2L). This follows
from a general full-effective-rank tuple uniformity theorem; affine
compatibility is proved by full rank rather than assumed. Uniform
irregular-window counts apply at length 2L with the enlarged logarithmic
width, and at least N/2 admissible contact starts have regular unions.
Consequently there is a positive c_C with

    c_C*N^(-1) <= M_contact <= N^(-1+epsilon)

for all sufficiently large critical N,L. The lower bound retains the
actual moving length phase through 2^(-2L). The general positive-family
activation theorem then gives

    N^(-1-epsilon) <= P(an active exact-contact edge) <= N^(-1+epsilon).

A generic positive-mass cover theorem proves that deleting probability-zero
members preserves the actual activation probability. Every positive-mass
close pair has separation exactly L, so the same probability bounds hold
for the event that two original active starts have distance at most L.
All statements concern the original infinite prime-sign probability law,
with both dyadic endpoints enforced and no BCN premise.

For centered coefficients the regular unions contribute zero, since their
actual pair rank loss is zero. Only the irregular full unions remain.
Their subpower count, the actual N^(-2+epsilon) point mass cap and exact
heterogeneous marginal caps prove the stronger bound

    sum_(exact-contact e) |c(e)| <= N^(-2+epsilon).

This improvement is specific to exact separation L. Strictly closer,
incompatible pairs can have negative centered coefficients and are not
included in that stronger exponent. It does not improve the already proved
N^(-1+epsilon) bound for all close-pair centered activity at arbitrary
fixed order. These positive-probability and exact covariance refinements
are recorded as improvement P1-MATH-0094. Main 6.3 stays proved; T7.1 and
T14.1 stay in progress. Coverage stays 77/167 (main 28/73, companion 49/94),
confirmed improvements 94. No full pair profile, multiplicative contact
probability equivalent, growing-order result, external premise, axiom,
dependency download, original-source change or Palomar registration is
introduced.

Verified under Lean v4.36.0-rc2: full lake build (10979 jobs), source and ledger checks, actual axiom audit of 6960 declarations (only propext, Classical.choice and Quot.sound), and 4677 direct ledger/evidence declaration checks; Ubuntu root free space 15.14 GiB. Original manuscript bytes and all 167 statement hashes preserved.
