# The explicit dense block-intersection cutoff in the actual second moment

The remaining actual principal-edge second-moment covariance sum is
now localized further to pairs whose complete event-space intersection
has dimension greater than 29L/30. This is an actual block intersection,
not an assumed relation-count input. The pairs still have disjoint
vertex sets, coupled spaces and no aligned triple seed of fixed
polynomial target height B^J, as in P1-MATH-0103. Write R_dense for the
sum of their absolute actual covariances and S for the complete
ordered factorial joint sum. Uniformly over all private cutoffs H,
  ||S-beta^2|-R_dense| <= N^(-41/30+epsilon),
  R_dense <= S-beta^2 + N^(-7/3+epsilon).
The comparison is also transported to the actual infinite-measure
expectation of Xi^2-Xi and to an error delta*beta^2 for every fixed
delta>0 and cutoffs 8B<=H<=D*B. No estimate for R_dense is presumed.

The generic finite probability argument is proved first. Every actual
positive block activation has exactly its homogeneous zero-target
probability. For arbitrary finite blocks e,f, the homogeneous union
probability is exactly 2^d times the product of their homogeneous
probabilities, where d is the dimension of the intersection of their
full square-class spans. Consequently, for positive actual marginals,
the absolute actual covariance is at most 2^d*q(e)*q(f). Incompatible
unions, including zero joint probabilities, are explicitly retained.
The identity holds for overlapping blocks as well.

An exact finite rank split and the previously proved coupled product
mass then show that, for every fixed real theta, all coupled principal
edge pairs with d<=theta*L have total absolute covariance at most
N^(-7/3+theta+epsilon). One threshold precedes every private cutoff.
The conversion from 2^d to a power of N is proved uniformly on the
critical band. Taking theta=29/30 makes this error
N^(-41/30+epsilon), the same as the aligned-sector error. Thus only
the strictly denser residual population can affect the beta^2 scale.

This is P1-MATH-0104: an explicit quantitative cutoff and a two-sided
characterization of the remaining second-moment obstruction. It does
not prove the dense residual covariance estimate or complete T1.17.
Coverage stays 79/167 and improvements total 104. No manuscript
conclusion error is asserted. No external estimate, dependency change,
source-byte edit or Palomar registration is introduced.

Verified with Lean v4.36.0-rc2: full lake build (11329 jobs), actual Audit.lean kernel-axiom audit (7711 declarations; only propext, Classical.choice, Quot.sound), all 5428 ledger references, source integrity (138 manifest entries / 167 numbered results), and git diff --check. Ubuntu root free space: 14.46 GiB.
