# Aligned four-vertex mass and the remaining actual second-moment error

The four-vertex principal-edge sector containing an actual aligned
triple now has total ordered joint mass at most N^(-41/30+epsilon),
uniformly over every private-prime cutoff H after one critical-band
threshold. The seed may use either principal source channel and every
reduced affine target of any fixed polynomial height B^J, including
physical, endpoint, contact, irregular and badly normalized targets
already retained by the aligned-triple mass theorem. The literal pair
sector contains every disjoint actual principal-edge pair whose union
contains such a represented triple; the source-cover theorem checks
this inclusion. More generally, for every fixed finite source channel
family and fixed additional size k, the actual mass of all (3+k)-sets
containing an aligned triple has the same N^(-41/30+epsilon) bound.
The fourth and further windows require no extra alignment condition.

The proof uses the already proved actual unordered seed propagation,
with all zero masses retained, followed by the proved sharp aligned
triple bound. A four-set has at most 36 ordered pair codes in the
literal two-edge cover; the constant is absorbed asymptotically.
This improves the source N^(-27/20+o(1)) upper exponent in this
aligned sector, without a separate rank-loss argument for the last
window. Its contribution is proved o(beta^2).

The entire actual second factorial joint sum S has a precise residual
description. Define R as the sum of absolute actual covariances over
distinct principal edges with disjoint vertex sets, coupled event
spaces, and no aligned triple seed of the above polynomial height.
These definitions retain incompatible merged systems and their zero
joint probabilities. A finite upper decomposition proves
S<=beta^2+shared_joint_mass+aligned_joint_mass+R. Conversely,
R<=S-beta^2+2*coupled_product_mass; independent event spaces factor
exactly, and every negative covariance is bounded by its baseline
product. The product mass includes the diagonal and was already
proved at most N^(-7/3+epsilon).

Consequently the new unconditional estimates are
  |S-beta^2| <= R + N^(-41/30+epsilon),
  R <= S-beta^2 + N^(-7/3+epsilon), and
  ||S-beta^2|-R| <= N^(-41/30+epsilon).
The first is transported to the actual infinite prime-sign expectation
of Xi^2-Xi. The last also holds with error delta*beta^2 for every
fixed delta>0 and cutoffs 8B<=H<=D*B, after one common threshold.
Thus the remaining relative second-moment claim is exactly localized
to a concrete nonnegative residual covariance sum, up to a proved
negligible error. No residual asymptotic estimate is assumed as a
proof of T1.17, and that numbered result stays in_progress.

This is P1-MATH-0103. It records the stronger aligned-sector exponent
and the effective two-sided residual characterization. Coverage stays
79/167 and improvements total 103. The nonaligned residual covariance
bound is still open; no manuscript conclusion error is asserted.
There are no new external estimates or dependencies, the original
sources are unchanged, and Palomar remains a later milestone.

Verified with Lean v4.36.0-rc2: full lake build (11321 jobs), actual Audit.lean kernel-axiom audit (7694 declarations; only propext, Classical.choice, Quot.sound), all 5411 ledger references, source integrity (138 manifest entries / 167 numbered results), and git diff --check. Ubuntu root free space: 14.48 GiB.
