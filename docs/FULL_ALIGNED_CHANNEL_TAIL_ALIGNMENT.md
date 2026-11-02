# Full enlarged aligned channel tail, including zero exact units

Zero-exact-unit enlarged alignments are now handled on the original
model. The actual relative pair nullity is bounded by the full pair loss.
The complete uniform enlarged aligned rank theorem bounds that loss by
eta(L+1) when the normalized unit set is empty, including both coefficient
orientations. After the fixed margin is chosen, each actually dependent
such pair belongs to the already checked weak class. Direct pairs have
zero centered coefficient, even with zero marginals. Their total absolute
activity is therefore at most N^(-1+epsilon), without BCN.

A literal family of enlarged aligned unordered dyadic pairs is constructed
for all reduced 0<a<b with b0<=b<=(L+1)^3. Every member either has an
exact unit and belongs to the previously checked channel union, or is a
zero-unit enlarged alignment. A finite positive cover, with overlap costs
kept nonnegative, gives for the full family

    A_aligned(b0) <= N^(-1+1/b0+epsilon).

In particular all these channels from height 3 have activity at most
N^(-2/3+epsilon), and their full tail from height 5 has activity at most
N^(-4/5+epsilon), now including alignments with no exact unit. The number
of windows remains two; the logarithmic-height quantifiers are uniform.

This closes the full enlarged aligned high-channel tail needed by main
3.3 and T7.1. It does not classify the height-one/two boundary population,
complete the principal-channel comparison with all aligned pairs, or bound
the remaining macroscopic nonaligned sector. The complete signed pair
profile and T7.1 remain in progress. Coverage stays 77/167 (main 28/73,
companion 49/94), confirmed improvements 94. No new correction, external
premise, axiom, dependency download, original-source change or Palomar
registration is introduced.

Verified under Lean v4.36.0-rc2: full lake build (10997 jobs), source and ledger checks, actual axiom audit of 6982 declarations (only propext, Classical.choice and Quot.sound), and 4699 direct ledger/evidence declaration checks; Ubuntu root free space 15.10 GiB. Original manuscript bytes and all 167 statement hashes preserved.


## The height-one/two dyadic boundary populations

The literal enlarged aligned height-one and height-two populations are
now constructed. A general finite positive cover controls actual activity
from families covering every nonzero coefficient, without requiring
representations or covering classes to be disjoint.

For the reduced channel 1:2, dyadic geometry confines the first center
to [N,N+3(L+1)] and the second to [2N-3(L+1),2N]. Thus its unordered
family has cardinality at most 16(L+1)^2, including all original irregular
sites and all affine incompatibilities. Each actual covariance magnitude
and each joint probability is bounded by an actual single-site marginal.
The unconditional marginal cap therefore bounds both the joint mass and
absolute centered activity by N^(-1+epsilon).

For 1:1, a pair with separation at most L belongs to the already checked
close-pair family. A pair farther apart has no exact normalized unit and
belongs to the checked zero-unit enlarged alignment class. Their positive
cover gives total absolute centered activity N^(-1+epsilon), with no BCN
or local compatibility premise.

These are the small-height boundary contributions to main 3.3 and T7.1.
The complete principal-versus-aligned comparison and the macroscopic
nonaligned sector remain open. Both numbered results stay in progress.
Coverage stays 77/167 (main 28/73, companion 49/94), confirmed improvements
94. No new correction, external premise, axiom, dependency download,
original-source change or Palomar registration is introduced.

Verified under Lean v4.36.0-rc2: full lake build (11003 jobs), source and ledger checks, actual axiom audit of 6992 declarations (only propext, Classical.choice and Quot.sound), and 4709 direct ledger/evidence declaration checks; Ubuntu root free space 15.09 GiB. Original manuscript bytes and all 167 statement hashes preserved.
