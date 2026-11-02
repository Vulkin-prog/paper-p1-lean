# Actual centered activity of fixed private channels

The actual unordered private source pairs in every fixed rational channel
are now constructed. Forward orientation is injective, so their joint mass
is exactly half the already checked ordered channel mass. This family keeps
all affine-incompatible pairs. An injection into a dyadic center and the
integer displacement bx-ay proves the source-scale O(N(L+1)) cardinality
bound, with explicit constant 2(a+b)+1; it improves the earlier auxiliary
quadratic logarithmic cover without changing any source conclusion.

Every such pair is regular and has exact relative nullity |units|-1>0.
Its nullity is at most (L+1)/b. Its actual joint probability and absolute
centered coefficient are each at most p_nominal^2*2^((L+1)/b). Uniformly
through the critical band, the latter is at most N^(-2+1/b+epsilon).
All these bounds retain the exact affine incompatibility convention.
Filtering to positive joint mass constructs the literal compatible dependent
edge population of one fixed private channel, with the same cardinality,
rank and probability bounds and unchanged total joint mass.

The signed activity of the unfiltered family is exactly half the channel
mass minus its independent-product mass. Its absolute activity differs
from half the channel mass by at most that independent mass. On the
compatible family the absolute activity equals the same subtraction with
the restricted product mass. The unfiltered product mass is at most
N^(-1+epsilon), uniformly in the prime cutoff. Each fixed interior channel
therefore has total absolute activity at most N^(-1+1/b+epsilon), when
2b(L+1)<=H<=D(L+1). Any fixed finite union of the source channels with
b>=3 has total activity at most N^(-2/3+epsilon). The finite channel set,
cutoff multiplier, epsilon and all thresholds are fixed before N. These
proofs are unconditional; no BCN premise or target activity estimate is used.

This completes the individual-weight and finite-good-channel contributions
needed by T7.1 and begins the actual edge population for main 3.4. The full
classification of the remaining regular macroscopic pairs, the sharp 4/5
residual, the complete two-channel beta comparison and the full A2 upper
bound remain open. T7.1 stays in progress; main 3.4 moves from not_started
to in_progress. Coverage remains 77/167 (main 28/73, companion 49/94),
confirmed improvements 91. No new mathematical correction, external input,
axiom, download, original-source change or Palomar registration is claimed.

Verified under Lean v4.36.0-rc2: full lake build (10943 jobs), source and ledger checks, actual axiom audit of 6890 declarations (only propext, Classical.choice and Quot.sound), and 4607 direct ledger/evidence declaration checks; Ubuntu root free space 15.21 GiB. Original manuscript bytes and all 167 statement hashes preserved.
