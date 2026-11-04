# Actual asymmetric graph representation and target budget

Source: companion T1.10, arithmetic_appendix.tex:811-860. Follow-up to [the necessary scope correction](ASYMMETRIC_ALIGNMENT_SCOPE.md) and [the unconditional sparse support count](ASYMMETRIC_SPARSE_SUPPORT_ALIGNMENT.md).

The literal asymmetric even-loss domain now has an UNCONDITIONAL
finite graph representation and target-component rank budget. This
prepares the weighted dense sector of corrected T1.10, without assuming
a weighted profile, graph extraction or dimension inequality as an input.

AsymmetricEnvelopeGraph constructs the actual standard large-prime
graph on a longer envelope. Its old and new centres are x-R+1 and
y-R+1; the graph length is H and its prime cutoff is10(H+1).
The actual asymmetric data still use the ORIGINAL cutoff H and new
length L. Assume L+1<=R, 2R<=H, R<x,y and that the prescribed old
set lies within distance R of x. The new index map i -> R-1+i is an
actual injection preserving every original complete-window value.
Every envelope old vertex whose value is absent from the prescribed
old set is pinned, as is every new vertex outside that index image.
Thus an unpinned component cannot use invented old values or extra
new coordinates. The actual new target has exactly B=L+1 vertices.

AsymmetricEnvelopeRelation proves that EVERY member of the actual
even-selection preimage can be lifted into this pinned graph space.
Its old coordinates come from a literal binary subset of the actual
old values, with no parity constraint. Its new coordinates are the
original even selection extended by zero. The two combinations agree
above the original H, hence give all graph prime equations above
10(H+1); every additional pin vanishes as required. The old witness
is constructed only to prove membership, and is not counted as extra
host data. FinitePiExtensionSupport proves the needed injectivity and
zero-outside-image assertions.

PinnedTargetRestriction works for any finite pinned graph and any
finite list of target coordinates, even a noninjective list. Its image
rank is bounded by the unpinned components meeting the actual targets.
Coordinates outside that target can be discarded when they are pinned.
PinnedTargetBudget then uses the disjoint component supports to prove
2*(target component count)<=B+c1, where c1 is the number of these
supports meeting the actual target at exactly one vertex. It counts
isolated target defects as well as nontrivial singleton-target components.

AsymmetricEnvelopeRank injects the actual loss domain into the right
coordinate image of the pinned graph, using the original selected-index
extension. It proves delta*<=target component count and the exact
2*delta*<=B+c1 budget for the ORIGINAL new length, independent of the
longer envelope size. The unconditional universal bound delta*<=L is
also proved. No old-rank assumption, selected-value independence,
regularity, affine compatibility, nonalignment or geometric premise
is needed for these finite conclusions.

The remaining dense work is to enumerate actual component root systems,
apply the already checked enlarged-offset counts and control c1.
The weighted profile is NOT yet proved. The support bound remains
N^(4/3+epsilon), while the printed radius-one31/24 assertion remains
disproved under P1-MATH-0162. Coverage stays87/167 unconditional and48
conditional; findings stay161 improvements and1 statement-scope
correction. Original manuscript bytes and dependencies are unchanged.

The result ledger records exact verification and proof commits.
