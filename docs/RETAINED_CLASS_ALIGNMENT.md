# Companion T12.1: the actual first retained class

The full numbered lemma is proved, including the source compressed-block
definition, heredity, the unique dependent pair and the boundary-nullity
bound on actual regular arithmetic windows. Numbered coverage is 55/167.

Source: `p1:stop:class`, companion T12.1, page 50,
`companion_sections/stopped.tex:58`; original statement hash
`ed9f0c28da35e7bb5006b72ac613951a9561404177bd32039821cfffa1c8ec46`.
The strengthened scope and explicit constants are P1-MATH-0051.

## Actual rank and relation kernels

`RetainedNullity` works with arbitrary finite effective binary spaces,
even inside an infinite-dimensional ambient space. It proves
submodularity of their actual span ranks and supermodularity of their
actual relative nullities. Rank-nullity is the existing kernel-dimension
identity, without adding local relations again.

If e is contained in I and rho(I)=rho(e), every restriction satisfies

    rho(J) = rho(J intersect e),     J subset I.

In particular, a restriction retaining both endpoints of a pair has the
same compressed nullity; removing an endpoint makes it direct. These
claims do not require equal dimensions of the individual spaces.

## Exact equivalence with the paper's compressed block

`CompressedBlocks.family` has one index for the actual span of e and
one index for each singleton outside e. Its addition map has the same
range as the actual span of I, and its relative nullity satisfies

    rho(compressed family) + rho(e) = rho(I).

Injectivity of this addition map is therefore proved equivalent to
rho(I)=rho(e), when e is contained in I. Ordinary directness is also
proved equivalent to zero relative nullity. `SourceRetained` consequently
equals precisely the paper's class of direct families and one compressed
good pair; this equivalence is proved, not postulated as a rank condition.

`RetainedDependence` proves heredity and uniqueness of the dependent
two-element subfamily. The uniqueness is among every dependent pair in
I, including pairs not initially declared good. It also proves the
general finite boundary estimate rho(I)<=R+L when retained edge
nullities are at most R and each local boundary rank is at most L.

## Actual regular windows and good edges

`RetainedGoodEdges` uses the existing literal `goodEdges H N L` and
`squareClassSpace x L`. Every good edge is a two-element subset of the
actual regular set, has positive actual relative nullity, and obeys

    rho(e) <= L/3 + 1.

This follows from the proved finite compression, whose leading
denominators are 3 and 4, and the exact local ranks L on regular windows.
For every family inside the regular set, actual relation-kernel nullity
is identified with the paper's cardinality-times-L rank deficit.

The actual source class is hereditary and each non-direct member has
exactly the dependent pair stated above. Its ordered boundary, restricted
to the actual regular ground set, satisfies the explicit finite bound

    0 < rho(I) <= 4L/3 + 1 < 3L/2,     N>=2, L>=7.

`RetainedClassTheorem.companion_T12_1` proves all three conclusions under
one threshold in the fixed dyadic critical band. The threshold precedes
every length, real prime cutoff, retained family and boundary family.
The logarithmic lower bound gives L>=7. Affine incompatibility is not
discarded or assigned positive mass: the good-edge definition retains
its actual positive joint probability, and the argument here is an
identity about effective spaces and actual finite classes.

## Revision consequence

The next manuscript can state the heterogeneous finite version of the
heredity/uniqueness lemma, the exact restriction identity, and the
general boundary increment. The original regular equal-rank setting
then gives the explicit +1 constant and the finite threshold L>=7.
Neither original manuscript is edited here. No new unproved literature
input or Paper C port is introduced. Whole-paper formalization and
Palomar registration remain later milestones.

The full build passed (9,537 jobs), the actual axiom audit passed for
all 3,826 declarations, and Lean checked all 1,541 distinct
coverage/finding names. Only propext, Classical.choice and Quot.sound
occur; original manuscript bytes are unchanged.
