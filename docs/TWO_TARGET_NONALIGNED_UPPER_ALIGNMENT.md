# Upper nonaligned dense-pair cardinality from actual target singletons

Source: the second dense-pair stratum in `companion_sections/exact_transfer.tex`, supporting `main_sections/exact_transfer.tex:129`.

The complete UPPER nonaligned cardinality stratum in article15.2
is now proved under the existing explicit ordinary-surface and
normalized-curve properties. Actual nonaligned dyadic pairs
whose effective relation dimension is at least (1/2+delta)*L
have O(N^epsilon) cardinality, uniformly over arbitrary fixed
sources and W inside their effective sum and disjoint from each
target separately. Together with the preceding lower count,
this verifies both nonaligned cardinality strata. Weak aligned
pairs and the final weighted and source-restricted statements
remain open, so main15.2 stays in_progress and numbered proved
coverage stays82/167. P1-MATH-0122 records the direct whole-label
class proof of these nonaligned strata, bringing confirmed
mathematical improvements to122.

CoefficientDegreeOneHostCount pools the actual degree-(a,1)
integer-root systems over any common small positive coefficient
list of fixed polynomial height. Every pattern may have its own
positive degree a, but within one selected system that degree
is fixed. The singleton offset in the second target is actually
constructed from its one-element set; within-target disjointness
proves the singleton offsets are distinct. The already proved
literal degree-one count then applies. Ordinary affine-curve
counting is obtained by the proved ordinary_specialization of
the normalized-curve property, rather than introduced as another
external premise. A positive fixed equation count is chosen
before all geometric inputs, coefficient lists and hosts.

TwoTargetSingletonLabels identifies each physical target's
singleton classes with their distinct nonzero labels. It proves
the exact image identity, cardinality equality and membership
criterion for these actual labels. The previous physical
projection budget therefore becomes, separately in each target,
  2*dim(P)<=L+1+#singleton_labels_j.
The classes and their cardinalities are literal physical sets.

TwoTargetSingletonSelection proves the actual finite dichotomy.
With class size at most K, if each target has at least
(K+1)*k+2 singleton labels, either one orientation supplies k
distinct mixed labels of one common positive other-target
degree, or two pure labels are available in EACH target.
The fixed type is chosen by a finite pigeonhole argument on
degrees0,...,K. Its degree is positive because the selected
classes really meet the other target and k>=1. No type,
population bound or pure/mixed alternative is assumed.

TwoTargetSingletonClassData constructs both orientations of
the actual degree-one square system. Its coefficients are the
same full squarefree target-product kernels from the source-only
list, and its offset sets are those of the actual classes.
The product equation is transported exactly, including the
commutative product reordering needed when the first target is
the singleton side. Degree, disjointness, bounded offsets and
all integer roots are internally proved. One threshold precedes
every actual target pair, subspace, number of equations and
choice of the singleton orientation.

CompressedAlignmentSymmetry proves the exact source alignment
relation symmetric for a fixed width multiplier. Consequently
TwoTargetNonalignedSingletonCount applies the same geometric
bound to either target orientation, with an explicit injective
integer host map. Both orientations share one constant and
threshold. A pair's positive other-target degree and actual
recovery subspace may vary with that pair; the common source
coefficient budget remains uniform. Its result is O(N^epsilon)
for every actual nonaligned host set with the selected mixed
singleton configuration.

TwoTargetNonalignedUpperCount.uniform_pairs closes the entire
upper nonaligned count from the genuine dimension hypothesis.
Choose the recovery parameter from s and delta before every
source and target. Regularization retains
dim(P)>=d-delta*L/4. For d>=(1/2+delta)*L the separate target
budgets imply at least (3*delta/2)*L-1 singleton labels in EACH
target. At one common critical length threshold these exceed
t*k+2, which is precisely the finite selection threshold for
K=t-1. The proved dichotomy gives one of the two orientations
of the mixed degree-one branch or the unconditional pure
branch. A finite cover of the actual host set by these three
actual populations gives O(N^epsilon), with no enumeration of
subspaces, sections, deletion patterns or prime assignments.

The effective kernel dimension is used throughout; no full
physical local kernel is added. Irregular windows, overlapping
targets and arbitrary W inside the actual source sum are
allowed. The nonalignment condition is retained literally.
These results do not remove the small aligned curves for weak
aligned pairs. Nor do the cardinality estimates themselves
establish the weighted sum in the source lemma. Both tasks
remain explicitly open in the result ledger.

The exact upper-branch external properties are
UniformOrdinarySurfaceCover.UniformCover k (t-1) and
UniformNormalizedCurvePointCount.UniformBound (k+3) M for all M.
These are the previously recorded P1-GEO-ORDINARY-SURFACE-COVER
and P1-GEO-NORMALIZED-CURVE-UNIFORM. The lower mixed branch
retains the existing chosen-source surface property. There is
no new unformalized literature input or kernel axiom, Paper C
port, dependency download or original manuscript-byte edit.
Palomar remains deferred.

The JSON result row and finding122 record full validation and its exact proof commit.
