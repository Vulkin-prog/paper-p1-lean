# Effective sections and separate dense-target budgets

Source: `main_sections/exact_transfer.tex:129`; first paragraphs and separate component/singleton counts of `companion_sections/exact_transfer.tex:9–171`.

The effective linear-algebra and separate coordinate budgets in
the proof of article Lemma15.2 are now proved unconditionally.
Its status moves from not_started to in_progress. This is a
preparatory checkpoint: neither the actual dense-pair host count
nor its weighted mass estimate is complete. Numbered completed
coverage stays82/167; confirmed mathematical improvements stay120.

TwoTargetKernel works over an arbitrary field. Its relation space
is the genuine kernel of addition W x Y x Z -> ambient space,
with effective subspaces W,Y,Z. Disjointness W/Z proves that
projection to Y is injective; disjointness W/Y separately proves
that projection to Z is injective. There is no disjointness premise
between the two targets. Rank-nullity gives exactly the printed
dimension deficit, and the kernel dimension is at most the
minimum of the two target dimensions. No formal local rank is
substituted for an effective target dimension.

EffectiveLinearSections proves that every subspace of the range
of an actual linear map admits a genuine injective linear section.
Lifting the three entries of the relation kernel through these
sections preserves their exact sum-zero equation, together with
the separate injective target projections. The section exists
without injectivity or local full rank of the original quotient
map, and without any restriction on which effective subspace W
is chosen. No count of sections or subspaces is asserted.

TwoTargetWindowSections instantiates these facts on the literal
even-selection maps of the original source and target windows.
The source map is the sum of their actual square-class maps;
its range is precisely the sum of the source effective spaces.
Every W inside that sum has an exact source section, and each
actual target has its own even-selection section. The resulting
physical lift keeps every source and both target coordinate
blocks, every block has even total parity, and the full actual
prime-parity vector sum is zero. Both target projections into
their own L+1 physical coordinates remain injective. The actual
kernel dimension is at most L. No positivity, pair separation,
source distinctness, affine compatibility, or regular-window
assumption is required for these algebraic statements.

SimultaneousProjectionRegularization chooses ONE recovery
subspace for an arbitrary family of injective coordinate
projections. The same codimension loss bounds each projection's
distinct nonzero label count separately; it is not just a count
for their union. The recovery multiplicity and physical support
pool bounds hold on that same subspace. No number of target
projections is inserted into the loss. This theorem is then
applied to the two actual target lifts.

TwoTargetRegularization.uniform_regularization chooses its fixed
recovery order from s and xi BEFORE every source tuple, both
target centres, the length and W. It produces the actual three
sections and one shared M. Its codimension is at most xi*L/4;
each target separately has at least dim(R)-xi*L/4 distinct
nonzero coordinate labels. The source sum W is arbitrary inside
the fixed sources, including on irregular windows. Every exact
prime equation is retained by the physical lift. The actual
support pools have the proved fixed bound
supportBound(s+1,t,t-1), not an assumed arithmetic enumeration.

TargetComponentBudget proves finite geometric-free counting
facts for disjoint physical sets. Distinct nonzero target labels
are at most the number of monochromatic pieces meeting that
target. For any disjoint piece family C and target coordinate
set T, the exact budget is
  2*#pieces_meeting_T <= #T + #pieces_meeting_T_once.
Thus the number of singleton target occurrences is at least
2*m-#T, separately for each target. The proof counts actual
intersections; it does not require a graph without isolated
active coordinates or a count for a union of targets.

LabelClassPartition constructs the actual nonzero physical
label classes. They cover all active coordinates and are
pairwise disjoint and monochromatic. The number of classes
meeting a specified target equals its actual number of
distinct nonzero labels. Recovery multiplicity bounds every
class's size. TargetLabelsComponents links these finite sets
to actual coordinate projection rank and proves both component
and singleton budgets for any field. Finally the actual
physical_class_budgets and physical_class_size supply these
bounds on each of the two original targets of the shared M:
  m_j >= dim(M),
  2*dim(M) <= L+1+n_(1,j),
  every nonzero physical label class has size <=t-1.
The classes are explicitly constructed. No physical partition
or target count is supplied as an external premise.

The arithmetic coefficient enumeration for two free targets,
the removal of weak aligned alternatives, the two dense rank
strata and their final weighted summation still require proof.
The label-class partition alone is not claimed to supply the
component equations or the final geometric host bound.
Accordingly this checkpoint does not close article15.2 or15.3,
and it adds no numbered completion or new finding identifier.
There is no new literature assumption, kernel axiom, Paper C
port, dependency download or source-manuscript edit. Existing
geometric conditional properties and Palomar status are unchanged.

The result row records the full build, direct audit, all declaration references and exact proof commit.
