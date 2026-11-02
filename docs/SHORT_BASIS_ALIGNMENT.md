# Complete article short-basis theorem13.1

Source: article13.1, `p13:rig:short-basis`,
`main_sections/pair_rigidity.tex:88`, and its companion extraction proof
in `companion_sections/pair_rigidity.tex:159`. Status: **proved**.
Coverage76/167 (main28/73, companion48/94); confirmed findings78.
Original V1.6 manuscript bytes are unchanged.

## Exact statement and quantifier order

`ShortBasisTheorem.article_13_1` proves that, for each fixed0<a<=1,
there are positive KD(a),KS(a), chosen before every critical-band
width C, and a threshold N0(a,C), such that for all larger N, every
critical length L and every dyadic pair x,y, an actual complete-relation
subspace has

    dimension >= d_xy - (2/3)B log(1/a) - KD(a) B/sqrt(log B),
    basis total physical support <= KS(a) B^a log B/loglog B,
    B=L+1.

`ShortBasisActualSpace.Certificate.space` is an actual submodule of
`Affine.completeRelationCode`, with an actual basis. Its two physical
projections and its actual common square-class map are injective.
Every nonzero vector selects a nonempty even set in each block and
has nonzero common square class. `commonClasses_equal` identifies
that class with the second-block image; `commonClasses_mem_intersection`
places it in both actual square-class spaces.

The two physical blocks are disjoint formal copies, including when
their numerical windows overlap. Compatibility, admissibility,
nonalignment and non-overlap are unnecessary.

## Actual components, prime columns and deletion costs

Actual medium primes are z<p<=10B. Disjoint actual component vertex
sets imply the sum of literal column weights is at most the sum of
actual odd prime-occurrence counts. The actual interval maps and
multiple counts give total weight<=2B*sum(1/p)+2*#P.

Deleting components of size>M costs at most2B/(M+1); deleting columns
of weight>=3 costs at most one third of their actual total weight.
There is no extra factor M in this deletion count. Actual free
nontrivial components meet both blocks and carry a private large
prime, which proves both physical and actual class-map injectivity.

`MangoldtFloorBudget` proves the exact factorial/Mangoldt floor
identity. Actual Chebyshev and log-factorial bounds, and the actual
convergent nonprime prime-power sum, give a bounded weighted-prime
logarithm error. `LogarithmicAbelWindow` discharges all differentiability
and integrability obligations of the actual Abel identity and proves
the inverse-log error. Exact real cutoffs yield

    abs(sum_{B^a<p<=10B} 1/p - log(1/a)) <= K_window(a)/log B.

Thus `RetainedComponentAsymptotics.critical_retained_lower` gives an
actual retained count>=d_xy-(2/3)B log(1/a)-K_ret(a) B/log B, with
K_ret(a) before C. No prime-harmonic, PNT-remainder, retained-count or
summatory-error conclusion is an external premise.

## Actual incidence model and proved short-vector bound

Every retained binary medium-prime column has weight<=2. Add one
infinity row equal to the sum of all original rows. This augmentation
is injective and preserves the actual kernel. Actual endpoints realize
weight0 columns as loops, weight1 columns as infinity edges, and
weight2 columns as ordinary labelled edges. Parallel labels are kept.
`MediumPrimeIncidence` identifies this actual incidence kernel with
the literal medium-prime equations on selected physical occurrences.

`LabelledEdgeCore` proves actual vertex pruning with the exact edge-
deletion budget. If e>2d*n, a nonempty actual core retains incident
degree>=2d. Exact double counting bounds incidence sums by twice the
number of touching edge labels.

`ShortIncidenceRoutes` constructs actual short edge vectors with
boundary delta(root)+delta(vertex). If there is no nonzero kernel
vector of support<=2r+1, each edge inside the radius-r ball is exactly
the difference of its actual endpoint route vectors. The independent
single-edge vectors lie in their actual finite span, giving
#insideEdges<=#ball. `IncidenceBallGrowth` deduces d-fold ball growth,
then #ball(r)>=d^r. Therefore

    e>2d*n and n<d^r => an actual nonzero kernel vector of support<=2r+1.

No simple-graph conversion, BFS, girth, cycle-length or forest-rank
estimate is an unproved input. Loops and parallel edges are covered.

## Independent family, final kernel and actual basis

`GreedyShortKernel` chooses an actual nonzero witness coordinate in
each short vector and deletes only that coordinate. It vanishes on
all later vectors, proving independence. The actual spanned subspace
has dimension>=e-2d*n and an actual short basis.

Selecting one retained component has actual physical support exactly
its actual vertex set, of size<=M. Literal support unions give actual
physical support<=M*(2r+1) for this basis.

An actual right inverse on actual pivot columns gives a fundamental
basis of a kernel of s equations with support<=s+1. The actual small-
prime equations and two separate block parities impose at mostpi(z)+2
constraints. Every resulting vector is proved to be an actual complete
even relation; all prime ranges and nonprime coordinates are checked.
The final actual dimension and basis support bounds are

    dimension >= #retained - 2d*n - (pi(z)+2),
    physical support <= M*(2r+1)*(pi(z)+3).

The injective actual relation map is transported to its actual range
by a proved linear equivalence; the basis belongs to that actual range.
Both physical and common-class maps stay injective.

## Numerical choices and full asymptotic assembly

Set M=floor(log B), z=floor(B^a), n=#mediumPrimes+1,
d=floor(sqrt(log B)), r=Nat.log d n+1. For all sufficiently large B,

    n<d^r,
    2d*n <= 48 B/sqrt(log B),
    2r+1 <= 11 log B/loglog B,
    pi(z)+3 <= (32/a) B^a/log B.

All floors, real logarithms and integer powers are proved compatible.
The small-prime bound follows from the actual finite Chebyshev bound,
not an assumed prime-count estimate at B^a. The existing actual count
at10B gives n<=24B/log B. The two final constants may be chosen as

    KD(a)=K_ret(a)+48+32/a,
    KS(a)=352/a.

No optimization is claimed. The critical-band scale supplies a common
N0(a,C) before all variable lengths and starts. This closes every
finite and asymptotic input of the original theorem13.1.

## Recorded improvements

P1-MATH-0006 now propagates the constant order through full13.1:
multiplicative constants depend on a alone; only the threshold depends
on C. Historical validations of T9.2/T9.3 are preserved separately.
P1-MATH-0078 records the additional endpoint a=1. It is a scope
extension, with a coarse support bound there; the universal literal
physical support cap2B also holds. No a=0 or varying-a claim is made.
Neither manuscript is fully formalized. No Palomar registration occurs.

## Actual words and the common-curve application

The actual offset embedding sends a complete vertex index i to i-1,
including the predecessor offset-1. It is injective and lies in the
exact integer box[-B,B], B=L+1. The finite coefficient conversion and
actual domain map prove literal support equality, not just a bound.
Total word support equals actual physical support on the disjoint
formal block copies, even when numerical windows overlap.

The actual complete-relation subspace and basis transport to their
actual word image by a proved injective linear equivalence. Dimension,
both physical projection injectivities, evenness and support bounds
are preserved. Complete prime-parity equations prove the actual
selected natural product square; if that product is zero, its square
status is handled directly. At actual centers x,y>=1, exact label
casts identify word evaluation with that natural product's integer
cast. Thus all actual image words are square-valued, without a supplied
square-word conclusion.

`CurveFromCompleteRelations.common_curve` reindexes the actual basis
to a finite integer index and applies the proved common-curve theorem.
Its inputs are the actual complete-relation certificate, rank>=2,
physical basis support<=2q,1<=q<=B and the explicit point threshold.
It constructs the actual curve certificate, point, degree<=48q and
height<=(B+1)^(2472q). The actual grid lower bound uses the original
relation-space rank and exceptional constant6, with the proved image
projection injectivities and literal offset bounds.

This is a finite bridge. The critical asymptotic point-threshold
assembly, degree-one alignment and final nonaligned contradiction
remain open for13.6. BCN retains its separate named explicit input
and is not counted proved. Coverage76/167, confirmed findings79;
no new correction, external input, Paper C source, cache download,
manuscript-byte change or Palomar registration.

## Validation

Lean v4.36.0-rc2 full build passed (10519 jobs); actual axiom audit passed for all 5879 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 3594 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records are intact. Ubuntu available space: 15.94 GiB. Full article13.1 is proved: the actual complete-relation subspace and its actual transported basis have dimension >=d_xy-(2/3)B log(1/a)-KD(a) B/sqrt(log B) and literal physical support<=KS(a) B^a log B/loglog B. Both physical projections and the actual common square-class map are injective; every nonzero vector selects nonempty even sets in both formal blocks and has nonzero common class. All actual prime estimates, retained-component bounds, labelled incidence-core/route/ball arguments, witness deletion, final sparse kernel cuts, basis transport and logarithmic numerical estimates are internally proved. Constants KD(a),KS(a) precede C, with a C-dependent threshold; KS(a)=352/a is a safe explicit choice. P1-MATH-0006 propagates this constant order, and P1-MATH-0078 adds the endpoint a=1. No compatibility, nonalignment, non-overlap, short-cycle, sparse-basis or target-bound premise. Coverage76/167 (main28/73, companion48/94); findings78. No optimized constant, source-conclusion error, new external estimate, added Paper C source, dependency download, manuscript-byte change or Palomar registration.


Actual-word bridge checkpoint: Lean v4.36.0-rc2 full build passed (10531 jobs); actual axiom audit passed for all 5927 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 3643 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records are intact. Ubuntu available space: 15.92 GiB. Actual complete relations map injectively to actual offset words at i-1. Literal supports, total physical support, actual image bases, dimension and both projection injectivities are preserved. Actual prime-parity equations prove the selected product square, including the zero-product case, and exact label casts prove square-valued word evaluation at the actual centers. The actual relation certificate with rank>=2, support<=2q and the explicit point threshold constructs the actual common curve; its actual grid count uses the original relation-space rank and exceptional constant6. No separate square, arbitrary word basis, support correspondence or target grid count is assumed. Critical asymptotic threshold assembly, degree-one alignment and the final nonaligned contradiction remain open for13.6; BCN remains separately explicit and unformalized. Coverage76/167 (main28/73, companion48/94); confirmed findings79. No new mathematical correction, external input, Paper C source, cache download, manuscript-byte change or Palomar registration.


## Subsequent degree-one branch

The actual degree-one common-curve branch is now proved by two bounded integer-grid points, at actual relation rank>=9. No line height/sign or extra root-pairing input is required. The critical threshold assembly, BCN specialization and final13.6 contradiction remain open. See [the current finite nonaligned scope](NONALIGNED_RANK_ALIGNMENT.md).


## Completed subsequent critical assembly

The actual support and critical logarithmic budgets now discharge every common-curve threshold in13.6. The final nonaligned rank bound, actual finite-pair maximum, literal limsup and strict half-window gap are proved under the separately named integer BCN input. All remaining unformalized scope is explicit. See [the conditional alignment](NONALIGNED_RANK_ALIGNMENT.md).
