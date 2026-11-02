# Exact actual fourth factorial cumulant

Source: main 16.1, its finite displayed identity and separate arithmetic remainder estimates. Status: **in progress** for the sharp arithmetic comparisons.

The complete finite fourth-factorial-cumulant identity in the proof of
main 16.1 is now checked for the actual heterogeneous original count.
Writing C2=sum_(|e|=2)c(e), it is exactly

    kappa4 = 24*sum_(|I|=4)c(I) - 12*C2^2
             -24*sum_(|T|=3)c(T)*sum_(x in T)p_x
             +24*sum_(e={i,j})(p_i^2+p_i*p_j+p_j^2)*c(e)
             -6*sum_x p_x^4.

Every repeated-index term and every actual marginal is retained. The empty
ground set, zero marginals and incompatible families are included. Removing
all zero-marginal sites is proved to preserve this actual cumulant exactly.
No independent-indicator, regularity, positivity or arithmetic hypothesis is
needed for the finite identity, and no analytic logarithm is used.

The algebraic proof is stronger in scope: it works in any commutative ring
for coherent joint and centered data q,c with c(empty)=1, zero singleton
coefficients and the finite uncentering identity. An exact incidence
bijection between a set with a marked subset and two disjoint subsets gives
the full all-order cardinality convolution. Its order-2,3,4 specializations,
the two-site deletion formulas and the independent quartic identity supply
the displayed formula. For the actual model, the coherence hypothesis is
discharged by the already proved exact infinite uncentering expansion.
It is not an assumed cumulant formula or asymptotic bound.

This weaker algebraic setting is recorded as confirmed improvement
P1-MATH-0089. It applies to the finite displayed identity in the proof of
main 16.1, not to the source arithmetic estimates that follow it.
The original manuscript bytes are preserved for later integration.

A separate first vanishing bound under the existing explicit BCN premise
is proved for the actual full original count:

    |kappa4(Z_N)| <= N^(-1/2+eta)

at every fixed critical-band width and eta>0. With F_r the actual factorial
moments, mu the actual mean and d_r=F_r-mu^r, the checked decomposition is
kappa4=d_4-4*mu*d_3+6*mu^2*d_2-3*d_2^2. The fixed moment estimates and
bounded mean prove the bound, with a small fixed exponent selected before N.
This does not assume a fourth-cumulant estimate.

The source comparisons kappa4=24*K4+O(N^(-3/2+eta)),
K4=K4_positive+O(N^(-3/2+eta)), and their positive quartic consequence
remain open. Main 16.1 therefore moves from not_started to in_progress;
main 6.4 remains in progress. No numbered result is counted complete.
Coverage stays 77/167 (main 28/73, companion 49/94); confirmed improvements
increase from 88 to 89. No new external input, axiom, dependency download,
source-byte change or Palomar registration is introduced.

Verified Lean v4.36.0-rc2 full build (10827 jobs), actual Audit.lean kernel audit (6699 declarations; only propext, Classical.choice, Quot.sound), 4416 direct ledger/finding declaration checks, 138 source manifest entries and all 167 original statement hashes. Ubuntu root free space: 15.42 GiB. Exact disjoint-subset incidence, all-order centered cardinality convolution and the complete heterogeneous quartic identity hold over a commutative ring. The original infinite-model specialization and zero-marginal restriction are proved unconditionally. The separate half-power fourth-cumulant decay uses the existing ordinary explicit BCN premise. Source sharp connected-quartic comparisons remain open. Main 16.1 and 6.4 stay in progress. Confirmed improvement P1-MATH-0089 concerns only the generalized finite identity. Coverage 77/167; improvements 89.


## Two pair components and the complete repeated-index remainder

Two further parts of main 16.1 are now checked on the actual original
model: nonconnected quartic component factorization and the complete
repeated-index error at the source 3/2 scale under explicit BCN.

A finite four-element partition without singleton parts is either one
block or exactly two two-element parts. Applied to an actual full-support
relation, this classifies the canonical effective-space components.
Nonzero actual centered activity forces every local marginal to be positive;
this is proved from exact zero-marginal cancellation, not assumed.
Consequently every nonconnected actual four-site family I with c(I)!=0
has actual disjoint two-site subsets e,f such that

    e union f = I,
    rho(I) = rho(e)+rho(f),
    c(I) = c(e)*c(f).

The subsets are obtained from the canonical effective-space partition;
finite-part reindexing identifies their moments and nullities exactly.
The factorization and nullity additivity use the checked canonical direct
partition, actual infinite-model moment factorization and exact part
images. No arithmetic or BCN premise is needed for this finite geometry.
This existence result is not yet an identification of the sum over all
unordered direct edge pairs with the source D22 population.

Write C2 for the actual signed pair activity and C4 for the signed sum over
ALL four-element families. The exact heterogeneous identity gives

    kappa4 - 24*C4 + 12*C2^2 = repeatedRemainder.

For any nonnegative individual marginals p_x bounded by P, a checked finite
bound retains every term:

    |repeatedRemainder| <= 72*P*A3 + 72*P^2*A2 + 6*P^3*mu,

where A2,A3 are the full actual absolute centered activities and mu=sum p_x.
The triple sum, two-site quadratic weights and diagonal fourth powers are
bounded separately before taking their total absolute value. The finite
bound needs no asymptotic estimate.

For every critical length and every G contained in the dyadic block, the
proved marginal cap P<=K/N, bounded actual mean, BCN-dependent half-power
A3 and pair-activity bound yield

    |kappa4(G)-24*C4(G)+12*C2(G)^2| <= N^(-3/2+eta)

for every eta>0, eventually uniformly in G. The pair-weight contribution
actually costs N^(-5/2+eta), and the diagonal contribution costs N^-3.
The constants and thresholds are chosen before N. No target fourth-cumulant
comparison is assumed, and no incompatible family or repeated index is
silently removed.

This proves the complete repeated-index precision used in the source
argument, conditional only on its already inventoried ordinary explicit
BCN premise. The remaining work includes the exact unordered direct-pair
population decomposition, its comparison with C2^2/2, and the sharp
incompatible/connected quartic estimates. No claim kappa4=24*K4 with the
source error is made yet. Main 16.1 stays in progress; coverage remains
77/167 (main 28/73, companion 49/94), improvements remain 89.
No new external input, axiom, dependency download, source-byte change or
Palomar registration is introduced.

Verified Lean v4.36.0-rc2 full build (10847 jobs), actual Audit.lean kernel audit (6728 declarations; only propext, Classical.choice, Quot.sound), 4445 direct ledger/finding declaration checks, 138 source manifest entries and all 167 original statement hashes. Ubuntu root free space: 15.39 GiB. The exact nonconnected quartic pair factorization, nullity additivity and finite repeated-index bound are unconditional. Under the existing ordinary explicit BCN premise, the full repeated remainder relative to 24*C4-12*C2^2 is at most N^(-3/2+eta) uniformly over all dyadic subgrounds. The exact unordered direct-pair population and its sharp product/incompatible comparisons remain open; main 16.1 stays in progress. Coverage 77/167; confirmed improvements 89.


## Per-site pair rows and repeated/shared-vertex products

The per-site actual pair-row estimate used in the proof of main 16.1
is now proved unconditionally. For every eta>0, uniformly over critical
lengths, all G contained in the dyadic block and every source x in that
block, eventually

    sum_(y in G, y!=x) |c({x,y})| <= p_x*N^eta.

The local probability p_x is its exact actual marginal. No common-marginal
replacement, source compatibility assumption or positive-marginal premise
is used; if p_x=0, the whole row vanishes exactly.

The proof transports the already checked fixed-source conditional mass
step to original run events. Boolean indicator products are proved to
depend only on tuple support, even for tuples with repetitions. Thus the
source-excluding row is obtained without dropping diagonal terms from an
identity that needed injectivity. The actual joint row, including y=x,
is uniformly at most p_x*N^eta. For distinct x,y,

    |c({x,y})| <= q({x,y})+p_x*p_y,
    |c({x,y})| <= p_x.

Actual marginals lie in [0,1]; the covariance bounds follow from the
actual joint-mass antitonicity. The uniformly bounded actual mean absorbs
the product-marginal row. All orders and thresholds are fixed before N.
This row estimate does not use BCN.

An exact finite incidence identity proves that summing every absolute
row counts every unordered edge twice. If all p_x<=P and the absolute
row at x is at most B*p_x, the actual finite product costs satisfy

    sum_e c(e)^2 <= P*A2,
    sum_x (sum_(y!=x)|c({x,y})|)^2 <= 2*B*P*A2.

These sums retain repeated edges and bound all pairs of incident edges;
no graph degree cap or independence of the filtered indicators is used.
The second bound intentionally includes diagonal and both ordered
neighbor choices, so it is an upper bound for the narrower distinct
shared-vertex contribution in the source argument.

Under the existing explicit BCN premise, insert the checked global
pair-activity estimate, P<=K/N and the unconditional row bound B=N^eta.
For every epsilon>0, both the actual repeated-edge square cost and full
star-square cost are eventually at most N^(-3/2+epsilon), uniformly in
every dyadic subground. This supplies the source remainder precision for
these overlapping-edge cases. The source's sharper intermediate 5/3
exponent is not asserted.

The disjoint non-direct edge-pair population and the full direct-pair
product comparison remain open. Main 16.1 therefore remains in progress.
No numbered result or new mathematical finding is counted complete.
Coverage stays 77/167 (main 28/73, companion 49/94); improvements stay 89.
BCN is an ordinary explicit argument used only in the global pair-activity
step. No new external input, axiom, dependency download, manuscript-byte
change or Palomar registration is introduced.

Verified Lean v4.36.0-rc2 full build (10857 jobs), actual Audit.lean kernel audit (6746 declarations; only propext, Classical.choice, Quot.sound), 4463 direct ledger/finding declaration checks, 138 source manifest entries and all 167 original statement hashes. Ubuntu root free space: 15.38 GiB. Actual per-site joint/absolute rows, repeated tuple support and finite repeated-edge/star-square bounds are unconditional. The source-scale N^(-3/2+epsilon) repeated/shared-vertex product costs use the existing ordinary explicit BCN premise. Disjoint non-direct edge products, the full direct-pair comparison and sharp connected/incompatible quartic estimates remain open; main 16.1 stays in progress. Coverage 77/167; confirmed improvements 89.


## Exact pair-product reduction and the remaining arithmetic cost

The actual squared-pair comparison in the proof of main 16.1 has been
reduced to an explicitly defined finite population of disjoint non-direct
edge pairs. Write D for the sum of products c(e)c(f) over unordered,
disjoint, distinct two-site edges with rho(e union f)=rho(e)+rho(f).
Write B for the sum of |c(e)c(f)| over the corresponding disjoint pairs
where this nullity equality fails. Both are literal finite original-model
sums, including zero marginals and incompatible edge data.

The exact arbitrary-weight identity separates the diagonal square term
from all omitted unordered edge products. A finite star cover and the
nonnegative elementary-symmetric inequality prove that all unordered
shared-vertex products have weight at most half the sum of squared rows.
Membership in the overlap population is proved equivalent to non-disjointness
for every distinct pair of actual two-site edges. Thus, without arithmetic
hypotheses,

    |C2^2/2 - D| <= (repeatedSquare + starSquare)/2 + B.

The checked source-scale repeated-edge and star-square bounds then give,
under the already explicit ordinary BCN premise, for every epsilon>0,

    |C2^2/2 - D| <= B + N^(-3/2+epsilon)

eventually uniformly over all critical lengths and dyadic subgrounds.
No estimate on B is assumed or asserted. The reduction is not counted as
having proved the source D22 comparison. Identifying D with the full
nonconnected quartic sum is also still open. Main 16.1 remains in progress;
coverage stays 77/167 (main 28/73, companion 49/94), improvements stay 89.
No new external input, axiom, dependency download, source-byte change or
Palomar registration is introduced.

Verified Lean v4.36.0-rc2 full build (10865 jobs), actual Audit.lean kernel audit (6760 declarations; only propext, Classical.choice, Quot.sound), 4477 direct ledger/finding declaration checks, 138 source manifest entries and all 167 original statement hashes. Ubuntu root free space: 15.37 GiB. Exact arbitrary signed-weight square comparison, finite overlap cover and actual direct/non-direct pair partition are unconditional. The N^(-3/2+epsilon) overlap remainder uses the existing ordinary explicit BCN premise; the literal disjoint non-direct cost is retained without an assumed estimate. Main 16.1 stays in progress, coverage 77/167, improvements 89.


## The full unordered direct-pair identity is proved

The complete finite direct-pair population identity in main 16.1 is now
proved on the original infinite model. For disjoint blocks e,f, the exact
cross-block identity is

    rho(e union f) = rho(e)+rho(f)+dim(span(e) intersection span(f)).

Consequently nullity additivity is equivalent to disjointness of the actual
effective block spaces. The proof only needs the finite local spaces; the
ambient square-class space need not be finite dimensional. A checked
relation cut constructs the actual two-part direct partition. Exact
finite-subtype preimages preserve the original blocks, their spaces and
their moments. For arbitrary nonempty disjoint direct blocks, not just
pairs, c(e union f)=c(e)c(f). Zero marginals are included by exact
cancellation; no compatibility assumption is introduced. Such a genuine
two-block direct family is nonconnected.

A refinement without singleton parts cannot split two-element blocks.
A nonzero quartic coefficient has an actual full-support relation, so any
direct two-pair split agrees with the canonical relation partition. This
proves uniqueness of the unordered split on the nonzero population.
Every nonconnected nonzero quartic coefficient has such a split by the
already checked component classification. An exact finite bijection
between nonzero summands, with zero terms retained in both full sums,
therefore proves

    sum_(all four-site I)c(I) = K4 + D,

where K4 is the actual connected quartic sum and D is the literal unordered
disjoint direct-pair product sum from the preceding checkpoint. This is an
identification of the actual populations, not a freely supplied D22 formula.
The finite geometry and probability identity are unconditional for L>0.

Combining this identity, the exact heterogeneous fourth-cumulant formula,
the checked repeated-index error and the checked overlap comparison gives,
under the existing ordinary explicit BCN premise, for every epsilon>0,

    |kappa4(G)-24*K4(G)| <= 24*B(G)+N^(-3/2+epsilon),

eventually uniformly over critical lengths and every dyadic subground.
Here B is exactly the sum of |c(e)c(f)| over disjoint two-site edge pairs
with non-direct total spaces. It remains in the conclusion with its
literal definition; no target bound on B is assumed or claimed.
The sharp estimate of B, the incompatible connected quartic activity
bound and the full source conclusions remain open. Main 16.1 remains
in progress; coverage 77/167 (main 28/73, companion 49/94), improvements 89.
No new external input, axiom, dependency download, source-byte change or
Palomar registration is introduced.

Verified Lean v4.36.0-rc2 full build (10881 jobs), actual Audit.lean kernel audit (6790 declarations; only propext, Classical.choice, Quot.sound), 4507 direct ledger/finding declaration checks, 138 source manifest entries and all 167 original statement hashes. Ubuntu root free space: 15.35 GiB. Cross-block nullity, direct-space equivalence, zero-marginal block factorization, canonical uniqueness and the complete actual disconnected quartic/direct-pair sum identity are unconditional for L>0. The actual connected fourth-cumulant comparison has a checked N^(-3/2+epsilon) remainder under existing explicit BCN, with 24 times the literal disjoint non-direct product cost retained. The sharp estimate of that cost and the incompatible connected quartic bound remain open. Main 16.1 stays in progress; coverage 77/167, improvements 89.


## A complete comparison at the weaker N^-1 scale

The literal remaining disjoint non-direct pair cost B admits the
unconditional finite bound B <= A2^2/2. Under the existing ordinary explicit
BCN premise, the proved global pair-activity estimate gives

    B(G) <= N^(-1+epsilon),
    |kappa4(G)-24*K4(G)| <= N^(-1+epsilon),

eventually uniformly in all critical lengths and dyadic subgrounds. The
second statement is a proved complete comparison with the actual connected
quartic sum; it uses the already checked canonical population identity.
This is weaker than the source 3/2 precision and is not counted as completing
main 16.1. Its stronger source-scale reduction with the literal cost B remains
available separately. The sharp disjoint non-direct cost and incompatible
connected quartic bound remain open. Coverage stays 77/167 (main 28/73,
companion 49/94), improvements stay 89. No new external input, axiom,
dependency download, source-byte change or Palomar registration is introduced.

Verified Lean v4.36.0-rc2 full build (10887 jobs), actual Audit.lean kernel audit (6797 declarations; only propext, Classical.choice, Quot.sound), 4514 direct ledger/finding declaration checks, 138 source manifest entries and all 167 original statement hashes. Ubuntu root free space: 15.34 GiB. The unique canonical original finite-set decomposition and all direct-partition joint/centered products include zero marginals and need no positivity premise. The literal non-direct pair cost is at most A2^2/2; the complete actual connected fourth-cumulant comparison at N^(-1+epsilon) uses the existing explicit BCN premise. The sharper source N^(-3/2+epsilon) comparison remains open. Main 4.4 stays proved; main 16.1 stays in progress. Coverage 77/167, improvements 89.
