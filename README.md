# P1 — Lean formalization

Formalization project for **Sharp Poisson approximation and second-order
correction for long multiplicative runs**, main article and technical companion,
by **Brice Pouly**, working version **1.6, 31 October 2026**.

**Status: active formalization, 78 / 167 numbered results proved.**

The actual original count and its retained modification now converge to Poisson in total variation under the explicit BCN premise; the sharp source rates remain open. Exact fourth-cumulant component identities and unconditional weak, irregular and incompatible pair bounds are proved. In particular, the actual absolute pair activity is asymptotic to half the actual second factorial cumulant, without BCN or a complete pair profile. The contact activity bound at every fixed order now holds unconditionally on every dyadic subground, including irregular starts and zero marginals. The activation probability of the actual principal edge family now has the unconditional exponent -2/3, with any fixed epsilon margin. The planar normal budget T20.4 is now proved with improved constants and an integer-fibre argument. The project records **95 confirmed mathematical improvements**. See [current status](docs/FORMALIZATION_STATUS.md), [the activity alignment](docs/FIXED_ABSOLUTE_ACTIVITY_ALIGNMENT.md) and [the mathematical change log](docs/MATHEMATICAL_CHANGELOG.md).

Article13.1 now has a complete actual short-basis construction, with
both physical projections and the common square-class map injective.
All arithmetic, incidence-growth and logarithmic estimates are proved.
The support constant352/a is explicit; multiplicative constants precede
C, and the endpoint a=1 is included. Article13.2 and proposition13.3
are also complete. See [the short-basis alignment](docs/SHORT_BASIS_ALIGNMENT.md).

Article13.6 now has its complete actual nonaligned-rank reduction, including the finite-pair maximum, literal limsup and a strict half-window gap, **conditional on the explicitly unformalized field-polynomial BCN bound**. All critical threshold, degree-one alignment and integer/rational presentation steps are proved internally. This adds no proved numbered coverage. See [the conditional scope](docs/NONALIGNED_RANK_ALIGNMENT.md).

Article13.8 is also conditional on that same BCN input: all triple rank bounds and the actual maximum joint probability are proved. The probability estimate extends to every family of at least two centers, and the stronger nonaligned-triple rank bound needs no compatibility. See [the triple alignment](docs/TRIPLE_RANK_ALIGNMENT.md).

Companion T17.2 is complete: the actual retained-reference identity and ordinary l1 bound use the literal sourceF_r,G_r, exact binomial counts, all zero conventions and weighted infinite sums. A finite heterogeneous extension is also proved. See [the retained-reference alignment](docs/RETAINED_REFERENCE_ALIGNMENT.md).

The analytic part ofT17.4 now has an explicit finite signed-measure conversion for0<=p<=1, with no convolution logarithm. The actual critical reference is controlled by4|beta-c2|+K_C*(N^(-2)+|c2|/N); the arithmetic covariance scale remains open. See [the conversion scope](docs/POISSON_CHARLIER_CONVERSION_ALIGNMENT.md).

Main15.1 now has its full finite heterogeneous analytic bound with the universal constant16exp(2), valid throughout0<=p_i<=1 with no mean bound. The actual run reference uses the exact mean and second cumulant, and has uniform error K_C*(N^(-2)+A_2/N). The arithmetic pair-activity rate remains open. See [the exact scope](docs/HETEROGENEOUS_CONVERSION_ALIGNMENT.md).

The actual Hermite probability reference is now constructed on an independent Poisson product space. Its exact mean, exponential moments and explicit quadratic-reference comparison are proved. The actual second cumulant is eventually positive without BCN; exact-parameter Hermite and quadratic probability status is now proved under the same explicit BCN input used for the coarse upper bound. The source count-law rates remain open. See [the reference scope](docs/HERMITE_REFERENCE_ALIGNMENT.md).

Companion T22.7 is complete: the actual infinite replica formula, the
uniform colored conditional target sum and every fixed positive weighted
replica moment are proved. Repeated centers and arbitrary ordered tuple
subfamilies are included. See
[the complete replica alignment](docs/COLORED_REPLICAS_ALIGNMENT.md).
Compatible centered coefficients are now proved nonnegative at every
finite order. The exact incompatible-triple cancellation and activity
comparisons are proved; their remaining arithmetic bound stays open.
See [the triple activity scope](docs/TRIPLE_ACTIVITIES_ALIGNMENT.md).
Main Proposition 6.3 is complete: actual conditional affine sums,
ordered-distinct extension-family propagation, and the full fixed-order
local-defect/contact mass bound are proved on the original infinite model.
Seed placement at every tuple position is included. See
[the complete propagation alignment](docs/FIXED_SOURCE_PROPAGATION_ALIGNMENT.md).
Main Proposition 6.2 is now complete: the actual large-rank-loss targets
are uniformly bounded by N^epsilon after any fixed source tuple, even
with repeated or overlapping sources. The proof constructs and counts
actual prime groups, two disjoint physical classes and their coefficients.
See [the complete dense-target alignment](docs/DENSE_TARGET_ALIGNMENT.md).
Companion T4.1 now uses only two disjoint square equations, with arbitrary
nonzero integer coefficients. The arithmetic proof removes the need for
the source Pila input at this step. See
[the complete square-equation alignment](docs/DISJOINT_SQUARE_EQUATIONS_ALIGNMENT.md).
Companion T19.9 constructs one actual family of compatible connected
regular components with quadratic nullity and no good pair. Both size
and nullity coefficients tend to 6 log(2)/17, and the centered mass
has the explicit relative error 2/sqrt(L). The original infinite-model
moments and the order of all asymptotic quantifiers are retained. See
[the complete component alignment](docs/QUADRATIC_COMPONENT_ALIGNMENT.md).
The support count in main 3.2 now has the stronger exponent 1+epsilon,
including local kernels, contacts and equal centres. Its weighted
nonaligned residual remains open. The actual second factorial moment
is bounded unconditionally by N^epsilon for each fixed epsilon. The bounded seed and fullT19.4 growing-order bound are now proved under the same explicit BCN input as13.6; they add no proved coverage. See [the exact pair-host scope](docs/PAIR_HOST_COUNT_ALIGNMENT.md).
Main Lemma 14.2 proves the sharp rational overlap bound for every integer
triple in the source range. The unique extremal triple is (10,12,15),
and all other primitive triples have the sharp smaller bound 11/18.
See [the complete overlap alignment](docs/RATIONAL_TRIPLE_OVERLAP_ALIGNMENT.md).
Companion T12.1 now proves the actual retained class is hereditary, has a unique dependent pair, and has boundary nullity at most 4L/3+1. See the
[complete retained-class alignment](docs/RETAINED_CLASS_ALIGNMENT.md).
Companion T12.2 now proves the actual large-boundary mass estimate with the source least cutoff, and strengthens its decay to N^(-5/3). See the
[complete large-boundary alignment](docs/LARGE_BOUNDARY_TAIL_ALIGNMENT.md).
The exact least cutoff also has the source asymptotic 3*log(N)/loglog(N) and its eventual K<=L/4 range. See the
[cutoff asymptotic alignment](docs/BOUNDARY_CUTOFF_ASYMPTOTICS_ALIGNMENT.md).
Both prescribed quadratic-kernel counting branches and the final affine count are proved uniformly, with a stronger capped exponent. T5.1 stays in progress solely for a qualification of its printed exact exponent comparison. See the
[full counting and range alignment](docs/QUADRATIC_KERNEL_COMPLETE_COUNTS_ALIGNMENT.md).
Both actual T5.2 counts are proved on all fixed comparable positive intervals.
The prescribed-divisor estimate also holds cumulatively
below a kernel-size bound; both counts accept fixed polylogarithmic widths.
The fixed-kernel assertion additionally permits odd degrees. See the
[complete split-product alignment](docs/PRESCRIBED_SPLIT_PRODUCT_ALIGNMENT.md).
Article 9.1 and its actual Lᵛ consequence are proved, including every fixed
comparable positive interval, arbitrary subsets of centres and fixed
polylogarithmic widths. The choice of c is explicit. See the
[complete moment alignment](docs/SHORT_MOMENT_ENUMERATION_ALIGNMENT.md).
Corollary 9.2 is also proved, including the complete motif enumeration.
Its old-space hypothesis can be reduced to O(log N) generators with arbitrary
value heights. See the [complete projection alignment](docs/SHORT_OLD_SPACE_PROJECTION_ALIGNMENT.md).
Companion T6.1 now counts the actual two-small-kernel centres, with the stronger
uniform real-cap bound Q*N^epsilon. The threshold is independent of Q, the cutoff
need not exceed the block diameter, and fixed polylogarithmic widths are allowed.
See the [complete two-small-kernel alignment](docs/TWO_SMALL_KERNEL_ALIGNMENT.md).
Companion T6.2 now constructs and counts the actual deterministic smooth-modulus
exceptional set. Only t+26 selected values are needed, and squarefree smooth parts
and moduli suffice. See the [complete smooth-modulus alignment](docs/LARGE_SMOOTH_MODULUS_ALIGNMENT.md).
Companion T6.3 now constructs the actual received certificates and proves both
incoming and outgoing degrees. Its complete scope extends to A>1 and both
directions share one finite subset bound. See the [complete certificate alignment](docs/ANCHOR_CERTIFICATE_ALIGNMENT.md).
Main Theorem 10.1 is proved by the full simultaneous induction and actual
stage counts, with arbitrary finite effective blocks, full old spans and
actual value-height/critical-width alignment. A constant short-selection cap
and full squarefree kernels suffice in its iteration. See the
[complete half-count alignment](docs/CONDITIONAL_HALF_COUNT_ALIGNMENT.md).
Corollary 10.3 now counts actual dependent block pairs, including equal
centres, for all fixed logarithmic widths. See the
[complete pair-count alignment](docs/DEPENDENT_BLOCK_PAIRS_ALIGNMENT.md).
The half-count also holds under separate coordinate-wise relative relations.
Main Corollary 10.2 now counts actual unordered connected and primitive
original-window families and their independent mass, retaining every exact
heterogeneous marginal. See [the relative extension](docs/RELATIVE_PARTICIPATION_ALIGNMENT.md)
and [connected-family scope](docs/CONNECTED_FAMILY_ALIGNMENT.md).
Companion T1.14 now has the stronger exponent r-s/2, with actual fixed
offset/dilation record counts, from the complete conditional half-count.
See [the complete support alignment](docs/SEVERAL_BLOCK_RELATION_ALIGNMENT.md).
The exact order-dependent exception and logarithmic rate in T19.4 are
proved. Its growing moment bound retains the actual initial second
factorial moment; the uniform bound for that moment remains open.
See [the precise remaining scope](docs/ORDER_DEPENDENT_BRANCHING_ALIGNMENT.md).
Companion T1.9 now covers the full enlarged geometric alignment, including
zero exact units and both orientations, with its fixed-height enlarged-prime
rate. The earlier one-unit coverage error and its subsequent closure are
retained in the [scope audit](docs/FORMALIZATION_SCOPE_AUDIT.md).
See the [complete alignment](docs/ALIGNED_RESIDUAL_RANK_ALIGNMENT.md).
Companion T1.11 and T2.6 prove the actual additional target rank from
literal alignment with the compressed source, including internal target
defects, old prime bits, both source orientations and explicit polynomial
source exceptions and target counts. One source unit suffices for this
rank conclusion. See the [complete target-rank alignment](docs/ALIGNED_TARGET_RANK_ALIGNMENT.md).
The exact leading coefficients are 1/3 for channel 2:3 and 1/2 for 3:4;
the universal finite coefficient bound 2/3 is attained in channel 8:9.
This coefficient computation does not assert optimality of rank or Palm bounds.
Article Proposition 13.7 is proved from the uniform residual, including
the exact height-one contact case. The same bounds hold for full pair
deficiency, retaining local defects. See the [alignment note](docs/KNOWN_ALIGNMENT_RANK_ALIGNMENT.md).
The finite channel sums now have checked even-selection counts,
predecessor-signed placements and both exact leading-channel formulas.
Actual dyadic translations now have an exact interval bijection and
error at most 6B for both orientations, uniformly up to height B^3.
See the [translation checkpoint](docs/SOURCE_TRANSLATIONS_ALIGNMENT.md).
The weighted canonical-pattern translation aggregate now retains the
signed main term N*w*S with explicit error <=6B*U. See the
[weighted checkpoint](docs/CHANNEL_WORD_HOSTS_ALIGNMENT.md).
The private pair intersection now has an explicit linear parameterization
by actual even unit selections, including zero and one unit. See the
[coefficient equivalence](docs/EXACT_UNIT_INTERSECTION_ALIGNMENT.md).
The actual private pair covariance is now p^2 times the signed sum of
nonzero even unit selections, including probability-zero pairs. The
paired characters are proved to be the literal predecessor signs. See
the [actual probability bridge](docs/PRIVATE_UNIT_COVARIANCE_ALIGNMENT.md).
Actual nonzero even unit selections are now bijective with their unique
endpoint-selected words. Their signed sum at a fixed pair is proved to
equal the sum of A_d times the two literal placement signs. See the
[local word enumeration](docs/SELECTED_UNIT_WORDS_ALIGNMENT.md).
The actual dyadic signed unit sum is now identified with the global
pattern/source aggregate. Both orientations give main term N*w*S and
error <=6B*U, uniformly through reduced height B^3. See the
[dyadic Fourier aggregate](docs/DYADIC_UNIT_FOURIER_ALIGNMENT.md).
The actual nonprivate normalized hosts now have an explicit finite
defect injection and an N^(1/2+epsilon) bound for each fixed channel.
Their rational-unit weights are bounded without a privacy assumption.
See the [exceptional-host checkpoint](docs/NORMALIZED_DEFECT_HOSTS_ALIGNMENT.md).
The actual retained channel mass now has an exact finite decomposition
and explicit endpoint, bad-host and baseline errors. Bad rational-unit
terms are removed without a complete residual-nullity estimate. See
the [actual mass reduction](docs/PRIVATE_CHANNEL_MASS_ALIGNMENT.md).
The actual fixed-channel remainder is bounded by an explicit
K(C,b)*B^2/N, implying the paper's N^(-1+epsilon) estimate. See the
[critical mass rate](docs/PRIVATE_CHANNEL_MASS_RATE_ALIGNMENT.md).
Companion T2.5 is now complete, including the positive channel phase,
literal separated symmetric family and fixed real prime cutoff. See the
[complete fixed-channel alignment](docs/FIXED_CHANNEL_MASS_ALIGNMENT.md).
Companion T1.6 now proves both actual selected-kernel counts, with explicit finite constants and a threshold uniform in the real kernel cutoff. See the
[selected-kernel alignment](docs/LARGE_SELECTED_KERNEL_ALIGNMENT.md).
The large-kernel branch for several windows now has an explicit finite CRT cost and the proved fixed-support exponent; T1.14 remains in progress. See the
[tuple branch alignment](docs/LARGE_KERNEL_TUPLES_ALIGNMENT.md).
The first assertion of T1.13 now covers arbitrary actual selected fixed-width blocks, including real prime thresholds; its two-small-kernel assertion remains open. See the
[one-kernel block alignment](docs/FIXED_WIDTH_SMALL_KERNEL_ALIGNMENT.md).
The elementary bidegree-one elimination estimate now counts actual primitive points uniformly in the remaining pair height; its complementary curve bound and full T1.4 remain in progress. See the
[local algebraic count](docs/BIDEGREE_ONE_CURVE_ALIGNMENT.md).
The primitive denominator now divides a single homogeneous resultant, giving a sharper finite bound and removing a redundant chart condition. See the
[single-resultant refinement](docs/SINGLE_RESULTANT_ALIGNMENT.md).
The actual homogeneous auxiliary factor now supplies its chart nondegeneracy by irreducibility, with exact degree and coefficient transport. See the
[projective bridge](docs/PROJECTIVE_NONDEGENERACY_ALIGNMENT.md).
The irreducible (1,1) auxiliary case now has both elementary orientations and a bound in the minimum of the two real box heights. See the
[bilinear local case](docs/BILINEAR_AUXILIARY_ALIGNMENT.md).
Both degree-zero auxiliary counts are now proved on the original positive equation, using primitive zero directions, quadratic fibres and the exact linear progression step. See the
[degree-zero local counts](docs/ZERO_DEGREE_AUXILIARY_ALIGNMENT.md).
The complete main pair profile remains in progress. See the
[finite calculation](docs/FINITE_CHANNEL_SUMS_ALIGNMENT.md).
Article Lemma 3.5 proves exact compression of the actual good-edge family,
with deduplicated normalized values, an explicit finite rank bound and at
most (L+1)^2 one-parameter motifs. See
[statement alignment](docs/GOOD_EDGE_COMPRESSION_ALIGNMENT.md).
Companion T19.5 proves the quantified square-root effective threshold and
its fixed power comparisons for the original count, with a coefficient
chosen before the critical-band width. See
[statement alignment](docs/EFFECTIVE_SUPPORT_ALIGNMENT.md).
Companion T19.6 proves the actual very small tail and its logarithmic-order
truncated moments. A smaller power threshold suffices, and every fixed c>0
is permitted without smooth-pair input. See
[statement alignment](docs/VERY_SMALL_TAIL_ALIGNMENT.md).
Companion T20.7 proves the actual covered three-window rank comparison,
its explicit finite component bound and the square-product assertion. See
[statement alignment](docs/COVER_RANK_ALIGNMENT.md).
Companion T19.11 is proved with a constructed Stein solution, both unit
factor bounds, the actual single/double Poisson reference and the exact
size-bias identity. See [statement alignment](docs/SCALAR_RECURRENCE_ALIGNMENT.md).
Companion T22.4 proves exact full-vector branching up to the growing
critical order K*log(N)/log(log(N)), including the stated logarithmic
correction and one uniform deterministic envelope. See
[statement alignment](docs/CRITICAL_ORDER_BRANCHING_ALIGNMENT.md).
Companion T1.15 is proved with full-vector independence after old observations,
its literal exceptional bound, and all subset, fixed-dilation and enlarged
logarithmic-window extensions. See [statement alignment](docs/FIXED_BRANCHING_ALIGNMENT.md).
Companion T21.2 is proved with actual conditional ranks, probabilities and
means, a sharper finite pool coefficient, and the matching fixed-j
critical asymptotic. See [statement alignment](docs/CONDITIONAL_RANK_ALIGNMENT.md).
Companion T19.7 now proves divergence of the original positive and total
run exponential moments along the prime subsequence, with the exact source
liminf constant and threshold. See [statement alignment](docs/PRIME_CYLINDER_ALIGNMENT.md).
Article Lemma 5.1, the full first-excluded-prefix polynomial identity, is proved
over any commutative semiring. Auxiliary lemmas develop the finite centering
transform at orders zero, one and two. The principal Poisson asymptotic theorems remain open.
Article Proposition 4.1 is proved on an arbitrary probability space with a
finite measurable indicator family. The actual count law is identified as a
measure; coefficients are Bochner expectations; zero-marginal sites are removed
without changing the law; complementary Bernoulli products are probabilities.
Article Proposition 5.2 is proved with its exact positive remainder kernel,
joint activation mass and ordinary ℓ¹ norm bound, without an independence
assumption between the prefix and suffix.
Actual finite-cylinder run marginals are proved to be zero in incompatible
cases and inverse powers of two at the effective rank otherwise. The
full-support centered Fourier formula and its sharper nullity bound are proved
on effective dual spaces and instantiated for actual run moments. Exact
finite-cylinder consistency is proved for the infinite prime-sign measure,
including its full count law and centered moments. Effective square-class
images and their relative relation kernels are identified with the actual
character spaces, completing Lemma 4.2. Its
[alignment note](docs/FOURIER_ALIGNMENT.md) records the representation and scope.
Lemma 4.3 is proved with its compatible-nullity bound, comparison and equality
case, using exact actual joint masses and retaining the empty family. See its
[alignment note](docs/COMPATIBLE_NULLITY_ALIGNMENT.md).
Lemma 4.4 is proved with the unique finest direct partition, exact factorization
of joint and centered moments, and additivity of effective relative nullity
under the actual infinite measure. See its
[alignment note](docs/DIRECT_COMPONENT_ALIGNMENT.md).
Companion Lemma T1.1 is proved with the exact degree-uniform bound
`U ≤ (64R)^d`, including real radii and integer bases. The proof uses formal
series, coefficient cancellation and integer-square separation. See its
[alignment note](docs/SPLIT_PRODUCT_ALIGNMENT.md).
Companion Lemma T1.2 is proved as an actual positive-solution count, uniformly
over every coefficient in a fixed real polynomial box. Both square and
nonsquare coefficient products are included, and all divisor, ideal and
unit estimates used in the proof are proved. See its
[alignment note](docs/QUADRATIC_COUNT_ALIGNMENT.md).
Companion Lemma T1.3 is proved in full: the uniform local `O(B/log B)`
bound, global `N^(1/2+o(1))` count, exact dyadic two-defect-window `N^o(1)`
count, and fixed real affine interval versions. The complete statements use
one common threshold and include the literal `B=L+1` convention. See
[statement alignment](docs/DEFECT_COUNTS_ALIGNMENT.md).
Article Lemma 2.1 is proved in full: exact Griesmer inequality, general and
critical rank thresholds, and exact subcritical independence of actual
relative signs under the infinite model. The critical-band effective ranks,
p or 2p marginals and a uniform pointwise O(1/N) bound are also proved.
The lower base bound U≥aN suffices, and one threshold controls every shorter
window. See [local rigidity alignment](docs/LOCAL_RIGIDITY_ALIGNMENT.md).
Article Proposition 3.1 is proved: the full-rank regular set has only
`N^o(1)` exceptional windows; the actual count laws, both means and arbitrary
affine marginal sums have the stated transfer estimates. Fixed-moment and
second factorial-cumulant transfers retain the source's bounded-moments
hypothesis, including the case of one prescribed length sequence. See
[regular-set alignment](docs/REGULAR_SET_ALIGNMENT.md).
Companion Lemmas T9.1 and T9.2 are proved for the exact integer offset sets
and critical vertex windows. Their proofs give a stronger local square
threshold and an absolute constant in the defect bound, with separate entries
in the mathematical change log. See
[local-square and critical-defect alignment](docs/LOCAL_SQUARE_THRESHOLD_ALIGNMENT.md).
Companion T22.2 is proved with both its missing-block inequality and its
sum over arbitrary ordered distinct tuple families. Falling-factorial moments
are actual infinite-model expectations. The proof also gives an exact
heterogeneous-marginal version. See
[missing-block alignment](docs/MISSING_BLOCK_ALIGNMENT.md).
Companion T19.1 is proved for every N≥2 and L≥1: the exact support is
bounded by `ceil(N/L)`, and every factorial moment belongs to the literal
`j! * p^j` nonnegative integer lattice, including all irregular windows.
See [support and lattice alignment](docs/SUPPORT_LATTICE_ALIGNMENT.md).
Companion T9.3 is proved: the actual number of free components is within
O(B/log B) of the pair intersection dimension, with exact cutoff 10B and
B=L+1. Complete relations and the small-prime/parity rank cost are proved;
overlapping windows, component selection and both-block membership are included.
See [free-component alignment](docs/FREE_COMPONENT_ALIGNMENT.md).
Companion T9.4 is proved with the exact bivariate factor-height constant,
including the integer quotient. The primitive-factor hypothesis is unnecessary.
See [factor-height alignment](docs/BIVARIATE_FACTOR_HEIGHT_ALIGNMENT.md).
Article Lemma 8.1 is proved for the actual quadratic Poisson signed measure:
all singleton masses and the exact closed positivity interval, in both
directions, are included. See [positivity alignment](docs/QUADRATIC_POISSON_ALIGNMENT.md).
Companion T19.12 is proved for arbitrary finite measurable indicator families:
the signed Palm residual bound, exact heterogeneous coefficients, and the
equal-marginal specialization retain all cancellations and zero-marginal
conventions. See [signed Palm alignment](docs/SIGNED_PALM_ALIGNMENT.md).
Companion T19.13 is proved for arbitrary probability laws, including laws
without a first moment. The weighted recurrence criterion and parameter
stability retain the original constants, with weaker parameter hypotheses.
See [weighted recurrence alignment](docs/WEIGHTED_POISSON_NORM_ALIGNMENT.md).
Companion T2.1 is proved uniformly in the position of every integer window:
its logarithmic small-prime budget and exceptional-value count have explicit
absolute constants. See [small-prime alignment](docs/SMALL_PRIME_BUDGET_ALIGNMENT.md).
Companion T20.2 is proved for the full product tail of positive integers,
with one constant per exponent and every real cutoff T>=1. See
[integer product-tail alignment](docs/INTEGER_PRODUCT_TAIL_ALIGNMENT.md).
Companion T2.2 is proved with the exact selected-coordinate codimension,
simultaneous multiplicity and unordered-decomposition bounds, and no further
dimension loss on removing zero coordinates. See
[coordinate regularisation alignment](docs/COORDINATE_REGULARISATION_ALIGNMENT.md).
Companion T2.3 is proved for the restricted constraint rows, including
binary connected components and a sharper ternary incidence bound dK^2.
Repeated supports are identified before counting. See
[ternary constraint alignment](docs/TERNARY_CONSTRAINTS_ALIGNMENT.md).
Companion T23.1 is proved with actual positive probability laws, the exact
factorial-moment perturbation and total variation constant, and uniform
exponential-moment control. Its parameter interval also extends to [0,2],
with the zero perturbation at the final endpoint made explicit. See
[moment-obstruction alignment](docs/MOMENT_OBSTRUCTION_ALIGNMENT.md).
The following unnumbered asymptotic example is also proved, including the
literal floor, fixed-order moment identities and failure of every polynomial
rate. See [its alignment](docs/MOMENT_OBSTRUCTION_ASYMPTOTICS.md).
Article Lemma 6.1 is proved in full over any field, including its stopping
subspace, exact codimension bound, coordinate multiplicity and independent-label
representation count. A stronger count replaces t by t-1 and covers all
zero-sum-free label supports. See
[disjoint recovery alignment](docs/DISJOINT_RECOVERY_ALIGNMENT.md).
Article Lemma 7.1 is proved for the actual truncated odd-prime kernel, with
real cutoffs and explicit constants. A finite square-part count extends the
bound to sigma=1/2. See
[small-kernel Rankin alignment](docs/RANKIN_SMALL_KERNEL_ALIGNMENT.md).
Companion T22.3 is proved for arbitrary finite prime sets, including its
uniform logarithmic-budget estimate. The stronger bound removes the zeta
factor and extends the exponent interval to [1/2,3/4]. See
[logarithmic prime-budget alignment](docs/LOGARITHMIC_PRIME_BUDGET_ALIGNMENT.md).
Companion T21.3 is proved for both actual squarefree prime products and
arbitrary distinct integer-factor supports, with literal weights and explicit
constants. The parameter range extends to every fixed d>=2. See
[offset-pattern Rankin alignment](docs/OFFSET_PATTERN_RANKIN_ALIGNMENT.md).
Companion T4.2 is proved uniformly over every tuple of fixed source windows,
with the exact signed offsets and an internally proved certificate count.
The product threshold also allows equality. See
[fixed-source certificate alignment](docs/FIXED_SOURCE_PRODUCT_CERTIFICATE_ALIGNMENT.md).
Companion T20.5 is proved for actual window square classes and the exact
line-substituted polynomials: at most one common root, and at most two
equations to discard. Only the first window needs to be regular. See
[offset-root separation alignment](docs/OFFSET_ROOT_SEPARATION_ALIGNMENT.md).
Article Lemma 7.2 is proved, including its exact finite certificate count
and weighted sum over all growing orders. The literal ceiling and factorial
budget give the exponent -2*beta+4/A+o(1), uniformly over critical-band
lengths. The weighted bound also permits beta>=0 and u>=0. See
[moderate-certificate alignment](docs/MODERATE_CERTIFICATE_ALIGNMENT.md).
Article Lemma 7.3 is proved for the actual incoming/outgoing saturation
neighbors and actual finite graph. Their uniform degree exponent is 2/A.
The same neighborhood bounds already hold at the lower threshold D>=N.
See [saturation degree alignment](docs/SATURATION_DEGREES_ALIGNMENT.md).
Article Lemma 7.4 is proved by an actual partition into disjoint graph
stars. Stronger generating bounds hold for every nonnegative activity and
for heterogeneous vertex weights. See
[marked generator alignment](docs/MARKED_GENERATOR_ALIGNMENT.md).
Article Proposition 19.2 is proved for actual signed Poisson differences,
including every order, the four-mass formula and the exact constant at
mean two. The correction coefficient's elementary lower bound is doubled.
See [Poisson difference norms](docs/POISSON_DIFFERENCE_NORMS_ALIGNMENT.md).
Companion T20.1 is proved for actual shared primes and physical offsets
on a line, with a constructed primitive direction and uniform logarithmic
and o(B) counts. It needs less regularity and has a sharper offset bound.
See [offset line alignment](docs/OFFSET_LINE_PRODUCT_ALIGNMENT.md).
Companion T20.3 is proved for actual forced offset planes, including all
normal coordinates and the uniform original affine mass of triples on two
geometrically distinct planes. It also holds under weaker regularity hypotheses.
See [forced plane alignment](docs/OFFSET_PLANE_ALIGNMENT.md).
Companion T19.2 is proved with the exact disjoint deficient blocks, their
original Bernoulli laws, exact mean identities and a sharper endpoint correction.
See [local block alignment](docs/LOCAL_BLOCKS_ALIGNMENT.md).
Companion T19.8 is proved with actual deletion traces, the original affine
moments and a constructed dense canonical component. Its positive-mass loss
improves by a factor of two. See [private-rank peeling](docs/PRIVATE_RANK_PEELING_ALIGNMENT.md).
The sharp PNT input is proved by a selected, recompiled and audited analytic
development, with [separate provenance](docs/PRIME_NUMBER_THEOREM_ALIGNMENT.md).

| Material | Location |
|---|---|
| Main article | [PDF](manuscripts/paper-p1/v1.6/P1_V1_6_Main_Article_2026-10-31_EN.pdf) |
| Technical companion | [PDF](manuscripts/paper-p1/v1.6/P1_V1_6_Technical_Companion_2026-10-31_EN.pdf) |
| French revision note | [PDF](manuscripts/paper-p1/v1.6/P1_V1_6_Revision_Note_2026-10-31_FR.pdf) |
| Original archives, editable sources and identities | [Manuscript package](manuscripts/paper-p1/README.md) |
| Coverage of all 167 numbered results | [Source-to-Lean correspondence](docs/MANUSCRIPT_ALIGNMENT.md) |
| Corrections and mathematical improvements | [Mathematical change log](docs/MATHEMATICAL_CHANGELOG.md) |
| Formalization state and next steps | [Status](docs/FORMALIZATION_STATUS.md) |
| Paper C reuse candidates | [Reuse record](docs/PAPER_C_REUSE.md) |
| Future Palomar registrations | [Preparation](docs/PALOMAR_PLAN.md) |

## Reproducible environment

Lean is pinned to **v4.36.0-rc2**. Mathlib is pinned to commit
`9d581dfff2e41de989072ea63abf3daf69311520`, tagged `v4.36.0-rc2`,
whose toolchain matches. The dependency lock file records all transitive revisions.

```sh
python3 scripts/check_disk.py
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update
python3 scripts/cache_dependencies.py
python3 scripts/check_disk.py
python3 scripts/check_sources.py
python3 scripts/update_audit.py --check
lake build
lake env lean Audit.lean
```

Use the committed lock file for ordinary builds; `lake update` is needed when
initially resolving or intentionally updating dependencies. Cache downloads are
restricted to the project's actual imports and their transitive dependencies. Set
`XDG_CACHE_HOME`, `MATHLIB_CACHE_DIR` and `TMPDIR` to local Ubuntu directories if
their defaults point elsewhere. Available-space warnings start at 10 GiB; large
downloads must stop below 5 GiB. See [environment policy](docs/ENVIRONMENT.md).

`lake build` treats Lean warnings as errors. The audit generator checks coverage
of every project theorem and lemma. `Audit.lean` exposes the kernel
axioms of each selected proved declaration. A successful build verifies only
the checked declarations, not the unformalized manuscript claims. The source
integrity check verifies file identities and the coverage inventory; it does
not certify mathematical proofs.

## Scope and attribution

The target includes exact marginals and square-class spaces, affine and stopped
expansions, arithmetic estimates, scalar reconstruction and optimality,
rational-channel refinements and the companion's additional results. External
mathematical inputs will be individually tracked rather than hidden as axioms.

The project follows the traceability approach of
[paper-c-lean](https://github.com/Vulkin-prog/paper-c-lean). No Paper C Lean code
was imported at initialization. Parity vectors, the prime-sign model and
selected arithmetic counting proofs have since been adapted and rebuilt.
The reuse record identifies every source and adaptation. Its old compiled
files are not reusable under this compiler.
Palomar registrations are planned after completion and
qualification; no registration exists for this project yet.

New Lean code, project scripts and project documentation are licensed under
[Apache-2.0](LICENSE), following Paper C. The unchanged manuscript package is
excluded from that grant and retains its original authorship and terms; no new
manuscript licence is inferred. The source package records its original AI
assistance. Repository setup and initial development are agent-assisted;
compilation and source checks are distinct from independent human review.

The exact incompatible-triple reduction now uses one copy of the actual
pair/target deficit, with its full effective-space support and exact incidence
bijection proved. The arithmetic bound for this deficit remains open. See
[triple activity alignment](docs/TRIPLE_ACTIVITIES_ALIGNMENT.md).

The actual original run count now has the complete third factorial-cumulant
identity, with every repeated-index correction. Its comparison with positive
connected activity is reduced to the two remaining arithmetic activities.
[Precise scope and remaining bounds](docs/TRIPLE_ACTIVITIES_ALIGNMENT.md).

Every fixed primitive order r>=5 now satisfies both bounds of main 15.5
by the stronger elementary exponent 1-r/2; r=4 remains open.
[Statement and fixed-order scope](docs/PRIMITIVE_GENERAL_MASS_ALIGNMENT.md).

Every literal fixed-height explicit coefficient now has direct positive vanishing bounds. Its quadratic and Hermite references are actual probabilities without BCN or the complete pair profile. The height4 coefficient, exact masses, first moving-phase constants and height5 correction are checked; source distance rates remain open. See [the finite-height scope](docs/EXPLICIT_CHANNEL_HIERARCHY_ALIGNMENT.md).
