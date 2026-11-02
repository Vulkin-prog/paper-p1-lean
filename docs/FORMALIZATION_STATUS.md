# Formalization status

Stage: **exact probability identities and uniform arithmetic foundations**, 2 November 2026.
Neither document is fully formalized.

- Baseline: P1 V1.6, 167 numbered results: main 73, companion 94.
- Numbered results completed: **77 / 167**: article Propositions 3.1, 4.1, 5.2, 6.2, 6.3, 9.1, 13.3, 13.7, 19.2, Corollaries 9.2, 10.2, 10.3, Theorems 10.1, 13.1, 13.2 and Lemmas 2.1, 3.5, 4.2, 4.3, 4.4, 5.1, 6.1, 7.1, 7.2, 7.3, 7.4, 8.1, 14.2; companion Lemmas T1.1, T1.2, T1.3, T1.6, T1.9, T1.11, T2.5, T2.6, T9.1, T9.2, T9.3, T9.4, T12.1, T12.2, T19.1, T22.2 and Propositions T1.15, T19.2, T19.5, T19.6, T19.7, T19.9, T19.12, T20.3, T22.4, T23.1, together with Proposition T9.5, Lemmas T19.8, T19.11, T19.13, T2.1, T2.2, T4.1, T4.2, T20.1, T20.2, T20.5, T20.7, T21.2, T21.3, T22.3 and Corollary T2.3, and Lemmas T5.2, T6.1, T6.2, T6.3, and Propositions T1.14, T22.7 and T17.2.
  Lemma 5.1 is the full
  first-excluded-prefix polynomial expansion on an arbitrary finite ordered set.
  The boundary is proved to be deletion of the maximum, and the suffix is proved
  to lie strictly after that maximum. The scalar parameter and empty products
  are included. The theorem holds over any commutative semiring.
- Article Proposition 4.1 is proved on an arbitrary probability space for a
  finite measurable Boolean family. `observedCountLaw_realizes` identifies the
  full measure-theoretic count law; `centered_bernoulli_expansion` proves the
  identity over the admissible set of positive exact Bochner marginals, the
  unit empty coefficient, vanishing singleton terms and probability status of
  the complementary references. The carrier may be the finite subtype of the
  paper's index set; `indicatorCount_subtype` proves the count reindexing.
  No independence or model-specific arithmetic premise is used.
- Article Proposition 5.2 is proved on an arbitrary probability space.
  `positive_stopped_remainder` gives the exact stopped law difference, positive
  kernel and its mass, and the full ordinary ℓ¹ error bound. Each kernel
  coefficient is proved to be the expected prefix activity times the actual
  suffix count event; its mass is the actual joint activation probability.
  The suffix can remain completely dependent. The retained reference has total
  mass one, without an assertion that its individual coefficients are positive.
- The ordinary ℓ¹ norm is the sum of absolute singleton masses. Its triangle
  inequality, convolution submultiplicativity and difference-power bound are
  proved. Positive kernels have norm equal to their mass, so the bound incurs
  no exponential factor in the suffix size.
- The inclusion-exclusion transform is proved to equal actual finite centered
  moments. Total mass is proved to be the coefficient sum and a convolution
  homomorphism; coefficientwise positivity is preserved by convolution.
- The project currently has **6992 audited theorem/lemma declarations**. This
  count includes auxiliary facts and is distinct from numbered-result coverage.
  Generic binary character orthogonality and the affine fiber Fourier identity
  are proved. The full-support centered Fourier formula, its sharper
  `2^ρ - 1` bound and nonzero-moment implication are now proved on effective
  dual subspaces and instantiated for actual finite-cylinder run moments.
  The relative nullity is identified with the dimension deficit in the paper.
  These formulas and bounds are also transported to the actual infinite
  prime-sign measure. Effective square-class images are now identified with
  the row character spaces by explicit linear equivalences. Relative relation
  kernels and their nullities are preserved. Article Lemma 4.2 is complete;
  `dyadic_squareClass_fourier` supplies the aligned conclusion for every
  nonempty admissible subfamily of the dyadic block. The
  [alignment note](FOURIER_ALIGNMENT.md) explains the rational-square
  representation and hypotheses. These identities alone supply no asymptotic
  estimate for run counts.
- Article Lemma 4.3 is complete. `compatible_nullity_majorant` proves the full
  bound with actual infinite-model centered and joint Bochner moments,
  compares the compatible maximum with the effective relative nullity, and
  proves equality when the complete joint mass is positive. The maximum is
  identified with the filtered finite supremum and proved attained by a
  positive-mass subfamily. Extension by zero proves nullity monotonicity.
  The exact joint-mass formula is proved from the actual joint affine system
  and rank-nullity; it is not an assumed bound. The empty family is included.
  See [statement alignment](COMPATIBLE_NULLITY_ALIGNMENT.md).
- Article Lemma 4.4 is complete. Partitions which preserve every effective
  relation under restriction are proved closed under common refinement, and
  there is a unique finest such partition. The criterion is proved equivalent
  to injectivity of addition from the actual block-sum spaces. The relation
  kernel splits as the product of the kernels inside the parts, proving
  nullity additivity. A finite spectral identity proves both joint and
  centered moment factorization, and these identities are transported to the
  actual infinite prime-sign measure. `canonical_run_components_finset`
  supplies all conclusions, including the empty family, with a finite cutoff
  constructed inside the proof. See [alignment](DIRECT_COMPONENT_ALIGNMENT.md).
- Paper C code ported: parity vectors and selected finite prime-cylinder
  definitions/proofs, with exact source identities recorded in the reuse ledger.
  Complete multiplicativity, the signed run-start interpretation, cutoff
  adequacy, actual cylinder probabilities and the exact-marginal centered
  count-law identity are proved. The infinite prime-sign measure, restriction
  to finite cylinders and exact consistency of values and start events have
  now been ported. Finite product-measure singleton weights equal the actual
  real weights used in P1. Every finite-cylinder expectation is transported;
  infinite start marginals and centered moments equal their finite versions.
  `dyadicCountLaw_realizes_infinite_count` identifies the full count law with
  its actual infinite-measure pushforward. The no-constant-tail result is
  also checked; its inherited lemma number refers to Paper C.
  No unproved input was added by these ports. The separate conditional BCN developments are recorded below.
- Generic affine fibers, their kernel equivalences, power-of-two cardinalities
  and rational uniform probabilities have been ported and checked. The actual
  real uniform mass is now proved to be zero for incompatible systems and
  `2⁻ʳ` otherwise. The full run-start affine system has been ported, and this
  formula is linked to actual finite-cylinder run marginals for positive length.
  The exact rank deficit from local even square relations is now proved.
  The finite Griesmer inequality is proved on the actual window relation code,
  with its exact ceiling distance from T1.1, actual defective coordinates and
  redundancy at most π(B)+1. A finite prime-count obstruction gives the two
  effective ranks and the two exact positive marginals under the infinite
  model. The sharp prime-count input is now proved by a selected, recompiled
  Wiener–Ikehara/PNT development, with its sequential ratio and uniform
  one-sided consequence. All its selected proofs are included in the kernel
  audit; unfinished upstream Fourier declarations are excluded from the
  dependency chain. See [PNT proof and provenance](PRIME_NUMBER_THEOREM_ALIGNMENT.md).
  Article Lemma 2.1 is now complete: the exact finite inequality, general and
  critical asymptotic rank bounds, and exact subcritical relative-sign
  independence under the actual infinite measure. The full relative-bit law
  is identified with the fair product law and `iIndepFun` is proved for the
  actual signs. The critical-band ranks, exact p or 2p marginals and a uniform
  pointwise O(1/N) bound are also proved. One threshold precedes all bases and
  lengths; only U≥aN is needed, with no upper base bound. See
  [local rigidity alignment](LOCAL_RIGIDITY_ALIGNMENT.md).
- On any effective subspace of actual binary linear forms, the affine event
  has its character expansion and actual marginal equal to the inverse size
  of that space. Local signs are evaluations at a solution and proved
  independent of the chosen solution. Run events are identified with the
  image of their actual row transpose, so local row relations are quotiented
  before taking centered products. The complete boundary map is proved to
  parametrize exactly the even selections of the window. Their prime-exponent
  parity image detects precisely rational square relations among positive
  vertices, and its injection into actual cylinder characters is proved.
  Local and relative dimensions therefore retain every local relation once.
- Companion Lemma T1.1 is complete. `uniform_split_product_real_radius`
  proves the exact bound `U ≤ (64R)^d` uniformly in every even degree `d ≥ 2`,
  for a real radius and integer base, with distinct bounded integer shifts.
  New weighted coefficient bounds keep the necessary powers of the radius.
  Integer-square separation supplies the large-base estimate using a
  polynomial of degree at most `d/2 - 1`; the zero-value branch uses the
  integral-root height bound. Every input is proved, with no analytic tail
  or arithmetic literature bound supplied as an assumption. The Paper C
  algebraic ports are pinned and audited. See
  [statement alignment](SPLIT_PRODUCT_ALIGNMENT.md).
- Companion Lemma T1.2 is complete. `uniform_quadratic_equation_count`
  counts the exact finite set of positive solutions in the literal real
  polynomial-height box, with a threshold before all coefficients. The square
  branch injects into divisors of the nonzero right-hand side after scaling.
  The nonsquare branch uses the proved ideal-divisor, conductor-descent,
  unit-orbit and elementary divisor estimates ported from Paper C. No
  literature inequality is left as an unproved premise. Both branches, every
  coefficient range and every positive real error exponent are included. See
  [statement alignment](QUADRATIC_COUNT_ALIGNMENT.md).
- Companion T1.3 is complete. The intrinsic defect predicate is proved
  equivalent to the large odd-prime kernel being 1, with canonical
  square-times-small-prime representations. The binary Hamming bound,
  augmented parity rank and square-product bridges are ported and checked.
  T1.1 discharges the short-word exclusion, giving a finite bound for the
  actual defective set in [U,U+R] with independent cutoff H and width R.
  Small-cardinality cases are included. An elementary Chebyshev bound and a
  direct floored coding radius give an explicit real local rate with a finite
  prime budget. The global `N^(1/2+o(1))` count is now proved for the actual
  positive defective set, uniformly for `H ≤ D log N` and `X ≤ CN`, with
  fixed real C,D and a threshold before all cutoffs and counting heights.
  The two-defect window count is also complete, including actual positive
  start sets and the exact dyadic windows [x-1,x+L-1]. A finite configuration
  cover uses the proved T1.2 bound with explicit polynomial coefficient
  heights. The prime-support count is proved uniformly subpolynomial with
  only H ≤ D log N; there is no unproved counting premise. See
  [two-defect alignment](TWO_DEFECT_ALIGNMENT.md). The local prime budget is
  now proved uniformly, giving the full O(B/log B) rate. Fixed positive real
  dilations and real translations are included with exact integer-point
  interval definitions and affine vertex endpoints. The complete statements
  use one common threshold for every local interval, cutoff, global counting
  height and run length. Global and window conclusions are quantified
  independently of local-interval parameters. Literal B=L+1 corollaries are
  included. See [complete alignment](DEFECT_COUNTS_ALIGNMENT.md).
- Article Proposition 3.1 is complete. The regular set is defined by the
  actual square-class rank L. A nonzero even relation needs two defective
  vertices, and the actual exceptional set has cardinality at most N^ε
  eventually for every ε>0, uniformly over all critical-band lengths. Every
  affine target on a regular window has mass exactly p=2^(-L). On all other
  windows, incompatibility and the proved critical rank bound give deviation
  at most p and mass at most 2p. The law-and-two-means error is at most
  4p times the number of exceptional starts, hence at most
  4·2^C·N^(-1+ε). The law is the actual infinite-measure pushforward and
  total variation is half the ordinary sum of absolute singleton differences.
  Fixed-moment transfer uses a proved finite truncation inequality and the
  source's explicit bounded-higher-moments premise. Allowed length families
  and a single prescribed sequence are included. The full second factorial
  cumulant retains its -E Z diagonal correction. See
  [regular-set alignment](REGULAR_SET_ALIGNMENT.md). This verifies the
  conditional transfer; uniform boundedness of the model's fixed moments
  remains a separate open manuscript result.
- Companion T9.1 and T9.2 are complete. T9.1 concerns actual nonempty even
  finite subsets of integer offsets in [-B,B]; the original threshold is
  proved as a consequence of the stronger (64B)^m bound. For B≥2 this gives
  the simpler exponent 5m in place of 12m. T9.2 counts the actual kernel-one
  positions above 10B in the full vertex interval. One absolute constant K
  works for every fixed critical band width C; only N0 depends on C.
  No admissibility or regularity hypothesis is used. See
  [statement alignment](LOCAL_SQUARE_THRESHOLD_ALIGNMENT.md).
- Companion T22.2 is complete. The actual relation kernel is covered by
  extension-by-zero images of its one-block-deleted kernels. Their exact
  cardinal inequality gives the pointwise probability bound, including
  incompatible events. A stronger version retains all heterogeneous actual
  marginals. Ordered tuples are embeddings, and deleting a marked coordinate
  encodes the tuple injectively by that value and the remaining ordered tuple.
  The exact count of active embeddings gives the full actual falling-factorial
  moment. Summation yields R|G|pmax·E(Z_G)_(R-1), hence the source's RNp bound
  on the regular set. All finite orders are included without a growing-order
  constant or an assumed moment estimate. See
  [statement alignment](MISSING_BLOCK_ALIGNMENT.md).
- Companion T19.1 is complete for every N≥2 and L≥1. Two active starts
  are deterministically separated by at least L. An injective quotient-bin
  encoding bounds their number by the exact real ceiling ceil(N/L).
  The full actual count law is supported in that range. Every actual joint
  event has at most |I|L binary equations and its probability is a
  nonnegative integer multiple of p^|I|, including incompatibility with
  coefficient zero. The unordered-subset expansion of the falling factorial
  supplies j!, proving E(Z_N)_j=j! p^j m with an actual natural m.
  No critical-band, regularity, independence or asymptotic premise is used.
  See [support and lattice alignment](SUPPORT_LATTICE_ALIGNMENT.md).
- Companion T9.3 is complete. The complete relation space retains both block
  parities and every prime coordinate, and its dimension is the sum of both
  local kernel dimensions and finrank(S_x∩S_y). Inside the actual large-prime
  solution space, the remaining finite constraint kernel is explicitly
  equivalent to that complete relation space. Its rank cost is at most
  π(10B)+2. The proved critical local-kernel bound yields c≤d_xy+π(10B)+4,
  while d_xy≤c+D and the actual D count is O(B/log B). Together they give
  the literal source estimate. One absolute constant precedes C; the threshold
  may depend on C. Every nontrivial free component meets both formal blocks
  and is selected entirely or omitted. No admissibility or separation is
  required, and overlapping physical windows remain separate formal copies.
  See [complete statement alignment](FREE_COMPONENT_ALIGNMENT.md).
- Companion T9.4 is complete. The exact bound for both factors in a nonzero
  integer bivariate product is 2^(dX+dY) times its actual coefficient ℓ²
  norm, bounded further by the source's exact rectangle constant times H(P).
  Univariate Mahler bounds, specialization and Parseval prove the estimate
  without assuming a multivariate measure theorem. Degree-lowering
  specializations are included. Primitivity of the factor is unnecessary.
  See [factor-height alignment](BIVARIATE_FACTOR_HEIGHT_ALIGNMENT.md).
- Article Lemma 8.1 is complete for every μ>0 and real α. The reference is
  an actual signed measure with proved summable singleton masses and total
  mass one. Its exact second-difference formula and its identification with
  the shifted actual Poisson measure are proved. The integer minimum of
  (k-μ)^2-k gives the exact closed interval for positivity; negative α is
  excluded by a proved large-index witness. Positivity constructs an actual
  probability measure. No parameter asymptotics or approximation estimate
  is assumed or concluded. See [positivity alignment](QUADRATIC_POISSON_ALIGNMENT.md).
- Companion T19.12 is complete on an arbitrary probability space. Every
  conditional deleted count law is normalized by its own positive marginal;
  zero-marginal sources are proved to vanish and are omitted. The exact
  size-bias and deletion identities isolate the diagonal error with norm
  at most 2 sum p_x^2. Translation is an exact ℓ¹ isometry, yielding the
  original residual comparison for every real theta. The residual is
  identified with the ordinary sum of its actual raw coefficients and
  actual mean. The generating polynomial after z=1+t gives the exact
  heterogeneous signed coefficients; differentiation proves the full
  equal-marginal formula (j+1)B_(j+1)-p(n-j)B_j at every natural order.
  Finite laws also embed injectively as actual atomic signed measures with
  the same countable ordinary ℓ¹ norm. See [signed Palm alignment](SIGNED_PALM_ALIGNMENT.md).
- Companion T23.1 is complete for actual probability laws with the literal
  epsilon=(1-a/2)exp(-1)/(2m!). The exact Δ^m coefficients give both
  pointwise comparison factors, all factorial-moment differences and the
  exact total variation constant. Exponential sums and domination prove
  integrability of every factorial moment and the source's uniform
  exponential bound. The construction also works on [0,2], with a zero
  perturbation at a=2; the larger uniform exponential bound is recorded
  separately. See [moment-obstruction alignment](MOMENT_OBSTRUCTION_ALIGNMENT.md).
  The unnumbered m_N/Stirling/polynomial-rate continuation is now proved
  separately: the literal floor and parameter define actual eventual
  probability laws, every fixed factorial moment eventually agrees exactly,
  the logarithmic error has the stated O(sqrt(log N)) size, and the distance
  strictly exceeds every fixed N^(-gamma) eventually. The proof gives a
  uniform version over all a in [0,1], with one threshold per gamma. This
  unnumbered work adds no completed numbered result. See
  [asymptotic alignment](MOMENT_OBSTRUCTION_ASYMPTOTICS.md).
- Companion T19.13 is complete for arbitrary actual probability laws on the
  natural numbers, without a first moment. The weighted residual is absolutely
  summable. The exact factorial resolvent proves the lower exp(-mu) bound;
  the forward operator proves the upper 2(1+mu) bound. Both original comparison
  and stability conclusions are checked. The comparison includes mu=0 and
  stability has an all-real-parameter version; the source M bound needs only
  0<=mu<=M, with no restriction on nu. See
  [weighted recurrence alignment](WEIGHTED_POISSON_NORM_ALIGNMENT.md).
- Companion T2.1 is complete for every translated positive interval. The
  exact odd-prime product is identified with sf(n)/K_B(n). Counting multiples
  uniformly in the interval position and summing factorial valuations proves
  the source logarithmic bound with explicit remainder (log 4)B. The exact
  exceptional set above B^A has cardinality at most
  (1/A+((log 4)/A)/log B)B. No PNT, critical-band or height premise is used.
  See [small-prime budget alignment](SMALL_PRIME_BUDGET_ALIGNMENT.md).
- Companion T20.2 is complete for each fixed real s>1 and every real T>=1.
  Absolute convergence and the exact positive-index product summand are proved.
  The evaluated power integral treats the exact floor, and the harmonic sum
  gives the logarithmic factor. One explicit positive constant depends only
  on s and precedes all thresholds. See
  [integer product-tail alignment](INTEGER_PRODUCT_TAIL_ALIGNMENT.md).
- Companion T2.2 is complete on the actual binary coordinate subspace. Its
  selected coordinates define R prime exactly, with codimension equal to their
  cardinality. The final multiplicity and unordered-decomposition bounds hold
  simultaneously. Exact kernel dimensions, disjoint pair collisions and a
  finite potential prove existence and termination. Removing zero coordinates
  is an injective projection and costs no further dimension. A stronger version
  charges only initially nonzero coordinates and includes K=0 or d=0. See
  [coordinate regularisation alignment](COORDINATE_REGULARISATION_ALIGNMENT.md).
- Companion T2.3 is complete on the actual restricted constraint supports.
  Three-block coloring gives size at most three. Restriction preserves the
  actual zero sums, deletion removes exactly zero labels, and repeated supports
  are identified. Binary and ternary row classifications and the actual binary
  graph-component bound K are proved. The unordered support cover gives the
  stronger ternary incidence dK^2. An existence wrapper constructs D by T2.2;
  no regularizer output is assumed. See
  [ternary constraint alignment](TERNARY_CONSTRAINTS_ALIGNMENT.md).
- Article Lemma 6.1 is complete. Its actual small-codimension stopping
  subspace, exclusion of every t-disjoint recovery system, coordinate
  multiplicity t-1 and independent-label representation count are proved.
  A maximal independent history and its pointwise rank certificate are
  constructed; exact finite Bernoulli weights and the literal sampling
  parameter give the source constant two. Maximal disjoint families give
  explicit transversals, and an erase recursion proves the sharper
  j!*(t-1)^(j-1) bound, even for zero-sum-free supports. The full lemma holds
  over any field for any finite family of linear forms, without separation.
  The literal binary coordinate specialization retains the original bound.
  See [disjoint recovery alignment](DISJOINT_RECOVERY_ALIGNMENT.md).
- Article Lemma 7.1 is complete for the actual truncated odd-prime kernel,
  with real cutoffs, positive integer values and explicit constants. A finite
  cover comes from the canonical small/large/square decomposition. Direct
  square-root fibre counts and integral bounds for finite reciprocal-power
  sums give the source bound, uniformly in every cutoff. The stronger theorem
  includes sigma=1/2 and Y,T>=0. The exponential constant depends only on
  sigma. Three comparison proofs are adapted from the documented Paper C
  RankinTilt blob and rebuilt under the new compiler. See
  [small-kernel Rankin alignment](RANKIN_SMALL_KERNEL_ALIGNMENT.md).
- Companion T22.3 is complete for the actual positive integers with odd-prime
  support in an arbitrary finite prime set. Both the finite Euler-product
  count and the logarithmic budget estimate are proved, with real cutoffs.
  The stronger count removes zeta(2*sigma); the uniform logarithmic bound
  extends to [1/2,3/4] with explicit constant 65+4*log(4), for Y>1.
  The argument uses the primorial bound and finite Abel comparison, without
  an unproved prime estimate. See
  [logarithmic prime-budget alignment](LOGARITHMIC_PRIME_BUDGET_ALIGNMENT.md).
- Companion T21.3 is complete for both literal weighted populations:
  squarefree prime products and finite supports of distinct integer factors.
  Prime-factor injectivity, finite support exhaustiveness and both source
  weight identities are proved. Finite Rankin and clipped Abel comparisons
  give all needed power tails. One prime constant is chosen before d=2 or
  d=3. Explicit versions also hold for every fixed d>=2, with dependence on
  d, and every zeta>=0 in the integer case. See
  [offset-pattern Rankin alignment](OFFSET_PATTERN_RANKIN_ALIGNMENT.md).
- Companion T4.2 is complete for the exact signed-offset certificate
  population, with one threshold before every source tuple and every length
  in the critical band. Each finite code selects source-value divisors and
  target offsets; proved coprime congruences give at most one centre per code.
  Uniform divisor subpolynomiality and logarithmic-width bounds yield
  N^epsilon. A stronger theorem allows product>=N and assumes only an upper
  logarithmic width bound. See
  [fixed-source certificate alignment](FIXED_SOURCE_PRODUCT_CERTIFICATE_ALIGNMENT.md).
- Companion T20.5 is complete for the actual positive windows, rational
  line and substituted polynomials. Two proportional pairs give a nonzero
  common even square class, excluded by directness. The full root lists
  have at most one common root. At most two physical coordinates account
  for all collisions, so disjoint equation supports require discarding at
  most two equations. Every remaining actual polynomial is squarefree, and
  their root sets are pairwise disjoint. Only first-window regularity is
  needed in the stronger theorem. See
  [offset-root separation alignment](OFFSET_ROOT_SEPARATION_ALIGNMENT.md).
- Article Lemma 7.2 is proved in full. The exact finite count includes all
  actual prime assignments and receiving congruences. The actual population
  vanishes above order N. Its factorial/exponential series majorant is
  proved, and the literal ceiling has scaled limit 2/A. A uniform factorial
  budget yields the weighted exponent -2*beta+4/A+epsilon for every
  epsilon>0. One threshold precedes all critical-band lengths and all
  finite counting orders. The stronger weighted statement allows beta>=0
  and u>=0. See [alignment](MODERATE_CERTIFICATE_ALIGNMENT.md).
- Article Lemma 7.3 is proved for actual saturation divisor witnesses,
  prime occurrences and receiving congruences. The explicit outgoing and
  incoming finite bounds are B^2*(B+1)^m and B^2*(2*exp(1)*B)^m. The
  actual simple graph's degree is the cardinality of the union of these
  neighborhoods. Its maximum degree is uniformly N^(2/A+epsilon), with
  one threshold before every critical-band length and every vertex. A
  separately defined larger relation only requires D>=N and satisfies
  the same neighborhood bounds. See [alignment](SATURATION_DEGREES_ALIGNMENT.md).
- Article Lemma 7.4 is proved for the exact admissible vertex family and
  actual finite graph degrees. Minimal covers with private vertices give
  disjoint partitions into stars and marked singletons. A finite polymer
  comparison and exact powerset weights give the source rational bound.
  Stronger star bounds hold at every nonnegative activity, retain the
  degree profile, and permit heterogeneous nonnegative vertex weights.
  The improved rational corollary holds for Delta*z<2. See
  [alignment](MARKED_GENERATOR_ALIGNMENT.md).
- Article Proposition 19.2 is proved for actual signed Poisson differences.
  The finite-kernel action identifies every coefficient. Exact factorial
  moments give the diagonal Charlier identity and all-order square-root
  norm bound. The exact negative interval, including integer-root cases,
  and finite telescoping give the four-mass formula. The constants at
  mean two are proved with the source normalization. The separate
  unnumbered lower coefficient bound is doubled. See
  [alignment](POISSON_DIFFERENCE_NORMS_ALIGNMENT.md).
- Companion T20.1 is proved for the actual shared odd-valuation prime
  pool and exact distinct offset population on any line. Canonical offset
  uniqueness, a primitive integer direction and the parametrization of
  every lattice point are proved. The whole product obeys the source
  3*N and 6*N*height(d) bounds. The source logarithmic majorant and its
  uniform o(B) estimate are proved with thresholds before all centers,
  lines and cutoffs. Stronger results need only first-window regularity
  and one direct pair, allow H=B, remove the count's additive one and give
  an absolute logarithmic constant. See
  [alignment](OFFSET_LINE_PRODUCT_ALIGNMENT.md).
- Companion T20.3 is proved in full for actual shared odd-valuation primes
  and unique offsets. Distinct prime products force an actual real plane;
  its bounded normal has every coordinate nonzero, and every further
  sufficiently large common divisor obeys the source offset equation.
  At most N centers lie on two distinct planes. Actual joint probabilities
  give B^18*N*p^2 and the uniform N^(-1+epsilon) primitive mass bound.
  First-two-window regularity suffices for the geometry; the mass estimate
  even needs only that first regular direct pair. Geometric distinction
  and the original ordered primitive population are explicit. See
  [alignment](OFFSET_PLANE_ALIGNMENT.md).
- Companion T19.2 is proved for the exact physical even square-product
  sets. Nonempty disjoint interval blocks partition precisely the deficient
  starts. The complete-boundary Fourier phase gives the zero/2p local
  marginals and the original block count has its actual Bernoulli law.
  The mean and absolute discrepancy identities, full-block contribution
  and at most two endpoint truncations are proved uniformly over every
  fixed critical band. The boundary correction improves from 2Lp to
  2(L-1)p, with a finer actual-length bound. No block independence is
  asserted. See [alignment](LOCAL_BLOCKS_ALIGNMENT.md).
- Companion T19.8 is proved for arbitrary compatible affine prescriptions
  on actual finite binary probability spaces. Every deletion trace obeys
  the exact rank charge, and a terminal trace is constructed. Each actual
  canonical direct component has the source centered/joint mass comparison.
  Rank additivity on restrictions and a size-weighted average construct a
  component with all source density, size and nullity bounds. The loss
  improves from p*2^t to p*2^(t-1), and the exact heterogeneous private-rank
  profile is retained. See [alignment](PRIVATE_RANK_PEELING_ALIGNMENT.md).
- Companion T19.7 is proved for the actual positive and total run counts
  under the infinite prime-sign measure. A constructed arithmetic cylinder
  has exact probability, and a finite residue-class argument bounds its
  positive starts. The proved sharp PNT and elementary limits give the
  source positive scaled-logarithmic liminf for every fixed t>2 along
  odd primes. The prime filter is proved nontrivial, the epsilon thresholds
  are explicit, and both original exponential moments eventually exceed
  every real level. No target moment or asymptotic estimate is a premise.
  See [alignment](PRIME_CYLINDER_ALIGNMENT.md).
- Companion T21.2 is proved in full. Its finite conditional rank bound,
  exact conditional start probabilities and conditional-mean budget are
  proved for actual infinite-model observations. A positive denominator
  is proved, and the complete row/square-class kernel equivalence retains
  local relations. The pool coefficient improves from p*2^(T-1) to
  p*(2^(T-1)-1)/T. The actual old windows give a logarithmic prime-pool
  budget, and the proved Euler bound and positive squares give matching
  pool exponents. Exact critical binary factors and integer floors prove
  both sides of the final N^(1/2-delta+o(1)) scale. One threshold precedes
  all critical lengths, old-window choices and realizable old vectors. See
  [alignment](CONDITIONAL_RANK_ALIGNMENT.md).
- Companion T1.15 is proved in full. Original consecutive windows have the
  complete fair relative-vector law and Mathlib independence from all
  old raw values, every conditional word probability, the literal rounded
  exceptional bound and its uniform fixed-j exponent. A constructed
  smaller exception set removes the separate contact term and halves
  the pool coefficient. Injective even-boundary embeddings and their
  transposes prove the actual selected-vector laws. Fixed dilations,
  arbitrary subsets, enlarged logarithmic widths, bounded positive height
  multiples and injective center changes are included uniformly before
  all old observation and pattern choices. See
  [alignment](FIXED_BRANCHING_ALIGNMENT.md).
- Mathematical improvements confirmed: `P1-MATH-0001`, weaker ambient algebra
  assumptions for Lemma 5.1; `P1-MATH-0002`, an entirely algebraic proof of
  companion T1.1 with its original constant; `P1-MATH-0003`, weaker cutoff
  hypotheses for all three parts of T1.3; `P1-MATH-0004`, a lower base bound
  alone and uniform shorter windows for local rigidity; `P1-MATH-0005`, a stronger
  local-square threshold; `P1-MATH-0006`, absolute critical-defect and free-component constants; `P1-MATH-0007`, the heterogeneous
  missing-block and tuple estimates; `P1-MATH-0008`, integer factor height
  without a primitive-factor hypothesis; `P1-MATH-0009`, the extended
  parameter interval for the exact moment perturbation, with its endpoint
  and enlarged uniform exponential constant stated explicitly; `P1-MATH-0010`,
  weaker parameter hypotheses for the weighted recurrence comparison and stability;
  `P1-MATH-0011`, an initially active coordinate budget and zero boundary
  parameters for coordinate regularisation; `P1-MATH-0012`, the sharper ternary
  incidence constant and a version without the three-block coloring;
  `P1-MATH-0013`, arbitrary fields and linear-form families for all of
  Lemma 6.1; `P1-MATH-0014`, its sharper independent-representation bound
  and extension to all zero-sum-free label supports; `P1-MATH-0015`, the
  square-root endpoint and explicit constants for the small-kernel count;
  `P1-MATH-0016`, removal of the zeta factor and the wider uniform interval
  with explicit constants under a logarithmic prime budget; `P1-MATH-0017`,
  the wider d and integer-tilt ranges for offset-pattern counts;
  `P1-MATH-0018`, a non-strict certificate product threshold and an upper
  logarithmic width condition for fixed sources; `P1-MATH-0019`,
  first-window regularity alone in the complete root-separation lemma;
  `P1-MATH-0020`, the wider beta and weight ranges for the weighted
  moderate-certificate estimate; `P1-MATH-0021`, the lower non-strict
  divisor threshold for saturation neighborhood bounds; `P1-MATH-0022`,
  stronger marked-graph generating bounds and heterogeneous vertex weights;
  `P1-MATH-0023`, a factor-two improvement of the elementary lower bound
  for the Poisson--Charlier correction coefficient; `P1-MATH-0024`,
  weaker regularity, directness and cutoff hypotheses for the line-product
  lemma; `P1-MATH-0025`, its sharper offset count and absolute logarithmic
  constant; `P1-MATH-0026`, weaker regularity hypotheses for forced planes
  and a larger population for the two-plane affine mass estimate;
  `P1-MATH-0027`, the sharper local-block endpoint correction;
  `P1-MATH-0028`, the factor-two positive-core improvement and its
  heterogeneous private-rank profile;
  `P1-MATH-0029`, the sharper incidence-slope coefficient in the finite
  conditional-mean pool budget;
  `P1-MATH-0030`, the smaller deterministic original-window exception set,
  with no separate contact term and half the pool coefficient;
  `P1-MATH-0031`, the pure-double-jump endpoint in the scalar criterion
  and the size-bias identity for any parameter in [0,m];
  `P1-MATH-0032`, a finite covered-rank bound including isolated components,
  with no separate defective-count estimate and weaker cutoff/separation
  hypotheses.
  No error in an original
  conclusion is asserted.
- Palomar registrations: none; preparation only.

The machine-readable [coverage ledger](manuscript-results.json) records the
individual status of every result. It records the exact original source block
hash and the original label, number, page and file. Preparatory lemmas do not
change these result statuses.

## Development sequence

1. Construct the completely multiplicative random sign model and run-start
   events, retaining both signs and the left boundary. Audit possible reuse
   of Paper C's finite and infinite prime-sign models.
2. Formalize effective square-class spaces, affine consistency, exact marginal
   probabilities and their finite-dimensional algebra; prove the full centered
   and first-excluded-prefix identities without independence assumptions.
3. Inventory every arithmetic literature input with its parameters and
   uniformity. Formalize the local/relative rank and channel estimates; separate
   fixed-order bounds from bounds with a growing number of blocks.
4. Formalize exact cumulant identities, reconstruction with every marginal
   retained, the fourth-order lower bound, the optimal quadratic error theorem,
   and explicit rational-channel refinements.
5. Complete companion coverage, including positional and supplementary results;
   reconcile each correction with the future manuscript revision.
6. Freeze a validated commit, prepare standalone statements and solutions,
   perform Comparator and kernel replay checks, then prepare Palomar records.

Each stage requires precise statement alignment and updated coverage, correction
and literature-input ledgers. This order is provisional and may be refined by
the dependency graph discovered during formalization.

## Growing critical-order exact branching

Companion T22.4 is complete. The actual old-value prime pool has a
proved uniform O_K(H^3/h) logarithmic budget. An explicit variable
Rankin tilt and a finite rational remainder prove the literal
(2/3)H-H*log(h)/(9h)+O_K(H/h) exponent. One positive envelope and
one threshold precede every j<=K*H/h, critical-band length and old
source choice. The retained full new relative vector is exactly fair
and independent of the entire old raw vector under the original
infinite measure. The smaller two-supported-value exception set of
P1-MATH-0030 suffices. See [alignment](CRITICAL_ORDER_BRANCHING_ALIGNMENT.md).
The full build passed (9,095 jobs), as did the actual audit of all
2,777 theorem/lemma declarations and all 647 coverage/finding names.
Coverage is 43 / 167, with 30 confirmed improvements. This proves no
growing-order factorial-moment estimate or principal Poisson theorem.

Validated implementation of companion T22.4:
[c5334aa55a0c179a93747cf2d3d6820d575b78dc](https://github.com/Vulkin-prog/paper-p1-lean/commit/c5334aa55a0c179a93747cf2d3d6820d575b78dc).

## Closed scalar recurrence criterion

Companion T19.11 is complete. An explicit Poisson Stein solution has
both unit factor bounds proved internally from finite cumulative/tail
balance. The actual Hermite reference is identified with the pushforward
of two independent Mathlib Poisson laws by (u,v)->u+2*v. Its stationary
identity and the literal 1/(1-2*theta) comparison are proved. The canonical
size-biased law, actual successor laws and their weighted mixture give
the exact second identity; the general identity needs only a positive
finite first moment. P1-MATH-0031 includes the pure-double-jump boundary
theta=mu and the arbitrary parameter form of that identity. Parameter
stability is also proved. No Stein factor or stationarity estimate is
an assumption. The inspected Paper C Stein modules remain unported.
See [alignment](SCALAR_RECURRENCE_ALIGNMENT.md).

The full build passed (9,113 jobs), as did the actual axiom audit of all
2,875 theorem/lemma declarations and all 672 coverage/finding names.
Coverage is 44 / 167, with 31 confirmed improvements. Original sources
are preserved; no Palomar submission or principal asymptotic is claimed.

Validated implementation of companion T19.11 and P1-MATH-0031:
[9ca5f8aecbbc79ecd99b0658bf2cb37fa414f842](https://github.com/Vulkin-prog/paper-p1-lean/commit/9ca5f8aecbbc79ecd99b0658bf2cb37fa414f842).

## Covered three-window relation spaces

Companion T20.7 is complete on the actual 3B formal window coordinates.
An arbitrary shared-prime hyperedge cover is identified with the ternary
valuation rows; after zeroing it the large-prime solution space equals
the constructed pinned graph space. Coordinate rank-nullity proves the
cover cost. Actual local injectivity and pairwise directness prove
that all free components missing a fixed block, including singletons,
number at most pi(H)+2. The finite bound is dim(R_D)<=c3(D)+3*pi(H)+6,
with no defective-vertex estimate. Every free component has its actual
positive product represented by a small-prime product times a square.
An explicit internal Chebyshev budget supplies the critical B/log(B)
rate uniformly before every triple and cover. C0=1 and overlapping
windows are permitted under the retained injectivity/directness
hypotheses; see P1-MATH-0032 and [alignment](COVER_RANK_ALIGNMENT.md).

The full build passed (9,135 jobs), as did the actual audit of all
2,927 theorem/lemma declarations and all 700 coverage/finding names.
Coverage is 45 / 167, with 32 confirmed improvements. No primitive-host
count, six-vertex mass estimate or Palomar registration is asserted.

Validated implementation of companion T20.7 and P1-MATH-0032:
[2ecbeb2a1c57c75e700e1efc63225a9107335400](https://github.com/Vulkin-prog/paper-p1-lean/commit/2ecbeb2a1c57c75e700e1efc63225a9107335400).


## Very small tails through a growing moment order

Companion T19.6 is complete. The actual prime pool after j<=K*(log N)^2
windows has a uniform quartic logarithmic budget. Rankin at sigma=3/4
and exact full-vector branching give actual factorial moments
F_k<=(2*N^(3/4+epsilon))^k through that entire growing range. A literal
ceiling order k=ceil(128*(log N)^2) proves
P(Z_N>b)<=exp(-2*(log N)^3) for every real b>=N^(9/10). The truncated
moments have the original exp(-(log N)^3/2) bound uniformly for
integer 0<=r<=log N. Both source ceilings are retained in passing to
the near-linear threshold. Every fixed c>0 is allowed, without the
smooth-pair input; this is P1-MATH-0033. See
[alignment](VERY_SMALL_TAIL_ALIGNMENT.md).

The full build passed (9,157 jobs), as did the actual axiom audit of all
2,969 theorem/lemma declarations and all 730 coverage/finding names.
Coverage is 46 / 167, with 33 confirmed improvements. The low-order
moment asymptotics and principal Poisson theorems remain open; no
Palomar registration is made. Ubuntu root free space is 17.76 GiB.

Validated implementation of companion T19.6 and P1-MATH-0033:
[79e4e6d814ac0dc941544b2beb92437e45657a39](https://github.com/Vulkin-prog/paper-p1-lean/commit/79e4e6d814ac0dc941544b2beb92437e45657a39).


## Quantified square-root effective support

Companion T19.5 is complete for the actual original count. The literal
rounded threshold sqrt(N)*exp(K*log(N)/(log(log(N)))^(2/3)) and both
source tail-moment conclusions are proved. The actual prime budget at
order ceil((log log N)^(2/3)) gives a finite factorial recurrence
initialized at F_0=1, with no bounded pair moment or fixed-order moment
input. The explicit coefficient K=E+D+r+log 4 is chosen before C;
only the N threshold depends on the critical-band width. This is
P1-MATH-0034. Every power threshold N^(1/2+eta) has the eventual bound
N^(-D), with constant one. See [alignment](EFFECTIVE_SUPPORT_ALIGNMENT.md).

The full build passed (9,165 jobs), as did the actual axiom audit of all
2,996 theorem/lemma declarations and all 757 coverage/finding names.
Coverage is 47 / 167, with 34 confirmed improvements. T19.4's stronger
initial-pair factorial estimate and the main Poisson asymptotics remain
open. No Palomar registration is made. Ubuntu root free space is 17.74 GiB.

Validated implementation of companion T19.5 and P1-MATH-0034:
[fa7ba5f5dd20098526dba859bb770a8ba73318f0](https://github.com/Vulkin-prog/paper-p1-lean/commit/fa7ba5f5dd20098526dba859bb770a8ba73318f0).


## Exact finite compression of the actual good-edge family

Article Lemma 3.5 is complete. The normalized union contains each value
once. Its actual parity map on even selections is injective with range
the sum of the two square-class spaces, and rank |U|-1. The finite
lower bound is (2-1/b)*L-1. There are at most (L+1)^2 integer motifs
in [-bL,bL], and one fixed-pattern anchor determines both centres.
The general finite result needs only one normalized coincidence and
private coordinates; local regularity follows automatically and no
affine compatibility or dependence premise is needed for compression.
The actual deterministic good-edge definition retains both of those
source properties and the leading slopes. This is P1-MATH-0035.
See [alignment](GOOD_EDGE_COMPRESSION_ALIGNMENT.md).

Four elementary channel arithmetic modules are ported from the pinned
Paper C snapshot, with exact blob attribution and a successful new
compiler build. The larger rational-channel-code module remains
unported. All even-image, normalization and motif bridges are new P1
proofs. The full build passed (9,191 jobs), as did the actual axiom
audit of all 3,078 theorem/lemma declarations and all 793
coverage/finding names. Coverage is 48 / 167: main 16 / 73,
companion 32 / 94, with 35 confirmed improvements. The pair mass
and complete profile remain open; no Palomar registration is made.
Ubuntu root free space is 17.72 GiB.

Validated implementation of article Lemma 3.5 and P1-MATH-0035:
[37c99c7ea71d70271902fd12d1b52494646ec919](https://github.com/Vulkin-prog/paper-p1-lean/commit/37c99c7ea71d70271902fd12d1b52494646ec919).


## Fixed-channel coefficient — partial T2.6 checkpoint

The literal coefficient gamma is a proved finite real maximum. Its
implicit denominator range has an exact finite cutoff, and its universal
bound gamma<=2/3 is closed by a coprime-divisor inequality. The checked
values are gamma_2:3=1/3, gamma_3:4=1/2 and gamma_8:9=2/3. The latter
proves sharpness of this finite coefficient across admissible fixed
channels; it does not prove sharpness of an actual rank loss or Palm
exponent. This is P1-MATH-0036. T2.6 remains in progress because its
aligned-target rank estimate, endpoint exceptions and old-prime
extension are open. See [partial alignment](FIXED_CHANNEL_GAMMA_ALIGNMENT.md).

The full build passed (9,195 jobs), as did the actual axiom audit of all
3,101 theorem/lemma declarations and all 816 coverage/finding names.
Coverage remains 48 / 167, with 36 confirmed improvements. No new
Paper C code or external mathematical assumption is introduced. Original
sources are preserved and no Palomar registration is made. Ubuntu root
free space is 18.16 GiB.

Validated coefficient checkpoint for T2.6 and P1-MATH-0036:
[b9ff1b2874b76ba8fe97e314db236980b2fe6e13](https://github.com/Vulkin-prog/paper-p1-lean/commit/b9ff1b2874b76ba8fe97e314db236980b2fe6e13).


## Uniform finite matching classes — partial T2.6 and T1.11

The two actual affine divisibility classes now have a two-sided error
at most 3 from interval length times their exact gcd density. Integer
Bezout coefficients identify each class, the intersection is exactly
the class modulo c, and finite inclusion-exclusion controls the error.
The bound is uniform in every integer parameter with no height cutoff.
The global density bound includes numerators beyond the finite gamma
range, giving B*gamma+3 and the two leading B/3+3, B/2+3 bounds.
Physical divisor fractions are classified separately as c=a or c=b,
d=1. This explicit finite remainder is P1-MATH-0037. See
[partial alignment](FIXED_CHANNEL_MATCHES_ALIGNMENT.md).

These initial results are divisibility-class counts. The actual-value and
physical-window bridges are proved in the later checkpoint below.
Residual rank and endpoint-source estimates remain open. T2.6 and T1.11 are in progress
and neither is counted complete. The full build passed (9,203 jobs),
as did the actual axiom audit of all 3,123 theorem/lemma declarations
and all 838 coverage/finding names. Coverage remains 48 / 167, with
37 confirmed improvements. Original sources are preserved; no Palomar
registration is made. Ubuntu root free space is 18.15 GiB.

Validated finite matching checkpoint for T2.6/T1.11 and P1-MATH-0037:
[84c4c9a4016ce9f1c4ab9f7828675f3495eced85](https://github.com/Vulkin-prog/paper-p1-lean/commit/84c4c9a4016ce9f1c4ab9f7828675f3495eced85).

## Actual compatible matching positions — partial T2.6 and T1.11

The actual target-position set now uses only the deduplicated normalized
source values. Its injective integer-offset map lands in the two counted
congruence classes. Positive actual pair mass gives deterministic start
separation and at most one true-window overlap. In both physical
fractions the resulting finite bound is B/b+2; all compatible strict
interior fractions satisfy B*gamma+3. The actual good-edge definition
supplies a positive integer source parameter. Positive actual triple
mass supplies both pair premises. This is P1-MATH-0038. See
[actual matching alignment](ACTUAL_TARGET_MATCHES_ALIGNMENT.md).

Residual normalized rank, endpoint exceptions and old-prime information
remain open, so T2.6 and T1.11 are not counted complete. The full build
passed (9,213 jobs), as did the actual axiom audit of all 3,144
theorem/lemma declarations and all 859 coverage/finding names. Coverage
remains 48 / 167, with 38 confirmed improvements. No external
mathematical assumption or new Paper C port is introduced. Original
sources remain unchanged and no Palomar registration is made. Ubuntu
root free space is 18.14 GiB.

Validated actual matching checkpoint for T2.6/T1.11 and P1-MATH-0038:
[4212bf9ec45186af0f1ce85ed9a6fea00542775e](https://github.com/Vulkin-prog/paper-p1-lean/commit/4212bf9ec45186af0f1ce85ed9a6fea00542775e).


## Uniform aligned residual rank — partial T1.9

The actual normalized full value kernel is uniformly o(B) for every
height b<=B^3. An explicit finite Runge--Hamming bound controls small
free components; the exact large-component budget is |S|/(K+1).
The omitted prime rows include the prime divisors of the dilation
coefficients, with their polynomial-height cost proved. The full pair
deficiency is bounded by (u-1)+epsilon*B, and by L/b+epsilon*B for
coprime channels, with one common critical-band threshold. This also
bounds the actual intersection rank and includes internal local defects.
One exact unit suffices; separation, compatibility and local regularity
are unnecessary. This is P1-MATH-0039. See
[alignment](ALIGNED_RESIDUAL_RANK_ALIGNMENT.md).

At this initial checkpoint T1.9 remained in progress pending its
fixed-height enlarged-cutoff assertion, completed below. The target quotient-rank and endpoint bridges for
T1.11/T2.6 remain open. The full build passed (9,245 jobs), and all
3,206 theorem/lemma declarations passed the actual axiom audit with
only propext, Classical.choice and Quot.sound. All 921 coverage/finding
names were checked directly by Lean. Coverage remains 48 / 167, with
39 confirmed improvements. No new Paper C port or external premise is
added. Original source bytes remain unchanged; no Palomar registration
is made. Ubuntu root free space is 18.09 GiB.

Validated uniform residual checkpoint for T1.9 and P1-MATH-0039:
[df34686b343f5297c181e6150e21834acc335ad8](https://github.com/Vulkin-prog/paper-p1-lean/commit/df34686b343f5297c181e6150e21834acc335ad8).


## Historical one-unit T1.9 checkpoint — scope corrected below

The last assertion is now proved on the actual large-prime value kernel.
Every nondefective normalized value has a private prime above the
interval width; all kernel coefficients there vanish. Restriction to the
actual defective values is injective. The proved local defect estimate
therefore gives O(B/log B) uniformly for every fixed height bound Q and
all enlarged cutoffs 2bL<=H<=D B. Its constant is chosen before the fixed
critical-band width. The full-kernel and full-pair-deficiency rates follow.
`AlignedPairTheorem.companion_T1_9` packages both uniform and fixed-height
assertions. See [statement alignment](ALIGNED_RESIDUAL_RANK_ALIGNMENT.md).

Coverage is now **49 / 167**: main 16 / 73, companion 33 / 94. The
39 confirmed improvements are retained; the historical P1-MATH-0039
validation continues to identify its initial uniform checkpoint. The
full build passed (9,253 jobs), and all 3,218 theorem/lemma declarations
passed the actual axiom audit with only propext, Classical.choice and
Quot.sound. All 933 coverage/finding names were checked directly by Lean.
Original source bytes are preserved, and no new Paper C port, external
mathematical premise or Palomar registration is introduced. Ubuntu root
free space is 18.08 GiB.

Validated complete companion T1.9:
[6165382c14d6f8e653ddec27accb9c042628ae10](https://github.com/Vulkin-prog/paper-p1-lean/commit/6165382c14d6f8e653ddec27accb9c042628ae10).


## Explicit dyadic source exceptions and target pools — partial T2.6/T1.11

The bounded-affine matching core now has finite integer separation,
actual endpoint-source sets, decoded target pools and explicit polynomial
counts. With H<=B^J and fixed J>=1, the source exception count is at
most (6(a+b)+2)*B^(J+2), and the pool for one fixed source parameter
has at most 6aB^(3J) targets. A common critical-band threshold is chosen
before all source and target data. Deterministic separation suffices for
the actual B*gamma+3 matching count; the compatible theorem derives it
from positive actual joint mass. This is P1-MATH-0040. See
[alignment](DYADIC_MATCHING_ALIGNMENT.md).

The bounded affine representation is explicit input data. Its construction
from the geometric alignment predicate, the actual quotient-rank bridge
and the old-information extension remain open. T1.11 and T2.6 are not
counted complete. Coverage remains 49 / 167, with 40 confirmed
improvements. The full build passed (9,271 jobs); all 3,250 theorem/lemma
declarations passed the actual axiom audit with only propext,
Classical.choice and Quot.sound, and all 965 coverage/finding names were
checked directly by Lean. No new Paper C source or external mathematical
hypothesis is introduced. Original manuscript bytes are preserved and no
Palomar registration is made. Ubuntu root free space is 18.05 GiB.

Validated bounded-affine dyadic checkpoint and P1-MATH-0040:
[1b87f9df9ba2c7a710a86f73443d39c7925abe63](https://github.com/Vulkin-prog/paper-p1-lean/commit/1b87f9df9ba2c7a710a86f73443d39c7925abe63).


## Actual finite target quotient rank and old prime information

The actual target deficiency is now bounded by true matching positions
plus the literal remaining-row kernel rank on the true scaled old/new
union. Its kernel characterization includes internal target defects.
Added old prime-coordinate bits are included whenever the finite discarded
row set contains them. One source unit suffices for this finite bridge;
source privacy, local regularity, compatibility and separation are
unnecessary for the rank step. Under the proved separated matching
hypotheses the resulting finite bound is B*gamma+3 plus the residual
row rank. This is P1-MATH-0041. See
[alignment](TARGET_QUOTIENT_RANK_ALIGNMENT.md).

The component estimates now control the whole discarded-row solution
space. Their application to the geometry of the actual combined target
union, and the construction of bounded affine data from geometric
alignment, remain open. T1.11 and T2.6 are in progress. Coverage remains
49 / 167, with 41 confirmed improvements. The full build passed
(9,285 jobs), all 3,294 theorem/lemma declarations passed the actual
axiom audit with only propext, Classical.choice and Quot.sound, and all
1,009 coverage/finding names were checked directly by Lean. No external
mathematical hypothesis or new Paper C source is introduced. Original
sources remain unchanged; no Palomar registration is made. Ubuntu root
free space is 18.04 GiB.

Validated finite target quotient-rank checkpoint and P1-MATH-0041:
[469f5ac7ab234cdd18962337291971682554d913](https://github.com/Vulkin-prog/paper-p1-lean/commit/469f5ac7ab234cdd18962337291971682554d913).


## Scope audit — T1.9 enlarged geometric alignment

Current coverage is corrected to **48 / 167** (main 16 / 73, companion
32 / 94). The earlier completion mapping of T1.9 checked its one-unit
subcase, but the source definition |b*x-a*y|<=(a+b)B also permits zero
units. The existing theorems remain proved with their literal hypotheses;
the wrapper is renamed `AlignedPairTheorem.one_unit_T1_9`. The zero-unit
case and the full enlarged-alignment geometry remain unfinished. T1.9 is
in progress. See [scope audit](FORMALIZATION_SCOPE_AUDIT.md). No change
to original manuscript bytes or to the Lean proof validity is involved.

Validated scope correction (full build 9,285 jobs; 3,294 audited declarations;
1,009 directly checked coverage/finding names):
[50889df7921f8374971c70d4d33878cc2a9326d4](https://github.com/Vulkin-prog/paper-p1-lean/commit/50889df7921f8374971c70d4d33878cc2a9326d4).

## Full enlarged-alignment T1.9 completed after the scope correction

Current coverage is **49 / 167** (main 16 / 73; companion 33 / 94).
The literal geometric inequality |b*x-a*y|<=(a+b)B now suffices,
including zero exact units. The true normalized union lies in an
explicit interval of radius 3*max(a,b)*B. The uniform residual argument
applies to it, and a separate finite two-even-space argument handles
the zero-unit pair deficiency. Both coefficient orientations are covered.

`EnlargedAlignedPairTheorem.companion_T1_9` gives the uniform unit-count
and channel bounds and the fixed-height enlarged-prime residual.
`fixed_height_loss` also gives the full pair deficiency at rate B/log B.
The fixed-height constant is chosen before the critical-band width.
Separation, compatibility and local regularity are unnecessary; internal
local defects are retained. This extends P1-MATH-0039; the number of
confirmed improvements remains 41. The prior one-unit coverage error and
its validation history remain explicit in the [scope audit](FORMALIZATION_SCOPE_AUDIT.md).

The full Lean v4.36.0-rc2 build passed (9,295 jobs); all 3,319 theorem/lemma
declarations passed the actual axiom audit with only propext,
Classical.choice and Quot.sound. All 1,034 coverage/finding names were
checked directly by Lean. All 138 manifest entries and all 167 source
statement hashes remain unchanged. No external mathematical input or
new Paper C port is introduced. T1.11/T2.6 remain in progress. No Palomar
registration is made. Ubuntu root free space is 18.01 GiB.

Validated full enlarged-alignment T1.9 (9,295 build jobs; 3,319 audited
declarations; 1,034 directly checked coverage/finding names):
[e4d183ed6e300f0352f6164c1c049cadfe0c0db4](https://github.com/Vulkin-prog/paper-p1-lean/commit/e4d183ed6e300f0352f6164c1c049cadfe0c0db4).

## Complete aligned-target rank — companion T1.11 and T2.6

Current coverage is **51 / 167** (main 16 / 73; companion 35 / 94).
The actual combined target union now has explicit interval geometry,
proved polynomial coefficient/prime budgets and uniform o(L) remaining-row
rank. The finite actual quotient-rank inequality therefore gives
(delta_Q)<=(gamma(a,b)+epsilon)*L, including internal target defects
and any old prime signs of a,b.

Literal alignment with the compressed centre constructs reduced affine
data with denominator and displacement <=B^5. The actual aligned-target
pool has size <=6*a*B^15. The symmetric source exception family has size
<=(12(a+b)+4)*B^7 and covers both source orientations. Actual source
parameters are extracted from one unit; private coordinates and dependence
supply it for raw geometric good pairs without source affine compatibility.
Compatible distinct actual targets supply deterministic separation.

`AlignedTargetSourceTheorem.companion_T2_6` includes gamma<=2/3 and
both separated and actual compatible conclusions.
`companion_T1_11` includes the exact leading coefficients 1/3 and 1/2,
with no source event premise. The common threshold precedes every source
and target choice. This extends existing improvements P1-MATH-0040 and
P1-MATH-0041; there are still 41 confirmed improvements. See the
[complete statement alignment](ALIGNED_TARGET_RANK_ALIGNMENT.md).

The full build passed (9,309 jobs), all 3,344 theorem/lemma declarations
passed the actual axiom audit, and all 1,059 coverage/finding names were
checked directly by Lean. Only propext, Classical.choice and Quot.sound
occur. All 138 manifest entries and all 167 original statement hashes
remain unchanged. No external mathematical input, new Paper C port,
manuscript revision or Palomar registration is introduced. Source mass,
Palm mean and the principal Poisson approximation remain open. Ubuntu
root free space is 17.99 GiB.

Validated complete T1.11/T2.6 (9,309 build jobs; 3,344 audited declarations;
1,059 directly checked coverage/finding names):
[3cc9dc9f816193e9488d32fab93f7aae9f9b6f90](https://github.com/Vulkin-prog/paper-p1-lean/commit/3cc9dc9f816193e9488d32fab93f7aae9f9b6f90).

## Article 13.7 completed — rank on a known alignment and exact contact

Current coverage is **52 / 167** (main 17 / 73; companion 35 / 94).
`KnownAlignmentRank.main_13_7` packages all three source assertions on
the actual intersection rank, with the stronger full pair deficiency
included. The fixed-tau estimate follows from T1.9 with zero additional
error after a tau-dependent threshold. No uniform assertion as tau varies
with N is made. The compatible uniform half bound and height-one o(B)
bound include the exact contact distance L, where the true windows share
at most one position.

This is a proof simplification from the already proved residual estimate:
short-basis extraction and norm-polynomial witnesses are unnecessary for
this known-line result. P1-MATH-0042 records that replacement and its
stronger full pair-deficiency scope. There are 42 confirmed improvements.
See the [full statement alignment](KNOWN_ALIGNMENT_RANK_ALIGNMENT.md).

The full build passed (9,311 jobs), all 3,349 theorem/lemma declarations
passed the actual axiom audit, and all 1,064 coverage/finding names were
checked directly by Lean. Only propext, Classical.choice and Quot.sound
occur. Original source bytes and all statement hashes remain unchanged.
The nonaligned rank and triple results remain open. No new external
mathematical input, Paper C port, manuscript revision or Palomar registration
is introduced. Ubuntu root free space is 17.98 GiB.

Validated complete article 13.7 and P1-MATH-0042 (9,311 build jobs;
3,349 audited declarations; 1,064 directly checked coverage/finding names):
[0b7945eff438d61604f6a3aea0bc33f7263372e9](https://github.com/Vulkin-prog/paper-p1-lean/commit/0b7945eff438d61604f6a3aea0bc33f7263372e9).

## Finite channel computation — selection counts, placements and closed sums

The unnumbered finite calculation preceding article 3.3 is complete.
`ChannelSelectionCount` constructs an explicit equivalence between actual
binary even selections with prescribed extremes and the interior zero-sum
space, proving the exact A_d weights. `ChannelPlacements` proves the
literal within-window placement count and predecessor-signed sum, retaining
signed contact -1 at diameter L. Their pair products are exactly U and S.

`ChannelSumIdentity` proves all three weighted moments, their positive
interval indexing, the closed algebraic identity for arbitrary integer
shift s, Euclidean specialization, empty sums and both exact leading
signed formulas. Positivity, coprimality and the remainder range are
unnecessary for the generic algebraic identity. P1-MATH-0043 records this
generality and explicit counting interpretation; there are 43 confirmed
improvements. See the [finite alignment](FINITE_CHANNEL_SUMS_ALIGNMENT.md).

Coverage remains **52 / 167**. Article 3.3 and companion T2.5 are in
progress: actual source translation counts, exceptional normalization
costs, full pair mass and asymptotic equivalents are not supplied by these
finite identities. The full build passed (9,317 jobs); all 3,375
theorem/lemma declarations passed the actual axiom audit, and all 1,090
coverage/finding names were checked directly by Lean. Only propext,
Classical.choice and Quot.sound occur. All original source bytes are
preserved. No external mathematical input, Paper C port, manuscript
revision or Palomar registration is introduced. Ubuntu root free space
is 17.98 GiB.

Validated finite channel checkpoint and P1-MATH-0043 (9,317 build jobs;
3,375 audited declarations; 1,090 directly checked coverage/finding names):
[67187ee05582f888683838e0d09f0509a0157867](https://github.com/Vulkin-prog/paper-p1-lean/commit/67187ee05582f888683838e0d09f0509a0157867).

## Actual dyadic source translations with a common growing-height threshold

`SourceTranslationInterval` proves the exact ceiling interval for t and
its equivalence with all four actual dyadic inequalities. Its two-sided
finite count differs from N*(2/b-1/a) by at most B/a+B/b+1.
`ActualSourceTranslations` constructs the bijection with the actual
source-pair set at each fixed pair of source-unit indices. The predecessor
offset -1 is included. For strict N>(a+b)B, forward and reverse families
are disjoint; their union differs from N*w(a,b) by at most 6B.
Both leading coefficients are exactly w(2,3)=w(3,4)=1/3.

`SourceTranslationCount.all_heights` chooses one critical-band threshold
before every reduced a<b<2a with b<=B^3 and every within-window index
choice. The errors are <=3B in one orientation and <=6B in both.
P1-MATH-0044 records these explicit constants and stronger quantifiers;
there are 44 confirmed improvements. See the
[actual translation alignment](SOURCE_TRANSLATIONS_ALIGNMENT.md).

Coverage remains **52 / 167**. Article 3.3 and companion T2.5 remain
in progress: relation-word host summation, probability/mass identification
and defective-normalization errors are still open. Fixed-index counting
is not an unweighted union over all index choices. The full build passed
(9,323 jobs), all 3,394 theorem/lemma declarations passed the actual axiom
audit, and all 1,109 coverage/finding names were checked directly by Lean.
Only propext, Classical.choice and Quot.sound occur. Original sources are
preserved. No new external mathematical input, Paper C port, manuscript
revision or Palomar registration is introduced. Ubuntu root free space
is 17.97 GiB.

Validated actual translation checkpoint and P1-MATH-0044 (9,323 build jobs;
3,394 audited declarations; 1,109 directly checked coverage/finding names):
[fc4c31d1a01ccb880d28fa6cdbd1d30040e054df](https://github.com/Vulkin-prog/paper-p1-lean/commit/fc4c31d1a01ccb880d28fa6cdbd1d30040e054df).

## Weighted canonical-pattern translations — preserve the signed main term

The actual translation counts are now summed over the finite family of
positive unit gaps and both true within-window placements. Pattern weights
are A_d, with the actual predecessor sign in each block. The dependent
finite sum is proved equal to the literal nested sums. Its positive and
signed total weights are exactly U and S; U>=0 and |S|<=U are also proved.

`ChannelWordHosts.unsigned_error` and `signed_error` retain main terms
N*w*U and N*w*S with explicit error <=6B*U. The signed term preserves
predecessor cancellations. `ChannelWordHostCount.all_heights` gives one
common threshold before all reduced channel heights b<=B^3 and patterns.
This extends P1-MATH-0044; the number of confirmed improvements stays 44.
See the [weighted pattern alignment](CHANNEL_WORD_HOSTS_ALIGNMENT.md).

Coverage remains **52 / 167**. The aggregate is not yet identified with
the actual complete unit-relation/Fourier or joint-probability contribution.
That bridge, defective-normalization removal, full fixed-channel mass and
complete pair profile remain open. The full build passed (9,329 jobs),
all 3,409 theorem/lemma declarations passed the actual axiom audit, and
all 1,124 coverage/finding names were checked directly by Lean. Only
propext, Classical.choice and Quot.sound occur. Original sources are
preserved. No external mathematical input, Paper C port, manuscript
revision or Palomar registration is introduced. Ubuntu root free space
is 17.96 GiB.

Validated weighted canonical-pattern checkpoint (9,329 build jobs;
3,409 audited declarations; 1,124 directly checked coverage/finding names):
[88ce8a72b7b579b3b7442de98efd91af4b445764](https://github.com/Vulkin-prog/paper-p1-lean/commit/88ce8a72b7b579b3b7442de98efd91af4b445764).

## Exact private intersection and actual even-unit coefficient equivalence

`PrivateEvenIntersection.space_inter` identifies the actual private common
class space with the even image of the true value intersection. The proof
restricts actual coefficients and preserves their total sum and combination.
An explicit linear equivalence is constructed, with injectivity and
surjectivity proved separately. `UnitIntersectionEquiv` gives the actual
unit/value bijection and transports zero-sum coefficients to the actual
intersection S_x cap S_y. Its forward prime-parity combination is identified
exactly, not merely by rank.

Under private normalized coordinates, the actual intersection rank and
full pair deficiency both equal (u-1)_+, including u=0 or 1. Coprimality,
height, separation and affine compatibility are unnecessary for this
classification. The full union-image compression still needs a shared
value. This extends P1-MATH-0035; there are still 44 confirmed improvements.
See the [exact coefficient alignment](EXACT_UNIT_INTERSECTION_ALIGNMENT.md).

Coverage remains **52 / 167**. Affine character signs, selected-unit word
enumeration into canonical patterns, actual Fourier/probability identification
and defective-normalization removal remain open for article 3.3/T2.5.
The full build passed (9,337 jobs), all 3,425 theorem/lemma declarations
passed the actual axiom audit, and all 1,140 coverage/finding names were
checked directly by Lean. Only propext, Classical.choice and Quot.sound
occur. Original sources are preserved. No new external mathematical input,
Paper C port, manuscript revision or Palomar registration is introduced.
Ubuntu root free space is 17.95 GiB.

Validated exact unit-coefficient checkpoint (9,337 build jobs;
3,425 audited declarations; 1,140 directly checked coverage/finding names):
[4461d6bdcc7e19648377fe47703c3bd0d14d21ee](https://github.com/Vulkin-prog/paper-p1-lean/commit/4461d6bdcc7e19648377fe47703c3bd0d14d21ee).

## Actual affine signs and private pair covariance

`StartVertexSign` derives the predecessor coefficient as the character
of an actual even true-window selection. `UnitAffineSigns` evaluates
the actual common unit class at separate local solutions; complete
multiplicativity and zero-sum coefficients cancel both dilation constants.
The paired sign is exactly the sum of the two predecessor parities.

`PairFourierIntersection.full_support_family_sum` explicitly reindexes
full-support pair relations by their nonzero common vectors.
`PairSquareClassFourier` retains heterogeneous actual marginals and
permits arbitrary actual local witnesses. Its actual infinite-measure
pair moment equals q-p_x*p_y for distinct centres.

`PrivateUnitCovariance` composes the exact unit equivalence and character
calculation. Privacy supplies both full local ranks and hence p_x=p_y=p.
The actual covariance is p^2 times the signed nonzero even-unit sum,
and the actual joint mass is p^2*(1+signedUnitSum). Joint compatibility,
separation, coprimality and height restrictions are unnecessary. In
particular, probability-zero pairs retain their signed cancellations.
See the [complete bridge alignment](PRIVATE_UNIT_COVARIANCE_ALIGNMENT.md).

This extends P1-MATH-0035. There are still 44 confirmed improvements,
and numbered coverage stays **52 / 167**. Actual selected-unit words
still require enumeration by canonical patterns, and defective
normalization removal, baseline correction and full mass/profile
asymptotics remain unfinished for article 3.3 and companion T2.5.
The full build passed (9,347 jobs), all 3,446 theorem/lemma declarations
passed the actual axiom audit, and all 1,161 coverage/finding names were
checked directly by Lean. Only propext, Classical.choice and Quot.sound
occur. Original sources are preserved. No new external mathematical
input, Paper C port, manuscript revision or Palomar registration is
introduced. Ubuntu root free space is 17.93 GiB.

Validated actual private pair covariance checkpoint (9,347 build jobs;
3,446 audited declarations; 1,161 directly checked coverage/finding names):
[c4d65eee4e0d0efc81a7e16fcc17538546ba5cdd](https://github.com/Vulkin-prog/paper-p1-lean/commit/c4d65eee4e0d0efc81a7e16fcc17538546ba5cdd).

## Actual selected-unit word bijection and fixed-pair signed enumeration

`BinaryEvenSelections` identifies actual nonzero even coefficient vectors
with nonempty even selected subsets. `ExactUnitProgression` derives the
primitive step (a,b) and constructs every intermediate fitting exact unit.
`SelectedUnitExtrema` proves unique selected endpoints and a unique
positive gap d<=L/b, with the literal within-window placements.

`SelectedUnitWordBijection.canonicalEquiv` is an explicit finite bijection
between these actual subsets and their fitting endpoint-selected words.
Both injectivity and surjectivity are proved on the actual unit indices.
`ChannelGapWords` proves the exact A_d cardinality and shows that every
word at a shape has the same two predecessor placement signs.
`SelectedUnitFourierEnumeration.signed_unit_enumeration` transports the
actual signed nonzero even-unit sum to the integer weighted shape sum
for each fixed pair. The arithmetic enumeration imposes no privacy,
separation or affine compatibility. Its actual probability use retains
the private normalized-union hypothesis of the earlier covariance formula.
See the [local word alignment](SELECTED_UNIT_WORDS_ALIGNMENT.md).

This extends P1-MATH-0043; there remain 44 confirmed improvements.
Coverage stays **52 / 167**. The global reindexing over actual dyadic
hosts into the canonical-pattern/source translation sum remains open,
as do defective normalization removal, baseline correction and the
full mass/profile estimates and phase equivalents for article 3.3/T2.5.
The full build passed (9,361 jobs), all 3,492 theorem/lemma declarations
passed the actual axiom audit, and all 1,207 coverage/finding names were
checked directly by Lean. Only propext, Classical.choice and Quot.sound
occur. No new literature input, Paper C port, manuscript revision or
Palomar registration is introduced. Manuscript bytes remain unchanged.
Ubuntu root free space is 17.91 GiB.

Validated actual local word-enumeration checkpoint (9,361 build jobs;
3,492 audited declarations; 1,207 directly checked coverage/finding names):
[75b7018923d2fc85473e609a5788b6bb97805498](https://github.com/Vulkin-prog/paper-p1-lean/commit/75b7018923d2fc85473e609a5788b6bb97805498).

## Actual dyadic signed unit aggregate and height-uniform error

`UnitShapePatterns.patternEquiv` reindexes actual pair-specific fitting
shapes by global patterns carrying the corresponding exact source unit.
`DyadicUnitWordHosts` proves the literal source-pair filter identity,
finite sum interchange and the exact two-orientation source cardinality.
`DyadicUnitFourierAggregate` transports these identities to the actual
real signed nonzero even-unit sum over all dyadic centres. Twice the
forward sum is exactly the earlier signed canonical-pattern aggregate.
It therefore has signed main term N*w*S and explicit error <=6B*U.
`DyadicUnitFourierCount.all_heights` gives one critical-band threshold
before every reduced positive a<b<2a with b<=B^3. See the
[complete global bridge](DYADIC_UNIT_FOURIER_ALIGNMENT.md).

This extends P1-MATH-0044, leaving 44 confirmed improvements. The
summed expression is the actual rational-unit Fourier contribution;
on private normalized pairs its p^2 multiple is the actual covariance.
No complete covariance identity is asserted on nonprivate hosts.
Defective-normalization removal, the p^2 baseline correction and full
mass/profile asymptotics and phase equivalents remain unfinished.
Article 3.3 and T2.5 remain in progress; coverage stays **52 / 167**.

The full build passed (9,369 jobs), all 3,506 theorem/lemma declarations
passed the actual axiom audit, and all 1,221 coverage/finding names were
checked directly by Lean. Only propext, Classical.choice and Quot.sound
occur. Current finding summaries have also been synchronized with the
already validated covariance and local-word extensions; their earlier
validation commits and histories are retained. No new literature input,
Paper C port, manuscript revision or Palomar registration is introduced.
Original sources are unchanged. Ubuntu root free space is 17.90 GiB.

Validated actual dyadic unit-Fourier checkpoint (9,369 build jobs;
3,506 audited declarations; 1,221 directly checked coverage/finding names):
[74727a964e38c4b8b556fac2f93194485c695c11](https://github.com/Vulkin-prog/paper-p1-lean/commit/74727a964e38c4b8b556fac2f93194485c695c11).

## Actual normalized-defect hosts, source separation and rational-unit weights

`NormalizedPrivateDefects` proves the exact cutoff-private/nondefective
equivalence on a finite actual set of diameter less than H. For a true
normalized source union, H>=2bB suffices. `NormalizedDefectSources`
extracts an actual defective normalized vertex and injects its source
family, at fixed unit and vertex indices, into the positive defect list.
The explicit finite bound is 2B^3 times the positive H-defect count below
b(2N+L). `NormalizedDefectSourceCount.bad_sources_rate` derives the
actual N^(1/2+epsilon) host count, with one threshold before all critical
lengths and integer H in [2bB,DB], for fixed a,b,D.

`UnitFourierWeight` proves |signedUnitSum|<=2^((u-1)_+)-1 and then
<=2^(B/b), without a private-coordinate or joint-compatibility premise.
The signed sum vanishes at zero or one unit. `FixedChannelSourceGeometry`
proves fixed-index source count <=N, total unit-host count <=B^2*N and
deterministic separation under N>(a+b)B. The polynomial baseline count
is deliberately recorded at its actual strength. See the
[exceptional-host alignment](NORMALIZED_DEFECT_HOSTS_ALIGNMENT.md).

This extends P1-MATH-0044; there remain 44 confirmed improvements.
The final combination into the actual retained private-channel mass,
its p^2 baseline and critical-scale error comparison remains unfinished,
as do the full mass/profile estimates and phase equivalents. Article 3.3
and T2.5 remain in progress; coverage stays **52 / 167**.
The full build passed (9,379 jobs), all 3,525 theorem/lemma declarations
passed the actual axiom audit, and all 1,240 coverage/finding names were
checked directly by Lean. Only propext, Classical.choice and Quot.sound
occur. There is no new literature input, Paper C port, manuscript revision
or Palomar registration. Manuscript bytes are unchanged. Ubuntu root
free space is 17.87 GiB.

Validated actual normalized exceptional-host checkpoint (9,379 build jobs;
3,525 audited declarations; 1,240 directly checked coverage/finding names):
[bd95627543139b4690c1311ce84f622d8ce7a221](https://github.com/Vulkin-prog/paper-p1-lean/commit/bd95627543139b4690c1311ce84f622d8ce7a221).

## Actual retained channel mass and direct bad-term deletion

`PrivateChannelSources` defines the actual cutoff-private source family
with at least two exact units, retains probability-zero pairs and proves
its deterministic order/separation and disjoint symmetric orientations.
Its literal sum of actual joint probabilities is twice the forward mass.
The actual private covariance formula gives its exact p^2 baseline and
signed unit contribution.

`PrivateChannelRemoval` partitions the full dyadic rational-unit sum
into the retained and bad terms, using zero/one-unit vanishing. The bad
sum has absolute value <=#badSources*2^(B/b), without a privacy or complete
residual-nullity premise. `PrivateChannelMassBound` proves the exact mass
identity and the finite error

    |M-p^2*N*w*S| <= p^2*(6B*U+2B^2*N+2*#badSources*2^(B/b)).

This is P1-MATH-0045, a verified simplification of the fixed-channel mass
route: bad rational-unit terms can be deleted before applying the actual
private probability identity. It is unnecessary to estimate the complete
nullity of defective pairs for this finite reduction. The proved coarser
B^2*N baseline is retained at its actual strength. See the
[actual mass alignment](PRIVATE_CHANNEL_MASS_ALIGNMENT.md).

There are now **45 confirmed improvements**. Coverage stays **52 / 167**:
the critical-scale comparison, unsigned channel-sum bound and positive
fixed-channel phase equivalent remain unfinished for T2.5, as do the
other arithmetic regimes of the complete main pair profile.
The full build passed (9,385 jobs), all 3,538 theorem/lemma declarations
passed the actual axiom audit, and all 1,253 coverage/finding names were
checked directly by Lean. Only propext, Classical.choice and Quot.sound
occur. No new literature input, Paper C port, manuscript revision or
Palomar registration is introduced. Original sources are preserved.
Ubuntu root free space is 17.86 GiB.

Validated actual finite channel-mass checkpoint (9,385 build jobs;
3,538 audited declarations; 1,253 directly checked coverage/finding names):
[37e67975065e2b4df18be484c2e7ba9123a6c8b9](https://github.com/Vulkin-prog/paper-p1-lean/commit/37e67975065e2b4df18be484c2e7ba9123a6c8b9).

## Actual fixed-channel remainder improved to an explicit O(B^2/N)

`ChannelUnsignedBound` proves U<=B^2*2^floor(L/b), including the empty
sum, by the exact weight moment and literal placement counts.
`CriticalChannelPowers` gives explicit bounds on 2^L, 2^(B/b) and p^2
in the actual critical band. `FixedChannelErrorAlgebra` compares the
three finite error terms: with b>=3, the actual exceptional host count
at exponent 7/12 and its root weight give a contribution below N^-1.
The endpoint term uses the eventual B<=N^(2/3) bound.

`PrivateChannelMassRate.mass_error_square_log` proves the actual mass
remainder <=K(C,b)*B^2/N, with
K(C,b)=(2^C)^2*(8*2^((C+1)/b)+2)>0. For each fixed reduced channel and
natural D, one threshold precedes all critical lengths and integer H
in [2bB,DB]. `mass_error_rpow` gives the source N^(-1+epsilon) error
for every epsilon>0. See the
[critical mass-rate alignment](PRIVATE_CHANNEL_MASS_RATE_ALIGNMENT.md).

This strengthens P1-MATH-0045; there remain 45 confirmed improvements.
The positive fixed-channel phase equivalent and any literal real-cutoff
convention transport remain unfinished. T2.5 therefore stays in progress,
as does the complete main 3.3 pair profile. Coverage stays **52 / 167**.
The full build passed (9,393 jobs), all 3,549 theorem/lemma declarations
passed the actual axiom audit, and all 1,264 coverage/finding names were
checked directly by Lean. Only propext, Classical.choice and Quot.sound
occur. No new literature input, Paper C port, manuscript revision or
Palomar registration is introduced. Manuscript bytes are unchanged.
Ubuntu root free space is 17.85 GiB.

Validated actual fixed-channel remainder checkpoint (9,393 build jobs;
3,549 audited declarations; 1,264 directly checked coverage/finding names):
[b19ae93509861774fd90f72c07a8d452603e5fc5](https://github.com/Vulkin-prog/paper-p1-lean/commit/b19ae93509861774fd90f72c07a8d452603e5fc5).

## Complete actual fixed-channel mass — companion T2.5

Companion T2.5 is complete. `FixedChannelMassTheorem.companion_T2_5`
proves both the actual mass asymptotic and positive phase for the literal
symmetric ordered separated source family, including actual zero-probability
pairs and any fixed real private-prime coefficient D>=2b.
`RealPrivateChannelSources` proves exact floor transport and cutoff bounds;
the literal separation filter is proved eventually redundant, rather than
omitted as an assumption. Both orientations are transported from the
canonical forward normalization.

`SignedChannelLeadingBounds` gives explicit positive coefficients and,
for L>=10b^3, L*2^floor(L/b)<=8b*S and S<=4b*L*2^floor(L/b).
`ChannelMainTermBounds` and `PrivateChannelMassPhase` combine actual
critical powers and the already proved remainder to establish positive
two-sided constants times L*N^(-1+1/b) for the actual mass.
The source N^(-1+epsilon) error and the stronger explicit K(C,b)*B^2/N
remainder are both retained. Every threshold precedes all critical
lengths, with the channel and real cutoff fixed before it. See the
[complete source alignment](FIXED_CHANNEL_MASS_ALIGNMENT.md).

Coverage is now **53 / 167** (main 17 / 73; companion 36 / 94), with
45 confirmed improvements. Main Theorem 3.3 remains in progress: T2.5
closes its fixed-channel mass input, not the other arithmetic regimes
or complete pair profile. This extends MATH-0043, MATH-0044 and MATH-0045.
The full build passed (9,405 jobs), all 3,577 theorem/lemma declarations
passed the actual axiom audit, and all 1,292 coverage/finding names were
checked directly by Lean. Only propext, Classical.choice and Quot.sound
occur. No new literature input, Paper C port, manuscript revision or
Palomar registration is introduced. Original sources are unchanged.
Ubuntu root free space is 17.83 GiB.

Validated complete companion T2.5 checkpoint (9,405 build jobs;
3,577 audited declarations; 1,292 directly checked coverage/finding names):
[b71d4e7409dccd61850024f99066ecaa24c6bccd](https://github.com/Vulkin-prog/paper-p1-lean/commit/b71d4e7409dccd61850024f99066ecaa24c6bccd).

## Complete actual selected-kernel counts (companion T1.6)

Both assertions of T1.6 are proved for the actual separated mixed rational-square
pair family and actual dyadic windows with one small kernel. One critical-band
threshold precedes every length and real cutoff 1<=T<=3N. The stronger estimate
permits all T>0 and tau=1/2, and the finite intermediate pair family also allows
odd selections and overlapping windows. Exact canonical support fibres, private
large primes and the residue-assignment count are proved; no asymptotic or
probabilistic bound is assumed. Explicit finite constants and the r>N CRT
case are P1-MATH-0046. See [alignment](LARGE_SELECTED_KERNEL_ALIGNMENT.md).

The full build passed (9,427 jobs); all 3,626 declarations passed the actual
axiom audit, with only propext, Classical.choice and Quot.sound. Numbered
coverage is 54/167 (article 17/73, companion 37/94). Original manuscript
bytes are unchanged. The remaining small-kernel and nonaligned geometric
regimes for main 3.2 and 3.3 are still open.

All 1,341 distinct coverage/finding declaration names were checked directly
by Lean against the compiled root import.

Validated complete companion T1.6 checkpoint (9,427 build jobs;
3,626 audited declarations; 1,341 directly checked coverage/finding names):
[3be7415366bd3d27aa016bf9690b0f93d7304fd9](https://github.com/Vulkin-prog/paper-p1-lean/commit/3be7415366bd3d27aa016bf9690b0f93d7304fd9).

## Verified large-kernel branch for fixed-support tuples

`LargeKernelTupleCounts.large_branch` proves the actual large-selected-kernel
branch with the source exponent, after a proved choice of tau following
epsilon. Exact receiver prime partitions give the finite cost
4^m*N^m/K, retaining all additive terms even for group moduli>N. Scaled
canonical support weights and actual marked-anchor encodings prove the
full uniform tuple count before the beta_s specialization. The broader
intermediate families allow non-even selections, repeated centres and
overlapping windows. This improvement is P1-MATH-0047.

Companion T1.14 remains in progress, with its all-small-kernel regime and
compressed fixed-width/dilation assembly open. Coverage remains 54/167;
47 mathematical improvements are confirmed. See
[large-kernel branch alignment](LARGE_KERNEL_TUPLES_ALIGNMENT.md).

The full build passed (9,441 jobs); the actual audit passed for all
3,655 theorem/lemma declarations, permitting only propext, Classical.choice
and Quot.sound. All 1,370 distinct coverage/finding declaration names
were checked directly by Lean. Original manuscript bytes are unchanged.

Validated large-kernel tuple-branch checkpoint (9,441 build jobs;
3,655 audited declarations; 1,370 directly checked coverage/finding names):
[8fa5f5d3988280093242c5b3fce68a506d9d1c80](https://github.com/Vulkin-prog/paper-p1-lean/commit/8fa5f5d3988280093242c5b3fce68a506d9d1c80).

## One-small-kernel count for arbitrary fixed-width selected blocks

The first assertion of T1.13 is proved by
`FixedWidthSmallKernel.one_kernel_real_cutoff`. The actual selected subsets
may vary with the integer centre. Real width and upper height constants
are covered by proved natural-ceiling inequalities; real prime thresholds
are transported exactly by their floor. A finite positive-value injection
gives the explicit offset count, and one threshold precedes every centre,
selected subset, critical length, cutoff and nonnegative real T. The
one-kernel assertion needs no lower centre or prime/diameter comparison.
This extends P1-MATH-0046. Full T1.13 remains in progress, with its
two-small-kernel assertion open. Coverage remains 54/167 and there are
47 confirmed improvements. See
[statement alignment](FIXED_WIDTH_SMALL_KERNEL_ALIGNMENT.md).

The full build passed (9,447 jobs); all 3,667 declarations passed the
actual axiom audit, permitting only propext, Classical.choice and
Quot.sound. All 1,382 distinct coverage/finding names were checked
directly by Lean. Original manuscript bytes are unchanged.

Validated selected fixed-width one-kernel checkpoint (9,447 build jobs;
3,667 audited declarations; 1,382 directly checked coverage/finding names):
[77be471d8c127edb6104caae2922aaef3a95ec54](https://github.com/Vulkin-prog/paper-p1-lean/commit/77be471d8c127edb6104caae2922aaef3a95ec54).

## Coefficient-independent bivariate grid ingredient of T1.4

`BivariateGridCount.homogeneous_integer_box_bound` proves the explicit
d*(2H+1) count for a positive-degree homogeneous polynomial at a nonzero
level in an actual integer box. A proved Schwartz-Zippel argument handles
all coefficients, the zero polynomial and powers of linear forms without
manual exceptional-full-fibre cases. This simplification is P1-MATH-0048.
Companion T1.4 remains in progress: the eliminant construction, determinant
method, other curve cases and lattice summations are still open. Coverage
remains 54/167, with 48 confirmed improvements. See
[alignment](BIVARIATE_GRID_ALIGNMENT.md).

The full build passed (9,477 jobs); all 3,677 declarations passed the
actual axiom audit, permitting only propext, Classical.choice and
Quot.sound. All 1,392 distinct coverage/finding names were checked
directly by Lean. Available Ubuntu-root space is 17.75 GiB after the
selected dependency downloads. Original manuscript bytes are unchanged.

Validated bivariate grid checkpoint (9,477 build jobs; 3,677 audited
declarations; 1,392 directly checked coverage/finding names):
[227b402575302cfdd178e7820c980874611a57c5](https://github.com/Vulkin-prog/paper-p1-lean/commit/227b402575302cfdd178e7820c980874611a57c5).

### Primitive denominator budget in T1.4 Step 3

`PrimitiveDenominators` proves that q divides R*Rprime from the two
concrete coprime-coordinate divisibilities, using a direct gcd argument
for arbitrary exponents. The actual signed choices cost at most
2*tau(|R*Rprime|). The existing elementary divisor bound gives a common
N^epsilon threshold at every fixed polynomial resultant height, before
all coordinates, exponents and finite denominator families. This extends
P1-MATH-0048. Actual resultant/eliminant construction and full T1.4
remain open; coverage stays 54/167, with 48 confirmed improvements.

The full build passed (9,479 jobs); all 3,683 declarations passed the
actual axiom audit, permitting only propext, Classical.choice and
Quot.sound. All 1,398 distinct coverage/finding names were checked
directly by Lean. Original manuscript bytes are unchanged.

Validated primitive denominator checkpoint (9,479 build jobs;
3,683 audited declarations; 1,398 directly checked coverage/finding names):
[a2aa7351c69460372795ffbe55fc41123821d382](https://github.com/Vulkin-prog/paper-p1-lean/commit/a2aa7351c69460372795ffbe55fc41123821d382).

### Actual two-chart resultant divisibilities

`ResultantDivisibility` constructs homogenized Bezout identities and
proves that padded coefficient reflection exchanges homogeneous
coordinates. The actual form evaluations give both chart divisibilities
and primitive cancellation gives q dividing the actual product R*Rprime.
Nonzero padded resultants are proved under explicit univariate
coprimality and full-degree conditions, including the integer-to-Q map.
The signed denominator family may vary its primitive coordinate witness
with q; its count is <=2*tau(|R*Rprime|) and uniformly N^epsilon at
fixed product height. This extends P1-MATH-0048. Source chart extraction,
nondegeneracy and height, eliminant construction and full T1.4 remain
open. Coverage stays 54/167, with 48 confirmed improvements. See
[actual resultant alignment](RESULTANT_DENOMINATORS_ALIGNMENT.md).

The full build passed (9,489 jobs); all 3,693 declarations passed the
actual axiom audit, permitting only propext, Classical.choice and
Quot.sound. All 1,408 distinct coverage/finding names were checked
directly by Lean. Original manuscript bytes are unchanged.

Validated actual chart-resultant checkpoint (9,489 build jobs;
3,693 audited declarations; 1,408 directly checked coverage/finding names):
[582ea278507fd72b88e47d7dbae9d30ff064f179](https://github.com/Vulkin-prog/paper-p1-lean/commit/582ea278507fd72b88e47d7dbae9d30ff064f179).

## Actual bidegree-one auxiliary curve count

`BidegreeOneCurveCount.actual_real_solutions_count` proves the local
N^epsilon*H bound for actual primitive integer solutions in real boxes.
A canonical primitive scale, actual chart resultants and their explicit
coefficient-height bounds, a constructed homogeneous eliminant and an
injective fixed-scale fibre map supply the complete arithmetic count.
The generic original bidegree includes both (2,1) and (1,2). No height
bound on the original coefficient forms, nonzero shift or box heights
is needed in this case. This strengthens the local scope as P1-MATH-0049.

Full T1.4 remains in progress: its source auxiliary-form extraction and
nondegeneracy/coefficient height from determinant/lattice construction,
other curve cases and short-vector summations are open. Coverage stays
54/167, with 49 confirmed improvements. See
[complete local algebraic count](BIDEGREE_ONE_CURVE_ALIGNMENT.md).

Scope precision for P1-MATH-0049: the proved elementary elimination
estimate is in the remaining pair height. The complementary Heath-Brown
bound in the eliminated pair height remains open, including for the
relevant bidegree-one auxiliary factors. The estimate involving the minimum of
the two heights remains unproved.

The full build passed (9,499 jobs); all 3,720 declarations passed the
actual axiom audit, permitting only propext, Classical.choice and
Quot.sound. All 1,435 distinct coverage/finding names were checked
directly by Lean. Original manuscript bytes are unchanged.

Validated elementary bidegree-one elimination checkpoint (9,499 build
jobs; 3,720 audited declarations; 1,435 directly checked coverage/finding names):
[bc9f8dc072a9efe82022b91f1a5261debfd49529](https://github.com/Vulkin-prog/paper-p1-lean/commit/bc9f8dc072a9efe82022b91f1a5261debfd49529).

## One homogeneous resultant for primitive scales

`ReflectedResultants` proves exact Sylvester row/column reversal and equal
absolute values of the two padded chart resultants. The two coordinate
powers therefore cancel by a primitive gcd, giving q dividing one
homogeneous resultant R. `SingleResultantFibreCount` sharpens the finite
point bound to 2*tau(|R|)*(k+d*ell)*(2H+1). The actual real-box N^epsilon*H
count only needs R!=0; univariate coprimality over Q and one full padded
degree provide it. This improvement is P1-MATH-0050. Coverage stays
54/167, with 50 confirmed improvements. Full T1.4 and the complementary
curve bound remain open. See [alignment](SINGLE_RESULTANT_ALIGNMENT.md).

The full build passed (9,503 jobs); all 3,733 declarations passed the
actual axiom audit, permitting only propext, Classical.choice and
Quot.sound. All 1,448 distinct coverage/finding names were checked
directly by Lean. Original manuscript bytes are unchanged.

Validated single-resultant checkpoint (9,503 build jobs; 3,733 audited
declarations; 1,448 directly checked coverage/finding names):
[a1ed70f2f336473fa51b6e345409308f78b78873](https://github.com/Vulkin-prog/paper-p1-lean/commit/a1ed70f2f336473fa51b6e345409308f78b78873).

## Projective nondegeneracy from the actual auxiliary factor

The elementary bidegree-one count now applies to literal homogeneous
forms. Irreducibility over Q gives absence of common nonunit factors;
homogenizing chart divisors and excluding the common factor at infinity
proves all chart nondegeneracy conditions. Exact degree/coefficient
transport and actual real-box solution equality are proved. This extends
P1-MATH-0050; coverage remains 54/167, with 50 confirmed improvements.
Source determinant/lattice extraction and height control, the complementary
Heath-Brown bound and full T1.4 remain open. See
[alignment](PROJECTIVE_NONDEGENERACY_ALIGNMENT.md).

The full build passed (9,509 jobs), the actual axiom audit passed for
all 3,753 declarations, and Lean checked all 1,468 distinct
coverage/finding names. Only propext, Classical.choice and Quot.sound
occur; original manuscript bytes are unchanged.

Validated projective nondegeneracy checkpoint (9,509 build jobs;
3,753 audited declarations; 1,468 directly checked names):
[f8cc5d409f099f7440d9346f576605130073bc21](https://github.com/Vulkin-prog/paper-p1-lean/commit/f8cc5d409f099f7440d9346f576605130073bc21).

## Both elementary orientations for a (1,1) auxiliary factor

Exact binary expansions construct the transposed original coefficient
array. The variable-group polynomial-ring equivalence preserves the
actual bilinear auxiliary factor and its irreducibility. The actual
primitive real-box solution sets are bijective after exchanging pairs.
Two elementary counts therefore prove N^epsilon*min(A,H), with one
threshold before all forms, original coefficients, nonzero shifts and
real A,H>=1. This closes the irreducible (1,1) local case and extends
P1-MATH-0049; coverage remains 54/167, with 50 confirmed improvements.
The complementary curve bound is still open for other auxiliary
bidegrees, as is the full determinant/lattice argument. See
[alignment](BILINEAR_AUXILIARY_ALIGNMENT.md).

The full build passed (9,515 jobs), the actual axiom audit passed for
all 3,772 declarations, and Lean checked all 1,487 distinct
coverage/finding names. Only propext, Classical.choice and Quot.sound
occur; original manuscript bytes are unchanged.

Validated bilinear minimum-height checkpoint (9,515 build jobs;
3,772 audited declarations; 1,487 directly checked names):
[b6cfffa06c97f77d6cdf3ec017a3c9af3e5902bd](https://github.com/Vulkin-prog/paper-p1-lean/commit/b6cfffa06c97f77d6cdf3ec017a3c9af3e5902bd).

## Both degree-zero auxiliary counts in original coordinates

Primitive rational directions have at most two signed representatives,
and a nonzero degree-k homogeneous form has at most 2*(k+1) primitive
zeros in any finite family, including infinity. The actual quadratic
fibres give a uniform N^epsilon count at polynomial input heights. The
actual linear fibres have exact step B/gcd(A,B); solvability and the
source scale comparisons give the finite 2*(k+1)*(C0*C1*|h|+1) bound
and the uniform N^epsilon count for polylogarithmic shifts. No auxiliary
coefficient-height bound is needed in these local counts. Source
construction/factorization and unimodular transport, the remaining
curve counts and determinant/lattice sums are open. This is proof
progress without a new correction; coverage stays 54/167, with 50
confirmed improvements. See [alignment](ZERO_DEGREE_AUXILIARY_ALIGNMENT.md).

The full build passed (9,527 jobs), the actual axiom audit passed for
all 3,795 declarations, and Lean checked all 1,510 distinct
coverage/finding names. Only propext, Classical.choice and Quot.sound
occur; original manuscript bytes are unchanged.

Validated degree-zero auxiliary checkpoint (9,527 build jobs;
3,795 audited declarations; 1,510 directly checked names):
[dd119c7505ddbf17cd3c21f324e5ae8f4f2625de](https://github.com/Vulkin-prog/paper-p1-lean/commit/dd119c7505ddbf17cd3c21f324e5ae8f4f2625de).

## Companion T12.1 — the actual first retained class

Exact span-rank submodularity and relation-kernel supermodularity give
rho(J)=rho(J intersect e) for a compressed pair. The actual compressed
block addition map is proved injective exactly when rho(I)=rho(e).
The source class is hereditary and has a unique dependent pair, even
with heterogeneous local dimensions. On actual regular windows and
literal good edges, rho(e)<=L/3+1 and the actual ordered boundary
satisfies 0<rho(I)<=4L/3+1<3L/2 for N>=2,L>=7. One critical-band
threshold precedes all lengths, real prime cutoffs and families.
Companion T12.1 is complete; coverage is 55/167, with 51 confirmed
improvements. This is P1-MATH-0051. See
[alignment](RETAINED_CLASS_ALIGNMENT.md).

The full build passed (9,537 jobs), the actual axiom audit passed for
all 3,826 declarations, and Lean checked all 1,541 distinct
coverage/finding names. Only propext, Classical.choice and Quot.sound
occur; original manuscript bytes are unchanged.

Validated full T12.1 checkpoint (9,537 build jobs; 3,826 audited
declarations; 1,541 directly checked names):
[8320668612ecc2b0e8b8945c974325dc8676f6c4](https://github.com/Vulkin-prog/paper-p1-lean/commit/8320668612ecc2b0e8b8945c974325dc8676f6c4).

## Companion T12.2 — a stronger actual large-boundary estimate

The exact least cutoff is constructed and proved minimal. A finite
powerset exponential tilt gives the actual large-subset tail <=N^(-3),
without an infinite factorial series. Actual affine joint probabilities
and exact regular marginals, including incompatible zero-probability
families, give the full source O(N^(-3/2)) mass estimate. Retaining
the precise loss rho<=4L/3+1 strengthens it to
2*2^(4C/3)*N^(-5/3), with the same cutoff and hypotheses. The actual
regular mean is <=2^C, so an admissible upper mean is proved explicitly.
One threshold precedes all lengths, real prime cutoffs and families.
Companion T12.2 is complete; coverage is 56/167, with 52 confirmed
improvements. This is P1-MATH-0052. The separate unnumbered cutoff
asymptotic and eventual K<=L/4 range remain open. See
[alignment](LARGE_BOUNDARY_TAIL_ALIGNMENT.md).

The full build passed (9,545 jobs), the actual axiom audit passed for
all 3,855 declarations, and Lean checked all 1,570 distinct
coverage/finding names. Only propext, Classical.choice and Quot.sound
occur; original manuscript bytes are unchanged.

Validated full T12.2 and improved-tail checkpoint (9,545 build jobs;
3,855 audited declarations; 1,570 directly checked names):
[e2a0e935344ae4c6ae3fc666de9e050d61fecaa5](https://github.com/Vulkin-prog/paper-p1-lean/commit/e2a0e935344ae4c6ae3fc666de9e050d61fecaa5).

## The exact least cutoff has the source asymptotic and range

Admissible rounded moderate trials and minimality bound the actual
least cutoff. Its normalized lower cost supplies the matching limit:
K_N/(log N/loglog N) tends to three. Also K_N/log N tends to zero,
K_N tends to infinity, and K_N<=floor(L/4) holds eventually under one
threshold before all critical lengths. This closes the accompanying
unnumbered claims for every fixed positive upper mean and extends
P1-MATH-0052. Coverage stays 56/167, with 52 confirmed improvements.
See [alignment](BOUNDARY_CUTOFF_ASYMPTOTICS_ALIGNMENT.md).

The full build passed (9,551 jobs), the actual axiom audit passed for
all 3,870 declarations, and Lean checked all 1,585 distinct
coverage/finding names. Only propext, Classical.choice and Quot.sound
occur; original manuscript bytes are unchanged.

Validated exact cutoff-asymptotic checkpoint (9,551 build jobs;
3,870 audited declarations; 1,585 directly checked names):
[e220886c65aecc4b2f1f7ca78165ab6b2b6a60a1](https://github.com/Vulkin-prog/paper-p1-lean/commit/e220886c65aecc4b2f1f7ca78165ab6b2b6a60a1).

## T5.1 first branch and actual quadratic congruences

Canonical kernels and square parts construct an injective positive
quadratic embedding, including the square case. Derived polynomial
heights give uniform fixed-kernel counts even for polynomial shifts.
The actual prescribed kernel budget is <=floor(2Q/e), giving the first
N^epsilon*Q/e count. Gcd-grouped actual congruence roots inject into
linear fibres and satisfy tau(M)*(X*h/M+1), hence the required
subpolynomial residue cost at polynomial modulus/polylogarithmic shift
heights. This is P1-MATH-0053. The second square-part sum and combined
T5.1 exponent remain open. Coverage stays 56/167, with 53 confirmed
improvements. See [alignment](QUADRATIC_KERNEL_FIRST_BRANCH_ALIGNMENT.md).

First-branch verification: the full build passed (9,559 jobs), the actual
axiom audit passed for all 3,891 declarations, and all 1,606 distinct
coverage/finding names were checked directly. All 138 source manifest
entries and 167 result records remain intact; Ubuntu has 17.64 GiB free.

## Actual T5.1 counts and exponent-range clarification

The second square-part branch is closed: actual parts lie between
N/(2 sqrt(Q)) and 3N/sqrt(Q), their moduli e*v^2 have derived height N^5,
and the finite sum gives N^epsilon*(sqrt(Q)/e+N/sqrt(Q)). The first branch
now accepts real Q. The two branches, their min exponent, a stronger
min(1,c2) exponent and the affine count have one common threshold before
h,e,beta and the actual set. No squarefreeness premise on e is needed.

P1-MATH-0054 proves the capped exponent is universally at most the affine
expression. The uncapped exact comparison needs beta-2delta<=2, while
the actual admissible families give the arbitrary-positive-margin
comparison. Because the literal source display omits this qualification,
T5.1 remains in progress for wording alignment; no unqualified comparison
is claimed. Coverage remains 56/167, with 54 confirmed improvements.
See [alignment](QUADRATIC_KERNEL_COMPLETE_COUNTS_ALIGNMENT.md).

Verification: full build passed (9,567 jobs); actual axiom audit passed for
3,912 declarations; all 1,627 distinct ledger/finding names were checked
directly. All 138 manifest entries and 167 result records remain intact.
Ubuntu available space: 17.63 GiB.

## Growing-degree prime-support and enumeration budgets

T5.2 now has proved preparatory budgets. The actual prime product dominates
omega(n)!, giving a finite logarithmic lower bound. For every fixed c>=0,
C>=1 and epsilon>0, one threshold before n,d proves omega(n)<=(c+epsilon)logN
when n<=(CN)^d and d<=c loglogN. Exact squarefree-divisor counts and
actual prime-colouring counts give N^(c log(a)+epsilon); a fixed
E(loglogN)^3 logarithmic-height error is also absorbed uniformly.
The literal split-product resultant/support arguments and their actual
height estimates are still open; T5.2 is not complete. Coverage remains
56/167 and there are still 54 confirmed improvements: formalizing this
source ingredient is not recorded as a new mathematical improvement.
See [alignment](GROWING_DEGREE_PRIME_BUDGET_ALIGNMENT.md).

Budget verification: full build passed (9,573 jobs); actual axiom audit
passed for 3,927 declarations; all 1,642 distinct ledger/finding names
were checked directly. The 138 manifest entries and 167 result records
remain intact; Ubuntu available space is 17.62 GiB.

## Actual split-product/resultant heights and linear-kernel supports

The literal product on finite integer offsets is positive and equals the
signed source product in the actual range, including negative offsets.
The unordered difference resultant is positive and bounded by
(2W)^(d^2). The actual q*D_A has logarithmic height
c loglogN log(3N)+c^2(log(2D)+A0)(loglogN)^3, so the previous prime
and exponential budgets now apply to that actual integer. Private-prime
parity proves each actual linear kernel divides rad(q*D_A).
The quantitative product-of-quadratic-kernels quotient, prescribed
divisor allocation, selected quadratic enumeration and full fixed-kernel
count remain open. T5.2 remains in progress; coverage stays 56/167 and
confirmed improvements stay 54. See
[alignment](SPLIT_OFFSET_KERNEL_BUDGET_ALIGNMENT.md).

Actual-offset verification: full build passed (9,579 jobs), the actual
axiom audit passed for all 3,950 declarations, and all 1,665 distinct
ledger/finding names were checked. The 138 source manifest entries and
167 result records remain intact. Ubuntu available space: 17.60 GiB.

## Full actual fixed-kernel part of T5.2

The literal fixed-kernel split-product family is bounded by
N^(2c log2+epsilon), using the actual q*D_A prime budget and at most
4^omega(q*D_A) two-linear-support codes. Every code has a proved
injective positive quadratic embedding, with actual coefficients
<=3N and all coordinate/nonzero-shift heights derived. Factorizable
cases are included. This conclusion needs no even-degree assumption
and accepts every fixed polylogarithmic width: P1-MATH-0055.
The prescribed-divisor conclusion and its quadratic-kernel allocation
remain open, so T5.2 stays in progress. Coverage stays 56/167 with
55 confirmed improvements. See
[alignment](SPLIT_OFFSET_FIXED_KERNEL_ALIGNMENT.md).

Fixed-kernel verification: full build passed (9,583 jobs); actual axiom
audit passed for all 3,966 declarations; all 1,681 distinct ledger/finding
names were checked directly. All 138 manifest entries and 167 result
records remain intact. Ubuntu available space: 17.60 GiB.

## Exact grouped-kernel square-overlap decomposition

The quantitative resultant relation is closed in stronger form: for every
finite disjoint grouping of nonzero linear factors, the product M of
block kernels equals q*R^2 with R|D_A. The source paired-quadratic
quotient M/q|D_A^2 follows. No even degree or block-size restriction is
needed for this finite identity. The exact kernel multiplication and
ordered-offset overlap induction replace a prime-occurrence valuation
argument. This is P1-MATH-0056. Divisor allocation and selected quadratic
enumeration still remain open; T5.2 stays in progress. Coverage stays
56/167, with 56 confirmed improvements. See
[alignment](GROUPED_KERNEL_RESULTANT_ALIGNMENT.md).

Grouped-resultant verification: full build passed (9,589 jobs); the
actual audit passed for all 3,991 declarations; all 1,706 distinct
ledger/finding names were checked directly. All 138 manifest entries
and 167 result records remain intact; Ubuntu has 17.59 GiB free.

## Actual grouped prescribed-divisor allocation and enumeration cost

The prime-removal divisor is proved equal to e/gcd(e,rad(D_A)), is
positive and squarefree, divides e and is coprime to D_A. Its removed
factor divides D_A and costs at most log(D_A) in the logarithmic budget.
Explicit block prime products divide both their block kernels and this
divisor, multiply exactly to it and are pairwise coprime. This extends
the arbitrary-block finite scope in P1-MATH-0056. The actual divisor
enumeration cost is proved <=N^(c log2+epsilon) from a derived height.
Pairing/selected-quadratic averaging, shifted quadratic counting and
final source enumeration still remain open. T5.2 stays in progress;
coverage stays 56/167 with 56 confirmed improvements. See
[alignment](GROUPED_DIVISOR_ALLOCATION_ALIGNMENT.md).

Allocation verification: full build passed (9,595 jobs); actual axiom
audit passed for all 4,017 declarations; all 1,732 distinct ledger/finding
names were checked directly. All 138 original manifest entries and 167
result records remain intact. Ubuntu available space: 17.57 GiB.

## Actual pair partition and uniform selected-quadratic averaging

Every even finite set now has an actual pair partition, with d=2*card(P).
For the actual allocated divisors, a selected block has logarithmic cost
at most (log(q)-2log(e)+4log(D_A))/(d/2). The actual resultant error
is uniformly negligible after division by logN at d<=c loglogN.
The stronger selection theorem quantifies one common threshold before
every prescribed fixed partition and all varying data; it introduces
no partition-enumeration factor per solution. This extends the explicit
finite scope of P1-MATH-0056. Shifted quadratic counting and final
selected-block/divisor/dyadic enumeration are still open. T5.2 stays
in progress; coverage stays 56/167 with 56 improvements. See
[alignment](SELECTED_QUADRATIC_BUDGET_ALIGNMENT.md).

Selected-quadratic verification: full build passed (9,601 jobs); actual
axiom audit passed for all 4,026 declarations; all 1,741 distinct
ledger/finding names were checked directly. All 138 manifest entries
and 167 result records remain intact; Ubuntu has 17.56 GiB free.

## Uniform actual shifted quadratic-block count

The prescribed quadratic-kernel affine count now holds on the wider
N/2<=x<=3N range. All square-part and modulus heights are derived,
including the fixed factors absorbed in the same uniform threshold.
For two ordered offsets a<b, the exact positive natural values satisfy
x=n+a and x+(b-a)=n+b; an injective shift identifies the actual block
kernel with sf(x(x+h)). This proves the uniform affine bound for every
actual two-element offset block. The capped-exponent proof remains
valid for all real beta without an exact beta<=2 assumption.
This extends P1-MATH-0054. The final T5.2 selected-block/divisor/dyadic
enumeration is still open; coverage stays 56/167 with 56 improvements.
See [alignment](SHIFTED_QUADRATIC_COUNT_ALIGNMENT.md).

Shifted-count verification: full build passed (9,611 jobs); actual axiom
audit passed for all 4,042 declarations; all 1,757 distinct ledger/finding
names were checked directly. All 138 source manifest entries and 167
result records remain intact. Ubuntu available space: 17.55 GiB.

## Complete actual companion T5.2 and a cumulative strengthening

Both advertised actual counts are proved on every fixed comparable
positive interval a*N<=n<=b*N, a>0. The real-bounds theorem additionally
proves positivity and equality with the literal integer split product.
The final selected-block/divisor/dyadic finite cover is closed: its actual
cell counts and every enumeration/height cost are proved. The interval
transfer uses an exact scale-independent power profile, a constructed
finite cover and uniform degree/width transfer. It preserves the stated
coefficient c with only arbitrarily small exponent losses; no dependence
on the varying size exponent beta is hidden in constants.

One common threshold precedes all varying widths, offset sets, degrees,
divisors, kernel-size exponents, kernels and finite solution families.
The prescribed estimate also holds cumulatively below F*N^beta for any
fixed comparison factor F: P1-MATH-0057. Both assertions allow arbitrary
fixed polylogarithmic widths. The independent fixed-kernel assertion also
allows odd degree >=2: P1-MATH-0055. The prescribed assertion retains
even degree and the paired-quadratic proof.

Coverage is 57/167 (main 17/73; companion 40/94), with 57 confirmed
improvements. Earlier open-stage entries above are historical checkpoints
closed by this section. T5.1's printed unqualified comparison remains
unclaimed; its proved actual affine count suffices here. See
[complete alignment](PRESCRIBED_SPLIT_PRODUCT_ALIGNMENT.md).

Verification checkpoint: Lean v4.36.0-rc2 full build passed (9,629 jobs); actual axiom audit passed for all 4,092 theorem/lemma declarations using only propext, Classical.choice and Quot.sound. All 1,807 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 result records remain intact. Ubuntu available space: 17.52 GiB. No unproved count, new literature input, new Paper C port or Palomar registration.

## Actual short-product moment foundations — article 9.1 in progress

The actual infinite-measure even moment is exactly the number of square
product tuples, including repetitions. Canonical occurrence patterns of
the actual squarefree kernels are proved positive, squarefree, pairwise
coprime, even, reconstructive and unique. Earlier-pattern prescribed
divisors divide the actual coordinate kernels, split off the fresh product
and determine the last kernel completely.

The finite exponent calculation now uses a minimum weighted-degree last
index and a constructed actual injective exposure rank. Its exact finite
height error is log(K)/(2logN), without a dependence on d. This is
P1-MATH-0058. Actual fresh coprime factor families inject into prime
colourings; their uniform assignment cost is proved. Full size-profile
and prefix-state enumeration still remain open. Article 9.1 is in progress;
coverage stays 57/167 with 58 confirmed improvements. See
[moment checkpoint](SHORT_MOMENT_ENUMERATION_ALIGNMENT.md).

Verification checkpoint: Lean v4.36.0-rc2 full build passed (9,653 jobs); actual axiom audit passed for all 4,162 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 1,877 distinct ledger/finding declarations were directly checked. All 138 manifest entries and 167 numbered records remain intact. Ubuntu available space: 17.49 GiB. No unproved literature input, new Paper C port, original manuscript change or Palomar registration.

## Complete actual short split-product moments — article 9.1

The full actual square-tuple count is proved. Each fixed dyadic profile
has one fixed exposure order; actual prefix states fix the prescribed
divisor before the centre is counted. New coprime factors are counted by
an injective prime code, and at the final step the kernel is fixed and
there is no fresh factor assignment. The actual finite transition counts
are iterated and all profiles and exponent losses are summed uniformly.
No target moment, tuple count or local enumeration estimate is assumed.

The exact infinite-measure moment identity then gives the source exponent
v/2+c*[v*(v-1)+2]*log2+epsilon. The source signed polynomial is uniformly
positive and identified exactly with the natural product used in Lean.
Measurability and MemLp are proved. The explicit positive choice
c=epsilon*v/(2*[v*(v-1)+2]*log2), chosen before every fixed interval and
width constant, gives both actual lpNorm and eLpNorm bounds N^(1/2+epsilon).
The theorem allows every finite subset of the comparable positive range
and every fixed polylogarithmic width, P1-MATH-0059.

This closes the historical open-profile and prefix-state entries above.
Proposition 9.1 is complete; Corollary 9.2 remains open. Coverage is
58/167 (main 18/73, companion 40/94), with 59 confirmed improvements. See
[complete moment alignment](SHORT_MOMENT_ENUMERATION_ALIGNMENT.md).

Verification checkpoint: Lean v4.36.0-rc2 full build passed (9,683 jobs); actual axiom audit passed for all 4,226 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 1,941 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records remain intact. Ubuntu available space: 17.43 GiB. No unproved arithmetic/tuple count, new literature input, new Paper C port, manuscript-byte change or Palomar registration.

## Complete actual short projections into the old space — article 9.2

The old space is the full span of the actual old value square classes.
Its character image preserves exactly the relevant relation, and its
positive character density has mean one and exact real moments. A proved
finite weighted Holder inequality and the actual 9.1 Lp estimate bound
fixed motifs. The complete set of bounded integer motifs is counted
uniformly, and the actual finite cover counts every projected centre list,
including repetitions and varying nonempty even selections.

The source block theorem includes critical B=L+1, all comparable positive
centre ranges, a common threshold before varying blocks and motifs, and
uniform positivity/literal signed-product identity. The stronger core only
needs O(logN) arbitrary old generators, with no geometric or height bound;
it also permits arbitrary fixed polylogarithmic new widths. This is
P1-MATH-0060. The c choice precedes the fixed interval/width constants.

Corollary 9.2 is complete. Coverage is 59/167 (main 19/73, companion 40/94),
with 60 confirmed improvements. Earlier statements that 9.2 was open are
historical checkpoints closed here. The conditional full-support theorem
10.1 remains open. See [complete alignment](SHORT_OLD_SPACE_PROJECTION_ALIGNMENT.md).

Verification checkpoint: Lean v4.36.0-rc2 full build passed (9,707 jobs); actual axiom audit passed for all 4,270 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 1,985 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records remain intact. Ubuntu available space: 17.39 GiB. No unproved projection/list count, new literature input, new Paper C port, manuscript-byte change or Palomar registration.

## Complete actual two-small-kernel count — companion T6.1

The actual two-small-kernel centre set is now counted, including all small
prime supports, actual positive kernel pairs, Pell fibres, offset pairs
and comparable-interval cells. Polynomial coefficient heights follow from
actual values; no arithmetic count is supplied as an unproved premise.
The literal source critical-block version and source positivity are proved.

The stronger estimate Q*N^epsilon has a threshold independent of the real
cap Q>=0. The q formulation is therefore uniform in all real q, even when
q varies. The cutoff need only satisfy H<=D*logN, independently of any
fixed polylogarithmic offset width; H>diameter is unused. This is
P1-MATH-0061. Coverage is 60/167 (main 19/73, companion 41/94), with 61
confirmed improvements. See [complete alignment](TWO_SMALL_KERNEL_ALIGNMENT.md).
The smooth-modulus/certificate steps and conditional half-count stay open.

Verification checkpoint: Lean v4.36.0-rc2 full build passed (9,713 jobs); actual axiom audit passed for all 4,282 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 1,997 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records remain intact. Ubuntu available space: 17.38 GiB. No unproved centre/fibre count, new literature input, new Paper C port, manuscript-byte change or Palomar registration.

## Complete deterministic smooth-modulus exception — companion T6.2

The actual exceptional set, its full Rankin/divisor/offset/congruence count
and the selection-to-membership implication are now proved. The literal
real cutoff Y=(logN)^A, critical B=L+1, arbitrary fixed comparable positive
intervals and source value positivity are included. No target count or
modulus-existence premise is left unproved.

Only t+26 selected values are needed, with a threshold before t,H and the
selection. Full canonical square parts and squarefree small odd-prime
parts suffice, and the actual first-passage modulus is squarefree. The
deterministic set is common to all H,t and selections; H>diameter and
H<=Y are not required. This is P1-MATH-0062. Coverage is 61/167 (main 19/73,
companion 42/94), with 62 confirmed improvements. See
[complete alignment](LARGE_SMOOTH_MODULUS_ALIGNMENT.md). The incoming/outgoing
certificate lemma and full conditional half-count remain open.

Verification checkpoint: Lean v4.36.0-rc2 full build passed (9,731 jobs); actual axiom audit passed for all 4,318 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 2,033 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records remain intact. Ubuntu available space: 17.35 GiB. No unproved modulus/centre count, new literature input, new Paper C port, manuscript-byte change or Palomar registration.

## Complete actual received certificate graph — companion T6.3

Actual projected relations in the full old span now force a short
source--receiver certificate. Actual old vectors are represented by
unrestricted old selections, including overlaps and dependence. Private
anchor-prime reception, coprime products and allocation, a large receiver
modulus and minimal first passage are all proved. Both actual directed
degree counts are proved from finite prime/offset codes, with one common
bound B^t*(e*t*B)^k and k=floor(log(Z)/logY)+1.

The literal critical-block theorem inflates the admissible radius by B0=L+1,
so the constructed certificate exceeds 2*K*N*B0. Every fixed comparable
positive range and source-value positivity are included. The complete
statement works for A>1; degree counts alone work for A>0. This is
P1-MATH-0063. Coverage is 62/167 (main 19/73, companion 43/94), with 63
confirmed improvements. See [complete alignment](ANCHOR_CERTIFICATE_ALIGNMENT.md).
The main conditional half-count still needs its simultaneous induction
and stage iteration; it is not counted as complete here.

Verification checkpoint: Lean v4.36.0-rc2 full build passed (9,757 jobs); actual axiom audit passed for all 4,362 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 2,077 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records remain intact. Ubuntu available space: 17.31 GiB. No unproved receiver/degree count, new literature input, new Paper C port, manuscript-byte change or Palomar registration.

## Conditional half-count foundations — main 10.1 remains in progress

An actual injective-list witness model now keeps even selections, nonzero
vectors in each own absolute space and total projection into the full old
span explicit. Actual tuple erasure preserves these data after one or two
centres are fixed and their full blocks are adjoined to the old sources.
The corresponding actual fibres inject into fewer-target list sets. The
all-short fixed-cap case is completely counted using 9.2, with the actual
product/parity and old-generator cardinality bridges proved.

The simultaneous induction, stage invariant and full stage enumeration,
and final geometric/effective-space alignment, remain open. Main 10.1 is
not included in completed coverage. Coverage stays 62/167, with 63 confirmed
improvements. See [preparatory alignment](CONDITIONAL_HALF_COUNT_ALIGNMENT.md).

Preparatory verification checkpoint: Lean v4.36.0-rc2 full build passed (9,785 jobs); actual axiom audit passed for all 4,428 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 2,143 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records remain intact. Ubuntu available space: 17.27 GiB. Numbered coverage remains 62/167 and confirmed findings remain 63; main 10.1 is still in progress.

## Actual conditional half-count stage classes

The actual decreasing survivor sets, chosen-witness receiver extraction,
zero-cutoff initial exception and deterministic confinement of every
surviving long source are now proved. Actual directed source-receiver pairs
and new/old receiver list classes are counted by the exact tuple-deletion
fibres. The finite schedule reaches one half exactly and its increment
can be chosen arbitrarily small. Exact finite telescoping and the resulting
finite loss inequalities are verified. The simultaneous asymptotic induction
has not yet instantiated their explicit fewer-target cardinal arguments.
The complete main 10.1 count and its final geometric alignment remain open;
numbered coverage stays 62/167 and confirmed improvements stay 63. See
[current half-count alignment](CONDITIONAL_HALF_COUNT_ALIGNMENT.md).

## Full conditional half-count — main Theorem 10.1 complete

The simultaneous strong induction now instantiates every actual fewer-
target list count for all fixed old-source counts. All initial, removed
and final classes are counted with the actual finite stage schedule and
common thresholds before every position and block geometry. The proof
uses the fixed cap t+25 and H=0, recorded as P1-MATH-0064.

Actual effective even-selection images lift to the exact offset witnesses,
retaining nonzero vectors in each own space. Arbitrary finite candidate
sets and actual value heights are included; active centre heights follow
from the values, and empty old blocks can be recentered harmlessly.
Full old spans, overlap, dependence and literal critical B=L+1 are covered.
Main 10.1 is complete. Coverage is 63/167 (main 20/73, companion 43/94),
with 64 confirmed improvements. See
[complete alignment](CONDITIONAL_HALF_COUNT_ALIGNMENT.md).

Full main 10.1 verification: Lean v4.36.0-rc2 full build passed (9,797 jobs); actual axiom audit passed for all 4,453 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 2,168 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records remain intact. Ubuntu available space: 17.24 GiB. No unproved local or target count, new literature input, new Paper C port, manuscript-byte change or Palomar registration.

## Dependent block pairs — main Corollary 10.3 complete

The actual ordered pair set is identified with nonzero intersections of
actual effective even-selection spaces. Distinct-centre pairs inject into
the complete r=2, s=0 half-count. Equal-centre pairs inject into actual
active centres; actual value heights and radii prove the required linear
centre count. Both classes are counted and their factor two is absorbed.
All fixed logarithmic widths, heterogeneous bounded block shapes and
arbitrary finite candidate sets are included. Main 10.1 now also has an
explicit logarithmic-width version without a critical-length input.
Coverage is 64/167 (main 21/73, companion 43/94), with 64 confirmed
improvements. See [complete alignment](DEPENDENT_BLOCK_PAIRS_ALIGNMENT.md).

Dependent-pair verification checkpoint: Lean v4.36.0-rc2 full build passed (9,805 jobs); actual axiom audit passed for all 4,465 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 2,180 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records remain intact. Ubuntu available space: 17.23 GiB. Coverage is 64/167 and confirmed findings remain 64; no new external input, Paper C port, manuscript-byte change or Palomar registration.

## Relative participation and generic connected tuples

P1-MATH-0065 strengthens the relative half-count to allow a separate
participating relation at each new coordinate. Actual support extraction,
enlarged-old-span preservation, exact fibres and all finite split classes
are counted by simultaneous strong induction with fewer targets and all
old-source counts. The actual canonical direct partition supplies these
relations for every coordinate of a connected family of at least two
blocks. Thus actual generic connected block tuples have the full half-count.

Actual successive-exposure populations and their full counts are also
proved. Main 10.2 remains in progress for original-window/set-family,
primitive and independent-mass alignment. Coverage stays 64/167 (main
21/73, companion 43/94), with 65 confirmed improvements. See
[relative participation](RELATIVE_PARTICIPATION_ALIGNMENT.md) and
[connected-family scope](CONNECTED_FAMILY_ALIGNMENT.md).

Verification checkpoint: Lean v4.36.0-rc2 full build passed (9,821 jobs); actual axiom audit passed for all 4,501 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 2,216 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records remain intact. Ubuntu available space: 17.20 GiB. No unproved group, extension or target count, new external input, Paper C port, manuscript-byte change or Palomar registration. Coverage remains 64/167; confirmed improvements are 65; main 10.2 is still in progress.

## Connected and primitive original-window families — main 10.2 complete

Actual unordered r-element connected and primitive original-window families
are now counted. Their canonical/direct and primitive/nullity definitions
are literal source objects. Actual even-selection image identities, original
value heights/distances and injective family enumerations are verified.
Minimal positive nullity supplies an actual full-support primitive relation.

The independent masses use products of the exact heterogeneous infinite-
model marginals. Their proved common critical-band K/N cap, including zero
marginals, combines with the actual host counts and fixed-factor absorption
to give N^(-r/2+epsilon). No homogeneous or compatibility premise is added.
Full main Corollary 10.2 is complete. Coverage is 65/167 (main 22/73,
companion 43/94), with 65 confirmed improvements. See
[complete alignment](CONNECTED_FAMILY_ALIGNMENT.md).

Full original-window family verification: Lean v4.36.0-rc2 full build passed (9,835 jobs); actual axiom audit passed for all 4,515 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 2,230 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records remain intact. Ubuntu available space: 17.18 GiB. Full main 10.2 is complete; coverage is 65/167 (main 22/73, companion 43/94), with 65 confirmed improvements. No unproved host or independent-mass count, new external input, Paper C port, manuscript-byte change or Palomar registration.

## Full several-block relation count — companion T1.14 complete

The complete half-count yields the stronger exponent r-s/2 for a full
relation with at least s nonzero actual even-image block projections.
Actual support splits, complementary fibres and all role codes are proved
and counted. Original-window effective spaces and literal geometry are
identified. Arbitrary finite fixed-width block images, actual fixed
offset/dilation codes and their full coded records are also counted.
The source weaker exponent follows by a proved comparison.

This independent proof bypasses the unfinished two-small-kernel determinant
input for T1.14; it does not complete T1.5 or T1.13. P1-MATH-0066 records
the stronger bound and actual image scope. Coverage is 66/167 (main 22/73,
companion 44/94), with 66 confirmed improvements. The separate pair activity
partition and triple deficit remain open. See
[complete support alignment](SEVERAL_BLOCK_RELATION_ALIGNMENT.md).

Full several-block support verification: Lean v4.36.0-rc2 full build passed (9,845 jobs); actual axiom audit passed for all 4,536 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 2,251 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records remain intact. Ubuntu available space: 17.16 GiB. Full T1.14 is complete with the stronger support bound and actual fixed-parameter record counts; coverage is 66/167 (main 22/73, companion 44/94), with 66 confirmed improvements. No unfinished determinant or kernel count, target-count hypothesis, new external input, Paper C port, manuscript-byte change or Palomar registration.

## Order-dependent branching — exact finite and uniform rate, initial moment retained

The actual rounded cardinality budget now has the logarithmic Euler gain
sqrt(m/log(m+2)), proved by elementary prime-sum splitting. The full
infinite-model independence conclusion and deterministic two-supported-value
exception give (B/2)*sqrt(3N)*exp(C0*sqrt(m/log(m+2))) with no separate contact
term. The literal larger source exception has its uniform logarithmic rate
for all 1<=j<=log(N), under one threshold before every critical length.

The actual factorial recurrence also gives the displayed growing-order
exponential factor multiplied by the actual F_2. A uniform O_C(1) bound
for that initial pair moment remains open, so T19.4 is in progress. This
extends P1-MATH-0030; coverage stays 66/167 and confirmed findings stay 66.
No extrapolation of fixed-order constants or target estimate is assumed.
See [exact scope](ORDER_DEPENDENT_BRANCHING_ALIGNMENT.md).

Order-dependent branching verification: Lean v4.36.0-rc2 full build passed (9,855 jobs); actual axiom audit passed for all 4,570 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 2,285 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records remain intact. Ubuntu available space: 17.13 GiB. T19.4 remains in progress only for its bounded initial pair moment; coverage is 66/167 and confirmed improvements remain 66. No new external input, Paper C port, manuscript-byte change or Palomar registration.

## Sharp rational overlap — complete main 14.2 and unique extremality

The exact ordered gcd density is at most 19/30 for every integer triple
u<v<w<2u with gcd(u,v,w)=1. Positivity follows from the literal integer
range. All pair positions, reduced-height cases and remaining finite
numerators and denominators have checked proofs. No arithmetic rank
estimate or unproved counting input is assumed.

Equality holds only at (10,12,15). Every other primitive ordered triple
has density at most 11/18, attained at (8,9,12), yielding the sharp gap
1/45. This is P1-MATH-0067. Main 14.2 is complete; coverage is 67/167
(main 23/73, companion 44/94) and confirmed improvements are 67. The
additional arithmetic relations and third-cumulant exponent remain open.
See [complete overlap alignment](RATIONAL_TRIPLE_OVERLAP_ALIGNMENT.md).

Rational-overlap verification: Lean v4.36.0-rc2 full build passed (9863 jobs); actual axiom audit passed for all 4603 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 2318 distinct ledger/finding names were checked directly by Lean. All 138 source manifest entries and 167 numbered records are intact. Ubuntu available space: 16.78 GiB. Full main 14.2, the integer equality classification and the attained next-value bound are proved; no arithmetic rank or counting hypothesis, external input, Paper C port or Palomar registration. Coverage is 67/167 (main 23/73, companion 44/94) and confirmed improvements are 67.

## Quadratic-component construction — actual population, rank and order inputs

For T19.9 the actual late prime-cylinder population is now constructed
and counted. A concrete common sample proves every subfamily compatible;
its actual position excludes every leading good pair. The actual three-band
prime cover, its literal 17/12 PNT budget and the actual finite-character
rank bound are proved. The regular population has size asymptotic to
N/(2q) and its rank-density envelope tends to 17/(6log2).

The literal integer peeling order tends to infinity, stays below L, and
its actual positive-mass loss is at most 2/sqrt(L). The selected canonical
component and its original-model moment/nullity/connectedness transport
remain to be instantiated. T19.9 is in progress; coverage stays 67/167
and confirmed findings stay 67. See
[actual quadratic-component inputs](QUADRATIC_COMPONENT_ALIGNMENT.md).

Quadratic-component input verification: Lean v4.36.0-rc2 full build passed (9,883 jobs); actual axiom audit passed for all 4,671 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 2,386 distinct ledger/finding names were directly checked. All 138 original manifest entries and 167 numbered records are intact. Ubuntu available space: 16.75 GiB. T19.9 remains in progress for the selected-component conclusion; coverage stays 67/167 and confirmed findings stay 67. No new external input, Paper C port, manuscript-byte change or Palomar registration.


## Complete quadratic-nullity component under the original infinite law

Full companion T19.9 is now proved. The actual peeling denominator is
positive and has a dynamic density envelope tending to 17/(6 log 2).
The private-rank theorem constructs an actual canonical part; minimality
of the canonical partition proves connectedness. Explicit coefficient
and index equivalences preserve this property, nullity and products.
The common solving sample and exact cylinder transport identify both
original infinite-model moments of the actual finite set of starts.

One selected family precedes every epsilon tolerance. Both source
lower-bound coefficients tend to kappa=6 log(2)/17, giving the linear
size and quadratic-nullity bounds for that same family. Its centered
mass is at least (1-2/sqrt(L)) times its positive joint mass. The family
is regular, nonempty, compatible and connected, full and compatible
nullities coincide, and no good pair is present for any threshold.
Coverage is 68/167 (main 23/73, companion 45/94), with 67 confirmed
improvements. See [complete alignment](QUADRATIC_COMPONENT_ALIGNMENT.md).

Quadratic-component completion verification: Lean v4.36.0-rc2 full build passed (9905 jobs); actual axiom audit passed for all 4713 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 2428 distinct ledger/finding declarations were checked directly by Lean. All 138 original manifest entries and 167 numbered records are intact. Ubuntu available space: 16.72 GiB. Full T19.9 is complete, with a fixed family before every epsilon and the actual infinite-model moments. Coverage is 68/167 (main 23/73, companion 45/94); confirmed improvements remain 67. No target component assumption, external input, Paper C port, manuscript-byte change or Palomar registration.


## Stronger actual full-loss pair support and second-moment progress

The first display of main 3.2 now holds with N^(1+epsilon), in place
of N^(6/5+epsilon), even before separation. Full rho includes every
local kernel. An actual cover splits regular effective intersections
from either locally deficient coordinate. Complete main 10.3 and the
regular-set count supply all three bounds, without an unfinished pair
estimate as input. Exact heterogeneous independent mass over the full
host set is at most N^(-1+epsilon). This is P1-MATH-0068.

An exact ordered-distinct-tuple split proves
F_2<=N^2 p^2+card(hosts)*M for an actual marginal cap M. It yields
F_2<=N^epsilon uniformly in every fixed critical band, for each fixed
positive epsilon. This does not imply the bounded seed in T19.4 or the
separate weighted nonaligned residual in main 3.2; both remain in
progress. Coverage stays 68/167; confirmed improvements are 68. See
[exact alignment](PAIR_HOST_COUNT_ALIGNMENT.md).

Pair-host verification: Lean v4.36.0-rc2 full build passed (9915 jobs); actual axiom audit passed for all 4729 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 2444 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records are intact. Ubuntu available space: 16.69 GiB. The stronger full-loss host count and exact heterogeneous independent mass are proved; main 3.2 remains in progress for its weighted nonaligned residual. The actual F_2<=N^epsilon bound does not close T19.4. Coverage stays 68/167; confirmed improvements are 68. No target host count, external assumption, Paper C port, manuscript-byte change or Palomar registration.


## Complete disjoint square-equation input with two arbitrary coefficients

Full T4.1 is proved in a stronger form: j=2 is independent of the degree
cap and error margin, and arbitrary nonzero integer coefficients need
no height bound. A square equation fixes the actual squarefree kernel.
The complete fixed-kernel count has a uniform N^epsilon fixed-degree
specialization; multiplying two disjoint nonconstant equations supplies
at least two distinct roots. The full actual integer population in any
fixed comparable positive interval is counted. The critical-band radius
ceiling, every offset list and the quantifier order are included.

This acyclic arithmetic proof uses the internally proved uniform Pell
and fixed-kernel estimates, removing the source Pila input at this
one-variable step. It is P1-MATH-0069 and also proves the one-variable
part of T1.7. The two-variable surface and graph estimates, main 6.2
dense-target classification and main 6.3 propagation remain separate
open obligations. Coverage is 69/167 (main 23/73, companion 46/94), with
69 confirmed improvements. See
[complete alignment](DISJOINT_SQUARE_EQUATIONS_ALIGNMENT.md).

Disjoint-square verification: Lean v4.36.0-rc2 full build passed (9923 jobs); actual axiom audit passed for all 4740 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 2455 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records are intact. Ubuntu available space: 16.68 GiB. Full T4.1 is complete with j=2, arbitrary nonzero integer coefficients and actual integer solution sets. The one-variable part of T1.7 is complete; its two-variable and graph conclusions remain open. Coverage is 69/167 (main 23/73, companion 46/94); confirmed improvements are 69. No Pila or target-count hypothesis, new external assumption, Paper C port, manuscript-byte change or Palomar registration.


## Actual dense-target projection and regularized support pools

Main 6.2 is in progress. The effective nullity increment equals the
new-block relation-projection rank. A complete physical code surjects
onto the actual effective relations, so its physical target projection
has at least that rank, including overlapping and dependent sources.
Restriction loses at most its codimension in any projection. Distinct
nonzero target labels bound the restricted projection rank.

One integer recovery order, fixed before all lengths and starts, loses
at most eta*L/4. The actual target retains at least delta_z-eta*L/4
labels. Minimal binary representations, injective physical lifts,
finite support pools and their fixed multiplicity-based count are
constructed. The prime-group classification, coefficient enumeration
and resulting actual target count remain open. Completed T4.1 and T4.2
supply the later square-equation and product-certificate inputs. Coverage
stays 69/167 and confirmed improvements stay 69. See
[exact scope](DENSE_TARGET_ALIGNMENT.md).

Dense-target input verification: Lean v4.36.0-rc2 full build passed (9943 jobs); actual axiom audit passed for all 4775 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 2490 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records are intact. Ubuntu available space: 16.66 GiB. Actual physical/effective relation projections, their fixed-order recovery regularization and finite support pools are proved. Main 6.2 remains in progress for the prime-group classification and actual target count. Coverage and confirmed improvements stay 69/167 and 69. No target-count premise, external assumption, Paper C port, manuscript-byte change or Palomar registration.


## Actual prime groups and the residual-kernel bound for main 6.2

All actual large-prime row equations are proved on the physical code and
its regularization. A prime above the window width meets at most one
vertex per window. An active target occurrence has a bounded actual
source support from its literal finite pool. Assigning each such prime
to one chosen physical support constructs squarefree pairwise coprime
groups dividing actual source and target values.

A maximal-product argument gives an actual strict product certificate
or small remaining groups. At most k target label classes are discarded,
with no second restriction of the relation space. Each nonzero class
meets at most (t-1)*Dstar groups. Its actual residual odd-prime product
is bounded by N^((t-1)*Dstar/k). The canonical three-part kernel
factorization gives small-prime and source divisors and a square
equation. Two-class selection and the final position/coefficient
enumeration remain open; main 6.2 stays in progress. No new coverage or
independent mathematical finding is counted.

Prime-group checkpoint verification: Lean v4.36.0-rc2 full build passed (9961 jobs); actual axiom audit passed for all 4833 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 2548 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records remain intact. Ubuntu available space: 16.63 GiB. Actual circuit groups, the strict-certificate dichotomy and the residual-kernel exponent are proved. Main 6.2 remains in progress for the final two-class selection and population count. Coverage and confirmed improvements remain 69/167 and 69. No output-count premise, external assumption, new Paper C port, manuscript-byte change or Palomar registration.


## Complete actual dense-target count — main 6.2

`DenseTargetCount.main_6_2` proves the literal source-excluding count
N^epsilon uniformly over all fixed source tuples and every critical-band
length after one threshold. The stronger `uniform_count` also permits
repeated sources and includes the source centres among target candidates.
There is no independence, separation, local regularity or compatibility
hypothesis. Every arithmetic classification and coefficient enumeration
is proved on the actual physical relation code. Two disjoint nonempty
target classes suffice by the completed T4.1; T4.2 counts the certificate
branch. No Pila theorem or output-count hypothesis is required.

Coverage is 70/167 (main 24/73, companion 46/94). Confirmed independent
findings remain 69. The complete proof records its finite support bound
Dstar, including one-source representations, and the stronger repeated-
source scope. Main 6.3 propagation and main 6.4 moments remain open.
See [full statement alignment](DENSE_TARGET_ALIGNMENT.md).

Complete dense-target verification: Lean v4.36.0-rc2 full build passed (9985 jobs); actual axiom audit passed for all 4880 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 2595 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records are intact. Ubuntu available space: 16.59 GiB. Main 6.2 is complete for its literal source-excluding effective-rank-loss population, with a stronger repeated-source and source-inclusive count. Coverage is 70/167 (main 24/73, companion 46/94); confirmed independent findings stay 69. Main 6.3 and 6.4 remain open. No target-count premise, external assumption, new Paper C port, manuscript-byte change or Palomar registration.


## Main 6.3 — Complete actual conditional-sum assertion

The first conditional-sum assertion of main 6.3 is proved on the actual
infinite prime-sign measure, including the literal source-excluding
sum and homogeneous prescriptions. It is uniform before every source
tuple, length and compatible affine prescription; a stronger theorem
permits repeated sources and arbitrary centre-dependent target
prescriptions. Every source prescription of positive mass is represented
by an actual finite-cylinder witness. The conditional law is identified
with the finite affine observation law and its exact effective nullity
increment. Actual local rank loss is retained; incompatible target
atoms have zero mass. The low/high split invokes the completed main
6.2 count with explicit exponent margins.

The full numbered result remains in progress for extension-family
propagation and the local-defect/contact seed conclusion. Coverage
stays 70/167 and confirmed independent findings stay 69. See
[precise scope](FIXED_SOURCE_PROPAGATION_ALIGNMENT.md).

Conditional-sum checkpoint verification: Lean v4.36.0-rc2 full build passed (9999 jobs); actual axiom audit passed for all 4908 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 2623 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records are intact. Ubuntu available space: 16.57 GiB. The first conditional-sum assertion of main 6.3 is complete on the actual infinite prime-sign measure, including arbitrary compatible affine prescriptions, homogeneous prescriptions and literal source exclusion. Extension-family propagation and the final seed consequence remain open, so main 6.3 stays in progress. Coverage and confirmed independent findings remain 70/167 and 69. No conditional-sum premise, external assumption, new Paper C port, manuscript-byte change or Palomar registration.


## Actual fixed-order mass propagation in main 6.3

The second main 6.3 assertion is now proved on literal finite ordered
extension families. Their actual infinite-measure joint masses factor
through the proved conditional probabilities, including zero-mass
seeds. One threshold controls every intermediate source order in a
fixed range, before every seed family and prescription. Finite iteration
gives the mass bound N^epsilon times the actual seed mass. The explicit
distinct-extension filter has the source initial-tuple and coordinate
conditions, and the original run joint moments are identified exactly.
The stronger full extension family permits repeated centres.

The numbered result stays in progress for the final local-defect and
compatible-contact seed mass conclusion at arbitrary tuple positions.
Coverage and confirmed independent findings remain 70/167 and 69.
See [exact current scope](FIXED_SOURCE_PROPAGATION_ALIGNMENT.md).

Fixed-order propagation verification: Lean v4.36.0-rc2 full build passed (10011 jobs); actual axiom audit passed for all 4929 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 2644 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records are intact. Ubuntu available space: 16.55 GiB. The conditional-sum and actual ordered-distinct extension-family propagation assertions of main 6.3 are complete, including an exact bridge to original infinite joint moments. The final local-defect/contact seed conclusion remains open; main 6.3 stays in progress. Coverage and confirmed independent findings remain 70/167 and 69. No propagation-mass premise, external assumption, new Paper C port, manuscript-byte change or Palomar registration.


## Complete main 6.3, including every exceptional seed position

All three main 6.3 assertions are proved. Local-defect seeds have the
actual affine mass O(N^(-1+epsilon)). At exact contact the two window
spaces span the full union interval; its relation rank is at most its
actual defect count. The uniform local count gives a subpower binary
relation factor and actual contact-seed mass O(N^(-1+epsilon)). Strict
contacts have zero joint mass for original run starts. This exclusion
is not applied to arbitrary homogeneous overlapping prescriptions.

A literal finite permutation cover places one-coordinate and two-
coordinate seeds at all positions of ordered distinct tuples, at cost
at most r!. Actual population membership and injected seeds are proved.
The completed propagation estimate supplies the final positive mass
bound. `FixedSourcePropagationTheorem.main_6_3` bundles conditional
sums, actual propagation and original-model exceptional mass after
one common threshold. Coverage is 71/167 (main 25/73, companion 46/94);
confirmed independent findings remain 69. Main 6.4 remains open.
See [complete alignment](FIXED_SOURCE_PROPAGATION_ALIGNMENT.md).

Complete main 6.3 verification: Lean v4.36.0-rc2 full build passed (10043 jobs); actual axiom audit passed for all 4978 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 2693 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records are intact. Ubuntu available space: 16.50 GiB. The full conditional-sum, actual ordered-distinct propagation and all-position local-defect/contact mass conclusions are proved, with original infinite joint moments and one common threshold. Coverage is 71/167 (main 25/73, companion 46/94); confirmed independent findings stay 69. No conditional-sum, propagation, contact-rank or seed-mass premise, external assumption, new Paper C port, manuscript-byte change or Palomar registration.


## Colored replica conditional propagation checkpoint

The actual finite colored prime-sign model, its exact replica-product
identity and its compatible/incompatible nominal-row mass formula are
proved. The complete uniform colored conditional target sum follows
from a stronger pointwise domination by the merged homogeneous atom.
Its threshold is independent of the coloring and small-prime threshold;
source and target repetitions are retained. The exact conditional ratio
is defined from actual source and intersection probabilities.

T22.7 stays in progress for the conditional-expectation interpretation,
effective relative-kernel alignment and full positive weighted moment
bound. Coverage remains 71/167 (main 25/73, companion 46/94). Confirmed
independent findings are now 70, including P1-MATH-0070. See
[colored replica alignment](COLORED_REPLICAS_ALIGNMENT.md).

Colored replica checkpoint verification: Lean v4.36.0-rc2 full build passed (10061 jobs); actual axiom audit passed for all 5007 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 2722 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records are intact. Ubuntu available space: 16.48 GiB. Actual finite replica products, the nominal-row compatibility/kernel formula and the full finite colored conditional target sum are proved. The stronger pointwise homogeneous comparison is P1-MATH-0070. T22.7 stays in progress for conditional-expectation interpretation, effective relative-kernel alignment and the positive weighted moment bound. Coverage remains 71/167 (main 25/73, companion 46/94); confirmed independent findings are 70. No conditional-sum, independence or merging premise, external assumption, new Paper C port, manuscript-byte change or Palomar registration.


## Infinite replica formula and weighted colored propagation

The exact replica formula is now proved for actual infinite-measure
conditional expectations given the small-prime sigma algebra. The
cutoff independence of that sigma algebra is proved. Exact heterogeneous
uncolored marginals and the effective relative kernel are retained;
the printed p^r version follows from regularity. Actual fixed-order
colored tuple masses propagate with any nonnegative seed weight retained
exactly, including all extension subfamilies and repeated centers.

T22.7 remains in progress for its final positive random-sum moment
expansion and logarithmic-weight absorption. Coverage stays 71/167
and confirmed findings stay 70; no additional independent finding is
counted for this proof progression. See [alignment](COLORED_REPLICAS_ALIGNMENT.md).

Infinite replica and weighted propagation verification: Lean v4.36.0-rc2 full build passed (10087 jobs); actual axiom audit passed for all 5052 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 2767 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records are intact. Ubuntu available space: 16.45 GiB. The replica formula uses actual infinite-measure conditional expectations and the exact small-prime sigma algebra; exact heterogeneous uncolored marginals and the effective relative kernel are proved, with the regular p^r specialization. Actual colored extension propagation retains arbitrary nonnegative seed weights and all extension subfamilies. The positive random-sum moment assembly remains open; T22.7 stays in progress. Coverage remains 71/167 (main 25/73, companion 46/94); confirmed findings remain 70. No conditional-expectation, uniform-law, weighted propagation or seed-mass premise remains uninstantiated; no new external assumption, Paper C port, manuscript-byte change or Palomar registration.


## Complete companion T22.7: actual replicas, conditional sums and positive moments

The actual infinite colored product space and its exact uniform finite
cylinder law are constructed. Its literal compatible-source conditional
probabilities satisfy the full uniform target sum. The original infinite
conditional replica formula retains affine compatibility and the actual
effective relative kernel; exact heterogeneous marginals are retained,
and the printed p^r formula is proved on the actual regular set.

Every fixed positive integer moment of an actual positive replica sum
is bounded by N^epsilon times its exact first moment. The proof expands
replica products, injectively flattens ordered occurrences to actual
extensions of their first tuple, retains its arbitrary nonnegative seed
weight, and absorbs only the remaining fixed logarithmic weight powers.
Repeated centers, all ordered tuple subfamilies, zero weights, empty
families and zero-length tuples are included. The final theorem uses the
original infinite run-start conditional probabilities. Its threshold is
uniform in Y, the color type and coloring, the tuple family and weights.

Coverage is now 72/167 (main 25/73, companion 47/94). Confirmed findings
stay 70; P1-MATH-0070 also has the exact infinite colored comparison.
Main 6.4 and the full pair profile remain open. See
[complete replica alignment](COLORED_REPLICAS_ALIGNMENT.md).

Complete T22.7 verification: Lean v4.36.0-rc2 full build passed (10123 jobs); actual axiom audit passed for all 5105 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 2820 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records are intact. Ubuntu available space: 16.39 GiB. Full companion T22.7 is complete: actual infinite conditional replica formula, printed p^r specialization on the actual regular set, literal infinite colored conditional target sum and actual original-run positive weighted moment estimate. Every fixed positive integer order, all tuple lengths including zero, repeated centers, arbitrary ordered dyadic tuple subfamilies, empty families and nonnegative logarithmically bounded weights are included, with threshold before Y and all varying families/colorings/weights. The actual infinite colored product space and its exact cylinder law are constructed. Coverage is 72/167 (main 25/73, companion 47/94); confirmed findings remain 70. No conditional-sum, moment, first-moment, independence, uniform-law or propagation estimate is assumed; no new external input, Paper C port, manuscript-byte change or Palomar registration.


## Triple positivity and incompatible cancellation checkpoint

Every compatible finite binary affine family now has a proved
nonnegative centered coefficient, equal to its exact heterogeneous
independent weight times the full-support effective relation count.
The result is identified with actual original infinite run coefficients
at every finite order, including irregular windows and repeated formal
centers. This strengthens the sign assertion of main 11.3 and is recorded
as P1-MATH-0071. Confirmed independent findings are now 71.

The exact incompatible triple cancellation, both-sign absolute bound,
canonical connectedness of nonzero triple activities and the finite
absolute/signed activity comparisons are proved. The actual independent
weight of the nonzero incompatible triple population has the full
N^(-3/2+epsilon) bound. The remaining pair/target activity deficit and
third factorial-cumulant assembly stay open, so main 11.2 and 11.3 remain
in progress. Coverage stays 72/167. See
[triple activity alignment](TRIPLE_ACTIVITIES_ALIGNMENT.md).

Triple activity checkpoint verification: Lean v4.36.0-rc2 full build passed (10143 jobs); actual axiom audit passed for all 5143 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 2858 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records are intact. Ubuntu available space: 16.36 GiB. Compatible centered coefficients are proved nonnegative at every finite order with exact heterogeneous marginals and an explicit full-support physical effective relation count, including original infinite run families. Exact incompatible-triple cancellation, canonical connectedness, finite activity comparisons and the actual independent N^(-3/2+epsilon) incompatible seed weight are proved. The pair/target activity deficit and third factorial-cumulant correction assembly remain open; main 11.2 and 11.3 stay in progress. Coverage remains 72/167 (main 25/73, companion 47/94); confirmed findings are 71. No activity deficit, moment bound, arithmetic count, new external input or Paper C source is assumed. No manuscript-byte change or Palomar registration.


Triple incidence checkpoint verification: Lean v4.36.0-rc2 full build passed (10153 jobs); actual axiom audit passed for all 5161 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 2876 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records are intact. Ubuntu available space: 16.35 GiB. The literal pair/target deficit, its physical effective-space alignment and the exact all-order incidence bijection are proved. Actual nonzero centered coefficients meet every complementary span. The actual incompatible triple activity is at most its independent active mass plus ONE copy of D_(2,1); the independent mass has the complete N^(-3/2+epsilon) decay. The uniform arithmetic D_(2,1) estimate and third factorial-cumulant correction assembly remain open. Main 11.1, 11.2 and 11.3 stay in progress. Coverage remains 72/167 (main 25/73, companion 47/94); confirmed improvements are 72. No target estimate, new external theorem or Paper C source is assumed. No manuscript-byte change or Palomar registration.


Third factorial-cumulant checkpoint verification: Lean v4.36.0-rc2 full build passed (10169 jobs); actual axiom audit passed for all 5190 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 2905 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records are intact. Ubuntu available space: 16.33 GiB. The actual original infinite run count has the complete third factorial-cumulant identity, including all repeated-index pair and cubic terms. Actual heterogeneous critical-band marginals give the uniform correction 12 K A2/N+2 K^3/N^2. The cumulant/positive connected activity comparison is reduced to exactly the actual D_(2,1) and pair activity A2, with the independent N^(-3/2+epsilon) term proved. The nonnegative A3-K3+ difference has the same deficit reduction. Neither remaining arithmetic activity estimate is assumed; main 11.1, 11.2 and 11.3 stay in progress. Coverage remains 72/167 and confirmed improvements remain 72. No new external input or Paper C source, manuscript-byte change or Palomar registration.


Independent target checkpoint verification: Lean v4.36.0-rc2 full build passed (10173 jobs); actual axiom audit passed for all 5197 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 2912 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records are intact. Ubuntu available space: 16.32 GiB. Every actual dependent target injects into one-block effective relation lists after exact source enumeration. The complete half-count proves N^(1/2+epsilon) targets and N^(-1/2+epsilon) independent target mass after every source family of a fixed cardinality, uniformly before L, G and all source centers, including overlaps and local defects. Consequently the literal D_(2,1) is bounded by A2 times N^(-1/2+epsilon). The full N^(-3/2+epsilon) deficit estimate still needs the pair partition and good-channel compression count; main 11.1 stays in progress. Coverage remains 72/167 and confirmed improvements remain 72. No deficit bound, new external input or Paper C source is assumed. No manuscript-byte change or Palomar registration.


Primitive general-mass checkpoint verification: Lean v4.36.0-rc2 full build passed (10179 jobs); actual axiom audit passed for all 5212 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 2927 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records are intact. Ubuntu available space: 16.31 GiB. Minimal effective nullity is bounded by every local rank without a finite-dimensional ambient assumption. Actual heterogeneous primitive weight, original infinite joint mass and admissible absolute centered mass are at most N^(1-r/2+epsilon) at every fixed r>=2. Both main 15.5 exponents follow for every fixed r>=5 on all primitive subpopulations, so its dense certificate argument is needed only at r=4. That case remains open; no growing-order or complete ordered nominal T4.3 claim is made. Coverage remains 72/167; confirmed improvements are 73. No new external estimate, Paper C source, manuscript-byte change or Palomar registration.


Ordered primitive mass checkpoint verification: Lean v4.36.0-rc2 full build passed (10187 jobs); actual axiom audit passed for all 5223 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 2938 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records are intact. Ubuntu available space: 16.30 GiB. Exact weighted finite fibers give r! ordered enumerations. The literal nominal p^r 2^rho sum and actual original infinite joint-mass sum are independently bounded by N^(1-r/2+epsilon) at every fixed r>=2. Both full ordered T4.3 source conclusions follow for every fixed r>=4 on all primitive subpopulations without separation. Only r=3 remains open there; main 15.5 still lacks only r=4. Coverage remains 72/167 and confirmed improvements remain 73. No growing-order claim, nominal-equals-actual substitution outside the regular-set convention, new external estimate or Paper C source is assumed. No manuscript-byte change or Palomar registration.


Two-witness finite budget checkpoint verification: Lean v4.36.0-rc2 full build passed (10193 jobs); actual axiom audit passed for all 5242 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 2957 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records are intact. Ubuntu available space: 16.29 GiB. Actual integer box cardinalities and matrix image bounds prove the nonzero integer kernel vector of height (3 n H)^7. The biquadratic four rectangular coefficient slot sets and triangular equation set have the exact source cardinalities. All dimension-gap inequalities, indexed kernel transport and explicit (B+1)^[7(10+c)q] height absorption are proved. The actual Runge matrix, its denominator and entry heights, primitive gcd division, integer separation and nonzero norm remain open; T9.5 stays in progress. Coverage remains 72/167 and confirmed improvements remain 73. No external Siegel lemma, new estimate or Paper C source is assumed. No manuscript-byte change or Palomar registration.


Actual Runge auxiliary checkpoint verification: Lean v4.36.0-rc2 full build passed (10203 jobs); actual axiom audit passed for all 5273 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 2988 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records are intact. Ubuntu available space: 16.28 GiB. The actual Runge matrix has common denominator 4^(6q), integer entry height (B+1)^(28q) and a nonzero integer kernel array of height (B+1)^(266q). The actual nested square-root formal numerator cancels through total degree 6q. Its four integer coefficient polynomials have the required partial degrees and the same height, with at least one nonzero polynomial. No Cauchy estimate is needed for this coefficient/kernel stage (P1-MATH-0074). Primitive gcd division and vanishing-order preservation, function independence, integer separation and the nonzero norm remain open; T9.5 stays in progress. Coverage remains 72/167 and confirmed improvements are 74. No new external estimate, Paper C source, manuscript-byte change or Palomar registration.


Primitive auxiliary coefficients checkpoint verification: Lean v4.36.0-rc2 full build passed (10209 jobs); actual axiom audit passed for all 5280 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 2995 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records are intact. Ubuntu available space: 16.28 GiB. The actual auxiliary coefficient family has a nonzero common integer polynomial factor and a quotient family with no common nonunit divisor. At least one quotient is nonzero. Its exact reduced partial degree bounds and explicit height (B+1)^(275q) follow from the complete T9.4. The original formal numerator cancellation remains in the same construction; preservation of the divided-numerator order, integer gap, function independence and nonzero norm are still open. T9.5 stays in progress. Coverage remains 72/167 and confirmed improvements remain 74. No new external estimate, additional Paper C source, manuscript-byte change or Palomar registration.


Reciprocal series order checkpoint verification: Lean v4.36.0-rc2 full build passed (10229 jobs); actual axiom audit passed for all 5305 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 3020 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records are intact. Ubuntu available space: 16.26 GiB. The actual bivariate reciprocal polynomial has exact order equal to its pole weight minus its total degree. The order multiplication law and coefficient-level quotient vanishing theorem are proved. Instantiating division still requires the actual numerator/common-factor product identity. T9.5 stays in progress. Coverage remains 72/167 and confirmed improvements remain 74. No new external estimate, additional Paper C source, manuscript-byte change or Palomar registration.


Actual primitive-order checkpoint verification: Lean v4.36.0-rc2 full build passed (10235 jobs); actual axiom audit passed for all 5326 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 3041 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records are intact. Ubuntu available space: 16.25 GiB. The actual original numerator/common-factor/reduced-numerator product identity and the exact primitive divided-numerator vanishing order are proved for the constructed integer coefficient family with height (B+1)^(275q). No division by the common factor at a point is used. Integer separation, character independence and the nonzero norm remain open. T9.5 stays in progress. Coverage remains 72/167 and confirmed improvements remain 74. No new external estimate, additional Paper C source, manuscript-byte change or Palomar registration.


Literal formal-word norm checkpoint verification: Lean v4.36.0-rc2 full build passed (10253 jobs); actual axiom audit passed for all 5371 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 3086 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records are intact. Ubuntu available space: 16.23 GiB. The literal integer word norm is proved nonzero for every nonzero four-polynomial coefficient family of independent finite reduced words. Word square-class independence, exact overlap quotient, third integer root and signed overlap relation are proved. The norm evaluates to zero whenever the actual auxiliary integer value is zero. Auxiliary nonvanishing holds in any injective domain realization of the radical identities. Analytic integer separation, general branch linkage and final norm degree/height bounds remain open. T9.5 stays in progress. Coverage remains 72/167 and confirmed improvements now total 75. No new external estimate, additional Paper C source, manuscript-byte change or Palomar registration.


Literal norm degree/height checkpoint verification: Lean v4.36.0-rc2 full build passed (10273 jobs); actual axiom audit passed for all 5416 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 3131 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records are intact. Ubuntu available space: 16.20 GiB. The actual independent-word norm has both partial degrees at most 12q, total degree at most 24q and explicit height at most (B+1)^(1200q), with the same constructed primitive coefficient family of height (B+1)^(275q). One construction retains actual w,D,Q,R, primitive coefficients, the numerator product identity, original and divided cancellations, and the nonzero bounded norm. The norm map identity is generalized to arbitrary RingHomClass morphisms, including variable swap. Analytic integer separation and actual branch linkage remain open; no point-vanishing conclusion is inferred from formal cancellation alone. T9.5 stays in progress. Coverage remains 72/167 and confirmed improvements remain 75. No new external estimate, additional Paper C source, manuscript-byte change or Palomar registration.


Real branch-value and numerator majorant checkpoint verification: Lean v4.36.0-rc2 full build passed (10283 jobs); actual axiom audit passed for all 5448 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 3163 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records are intact. Ubuntu available space: 16.19 GiB. The actual reduced numerator has coefficient majorant (B+1)^(300q)*(2B)^(a+b). Real series evaluation, geometric absolute convergence, Cauchy multiplication and finite products are proved. The actual Runge factors square to 1+gamma*t and are positive for |gamma*t|<=1/4; scaled products have the literal split-product square. Total-degree bivariate evaluation, the vanishing-tail bound, finite-word enumeration linkage and the final integer separation remain open. T9.5 stays in progress. Coverage remains 72/167 and confirmed improvements remain 75. No analytic binomial input assumption, additional Paper C source, manuscript-byte change or Palomar registration.


Actual bivariate value and vanishing-tail checkpoint verification: Lean v4.36.0-rc2 full build passed (10289 jobs); actual axiom audit passed for all 5473 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 3188 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records are intact. Ubuntu available space: 16.18 GiB. Literal total-degree bivariate evaluation is defined and proved absolutely convergent under the actual geometric coefficient majorant. An actual vanishing prefix gives the quantitative value bound 2*C*(M+1)*(R*t)^M. Branch values, finite sums, scalar multiples and literal monomial shifts have their proved real values. Reciprocal polynomial evaluation, finite-word enumeration linkage, remaining-pole scaling and final integer separation remain open. T9.5 stays in progress. Coverage remains 72/167 and confirmed improvements remain 75. No new external estimate assumption, additional Paper C source, manuscript-byte change or Palomar registration.


Actual auxiliary-value and word-enumeration checkpoint verification: Lean v4.36.0-rc2 full build passed (10297 jobs); actual axiom audit passed for all 5491 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 3206 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records are intact. Ubuntu available space: 16.17 GiB. Actual polynomial evaluation has its finite reciprocal scaling identity and integer-point casting compatibility. The literal scaled numerator value equals the actual four-polynomial auxiliaryValue. Nonzero primitive quotient members satisfy the full remaining-pole budget under the source rank bounds; zero members are handled directly. Actual finite word sets supply injective lists with exact products, lengths and offset bounds. Explicit 1/N scaling, positive integer word-root realization, final integer separation and an explicit degree-four field-norm certificate for the moreover clause remain open. T9.5 stays in progress. Coverage remains 72/167 and confirmed improvements remain 75. No new external estimate assumption, additional Paper C source, manuscript-byte change or Palomar registration.


Actual two-witness square-point polynomial checkpoint verification: Lean v4.36.0-rc2 full build passed (10307 jobs); actual axiom audit passed for all 5508 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 3223 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records are intact. Ubuntu available space: 16.16 GiB. The actual primitive auxiliary has bound (B+1)^(400q)/N and is proved integral at the given two-square integer point via canonical positive word-root realization, including the derived third root. Threshold N>(B+1)^(1200q) forces zero. The same construction supplies a nonzero integer polynomial vanishing at the point, primitive coefficient family, partial degrees12q,total24q,height1200q, uniformly for all source ranks and offsets and comparable integer points. This proves the polynomial conclusion of T9.5 without an external tail, value or integrality premise. The source moreover clause still needs an explicit degree-four field-norm realization; T9.5 stays in progress. Coverage remains 72/167 and confirmed improvements now total 76. No manuscript conclusion error, new external estimate, additional Paper C source, manuscript-byte change or Palomar registration.


## Completed two-witness proposition T9.5

`TwoWitnessTheorem.companion_T9_5` proves the full source proposition,
including the moreover clause identifying the same primitive auxiliary
norm in an actual degree-four field. The explicit common threshold and
norm-height exponent is1200; coefficient height exponent275 and the
actual integer-gap exponent400 are also proved. Real B and q are
included, and floor(q) gives stronger degree bounds. The source
half-open range is included in the proved closed comparable range.
Coverage is now73/167 (main25/73, companion48/94). Findings remain76.
The article common-curve theorem13.2 remains open. See
[T9.5 statement alignment](TWO_WITNESS_ALIGNMENT.md).

Full T9.5 checkpoint verification: Lean v4.36.0-rc2 full build passed (10315 jobs); actual axiom audit passed for all 5532 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 3247 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records are intact. Ubuntu available space: 16.14 GiB. Full companion T9.5 is proved, including the actual Algebra.norm in a field of dimension four generated by the two word roots. The same primitive coefficient family yields the nonzero vanishing integer polynomial with partial degrees12q,total24q,height exponent1200 and explicit threshold exponent1200. Real B and q are covered by floor reductions and monotone powers; no parameter integrality restriction or target premise is inserted. Coverage is73/167 (main25/73, companion48/94), and confirmed findings remain76. No new external estimate, Paper C source, manuscript-byte change or Palomar registration.


## Common-curve algebra and the first irreducible point factor

Article theorem13.2 is now in progress. The actual curve coordinate
ring and fraction field, field square classes, formal-word linear map
and entire image-rank collapse are constructed. A vanishing irreducible
point factor is extracted from actual factorization, with explicit
height, partial/total degree, primitivity and positive-degree conclusions
under the derived height threshold. Uniform resultants and assembly
of the single common factor for all pair norms remain open. Coverage
stays73/167; findings remain76. See [exact alignment](COMMON_CURVE_ALIGNMENT.md).

Common-curve algebra and point-factor checkpoint verification: Lean v4.36.0-rc2 full build passed (10333 jobs); actual axiom audit passed for all 5572 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 3287 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records are intact. Ubuntu available space: 16.13 GiB. Actual curve field and square classes, entire formal-word image-rank collapse from shared primitive norms, and actual irreducible point-factor extraction with explicit height and positive-degree budgets are proved. Uniform resultant nonvanishing/height and final source assembly remain open; article13.2 is in progress. Coverage remains73/167 and confirmed findings76. No new external estimate, Paper C source, manuscript-byte change or Palomar registration.


## Uniform resultants and simultaneous polynomial-family extraction

The full simultaneous common-factor step is proved for actual bounded
integer polynomial families. Resultant nonvanishing is derived over the
coefficient fraction field, and the common integer root follows from
the Sylvester Bezout identity. The coefficient-uniform determinant bound
gives resultant exponent124608q^2; threshold1000000q^2 constructs one
irreducible primitive two-variable factor dividing every family member,
with total degree48q and height exponent2472q. The construction is
independent of the number of family members. Final assembly from the
original bounded independent even basis via T9.5 remains open.
Coverage73/167 and findings76 are unchanged.

Uniform common-curve resultant checkpoint verification: Lean v4.36.0-rc2 full build passed (10347 jobs); actual axiom audit passed for all 5593 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 3308 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records are intact. Ubuntu available space: 16.12 GiB. Actual resultant nonvanishing, common-point vanishing and coefficient-uniform height are proved. The explicit resultant exponent124608q^2 and safe threshold1000000q^2 construct one primitive irreducible two-variable factor for an arbitrary bounded polynomial family, with total degree48q and height exponent2472q, independently of family size. Exact binary support encoding and independence of distinct actual basis words are proved. Final assembly of the source basis pair norms remains open, so article13.2 stays in progress. Coverage73/167 and findings76 are unchanged. No new external estimate, Paper C source, manuscript-byte change or Palomar registration.


## Completed common-curve theorem13.2

`CommonCurveTheorem.article_13_2` proves the full source theorem with
explicit absolute constant1000000, independent of the basis size.
Actual bounded even basis supports generate the actual T9.5 norms,
one primitive irreducible curve divides all of them, and its actual
function-field square-class map has entire image dimension at most1.
Total degree48q0, the point equation and the source height bound are
proved for this same curve. Real B,q0 and the source half-open range
are covered. Coverage is now74/167 (main26/73, companion48/94).
Findings remain76. See [full statement alignment](COMMON_CURVE_ALIGNMENT.md).

Complete common-curve theorem checkpoint verification: Lean v4.36.0-rc2 full build passed (10353 jobs); actual axiom audit passed for all 5607 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 3322 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records are intact. Ubuntu available space: 16.11 GiB. Full article theorem13.2 is proved from the actual bounded independent even basis through actual T9.5 pair norms, simultaneous primitive irreducible curve extraction and the actual function-field square-class map. Real B,q0, source comparable points, total degree48q0, point zero and common threshold/height constant1000000 are included, uniformly in the basis size. No pair-norm, common-factor, resultant bound, image-rank or unproved external premise is inserted. Coverage is74/167 (main26/73, companion48/94); findings remain76. No new manuscript conclusion error, external estimate, Paper C source, manuscript-byte change or Palomar registration.


## Actual exceptional sets and noncritical fibres for proposition13.3

Article13.3 is in progress. The actual leading-coefficient/derivative-
resultant polynomial is constructed and proved nonzero; its root set
provides at most6D^2 exceptional offsets across both blocks. Actual
regular fibres retain full degree, are separable and have exactly dY
distinct roots over an algebraically closed characteristic-zero field.
The literal integer point equation is retained. Functional-square root
matching, coordinate-cut dimension and the final grid-point lower bound
remain open. Coverage74/167 and findings76 are unchanged. See
[exact scope](INTEGER_FIBRES_ALIGNMENT.md).

Actual noncritical-fibre checkpoint verification: Lean v4.36.0-rc2 full build passed (10359 jobs); actual axiom audit passed for all 5628 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 3343 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records are intact. Ubuntu available space: 16.10 GiB. Actual nonzero exceptional polynomials, exact bad-offset membership and the combined6D^2 budget are proved. Regular specialization over any characteristic-zero field preserves degree and is separable; each root has nonzero derivative, and the actual finite root set over an algebraically closed field has cardinality dY. Literal integer point evaluations are retained. Functional-square root matching, coordinate-cut dimension and the final integer-grid lower bound remain open, so article13.3 stays in progress. Coverage74/167 and findings76 are unchanged. No new external estimate, Paper C source, manuscript-byte change or Palomar registration.


## Actual functional-square matching by formal Hensel branches

The local matching stage of article13.3 is now proved. Actual regular
fibre roots lift into the complete power-series ring; the exact curve
substitution kernel and actual function-field map are proved. An
unmatched selected offset would produce T times a unit, nonsquare even
in the fraction field, contradicting the actual functional square.
P1-MATH-0077 records this alternative to geometric normalization.
The coordinate-cut dimension and final grid-count assembly remain open,
so coverage stays74/167. Confirmed findings now77. Ubuntu remains above
the disk alert threshold; only the required Hensel dependency cache was
added. See [alignment](INTEGER_FIBRES_ALIGNMENT.md).

Formal Hensel root-matching checkpoint verification: Lean v4.36.0-rc2 full build passed (10443 jobs); actual axiom audit passed for all 5652 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 3367 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records are intact. Ubuntu available space: 16.05 GiB. Actual simple-root lifting follows from proved power-series adic completeness and Hensel after unit leading-coefficient normalization. The actual formal branch, exact curve substitution kernel, injective coordinate-ring map and actual function-field fraction map are proved. An unmatched selected fibre gives an actual T-times-unit word series, irreducible and nonsquare in its fraction field; actual functional squares therefore force an integer-offset match. No normalization, branch, valuation, kernel or target matching conclusion is assumed as an external theorem. This confirms P1-MATH-0077. Coordinate-cut dimension and final grid-count assembly remain open; article13.3 stays in progress. Coverage74/167 and findings77. No new manuscript conclusion error, external estimate, Paper C source, manuscript-byte change or Palomar registration.


## Completed integer-grid proposition13.3

Article13.3 is proved from the actual source hypotheses. The class-map
kernel followed by actual bad-coordinate restrictions has dimension
at least t-1-6D^2. Both injective physical projections force this many
used offsets. Actual Hensel root matching and a proved swap map of
the actual function fields give dY and dX integer points per selected
regular fibre, respectively. The actual grid count is at least their
maximum times the retained dimension. Real B,q, exact real-box grid
membership and both original/truncated lower bounds are included.
P1-MATH-0077 now covers the completed proof improvement. Coverage75/167
(main27/73, companion48/94); findings remain77. See
[statement alignment](INTEGER_FIBRES_ALIGNMENT.md).

Complete integer-grid checkpoint verification: Lean v4.36.0-rc2 full build passed (10457 jobs); actual axiom audit passed for all 5685 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 3400 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records are intact. Ubuntu available space: 16.04 GiB. Full article13.3 is proved through the actual common-curve certificate, the actual class-map and exceptional-coordinate kernels, bounded basis supports, both injective physical projections, actual Hensel root matching and the actual swapped function-field map. The retained dimension is at least t-1-6D^2 and the actual integer-grid lower bound has constant6. Original real parameters, exact real-box grid membership and the original real/truncated natural lower bounds are proved. No branch, normalization, matching, dimension-loss or target grid count is an unproved input. Coverage75/167 (main27/73, companion48/94); findings77. No optimized constant, source-conclusion error, external point-count estimate, Paper C source, manuscript-byte change or Palomar registration.


## Actual component and incidence stages of13.1

Article13.1 is in progress. Actual medium-prime columns on actual
large-prime components have total weight at most2B*sum(1/p)+2*#P.
The one-third heavy-column loss and2B/(M+1) oversized-component loss
give an explicit retained-family cardinality bound against actual
intersection rank and defective count. Both physical projections and
the actual first-block prime-parity image are injective. Actual
medium-prime equations equal the selected physical-occurrence sums
and have a constructed labelled incidence model with identical kernel,
including loops and parallel edges. The quantitative prime harmonic
estimate, short cycles, final sparse kernel basis and full source
assembly remain open. Coverage75/167 and findings77 are unchanged.
See [alignment](SHORT_BASIS_ALIGNMENT.md).

Component-stage checkpoint verification: Lean v4.36.0-rc2 full build passed (10469 jobs); actual axiom audit passed for all 5737 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 3452 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records are intact. Ubuntu available space: 16.01 GiB. The actual retained component family, literal medium-prime columns, finite one-third heavy-column loss and oversized-component budget are proved. Both physical projections and the actual first-block prime-parity image are injective. Actual medium-prime equations equal selected physical-occurrence sums and have a constructed labelled incidence model with identical kernel. Quantitative short cycles, the prime harmonic estimate, sparse final kernel basis and full short-basis assembly remain open; article13.1 stays in progress. Coverage75/167 (main27/73, companion48/94); findings77. No source-conclusion error, external graph estimate, additional Paper C source, manuscript-byte change or Palomar registration.


## Sparse kernel basis and actual final cut for13.1

The sparse fundamental-kernel-basis step is proved. An actual right
inverse on actual pivot columns gives a basis of the actual kernel
with support<=s+1 for s equations. Literal physical supports transfer
to ell*(s+1). After an actual medium-prime subspace, the constructed
small-prime and two-parity kernel maps injectively into the actual
complete even-relation code, loses at mostpi(z)+2 dimensions and has
a basis of support<=ell*(pi(z)+3) for an input basis of support<=ell.
Both physical projections and the actual square-class image remain
injective. The short-cycle basis with the required length/rank bounds,
the sharp prime-harmonic estimate and full asymptotic assembly remain
open. Article13.1 stays in progress; coverage75/167 and findings77.
See [alignment](SHORT_BASIS_ALIGNMENT.md).

Sparse-final-cut checkpoint verification: Lean v4.36.0-rc2 full build passed (10479 jobs); actual axiom audit passed for all 5759 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 3474 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records are intact. Ubuntu available space: 16.00 GiB. An actual supported section on pivot columns, the actual sparse kernel basis, literal physical support transport and the actual final small-prime/two-parity cut are proved. The cut maps injectively into actual complete even relations, loses at mostpi(z)+2 dimensions and has a basis of support<=ell*(pi(z)+3), preserving physical and square-class-image injectivity. Its input medium-prime subspace and basis are explicit data. Short-cycle construction, its length/rank estimates, the sharp prime-harmonic bound and full source asymptotic assembly remain open; article13.1 stays in progress. Coverage75/167 (main27/73, companion48/94); findings77. Read-only Paper C comparisons introduce no additional source dependency, external estimate or assumed pivot/basis/completeness theorem. Original manuscripts and Palomar status are unchanged.


## Actual sharp prime-harmonic and retained-component estimates for13.1

The source prime-harmonic window is proved from actual factorial
floors, actual prime-power summability and an actual Abel integral
with all regularity hypotheses discharged. Its explicit inverse-log
error supplies the exact(2/3)B log(1/a) retained-component loss. The
actual retained family has count>=d_xy-(2/3)B log(1/a)-K_a B/log B
uniformly over all critical pairs; K_a precedes C. Compatibility,
nonalignment and non-overlap are unnecessary. The graph short-cycle
length/rank estimates and final source short-basis assembly remain
open, so article13.1 stays in progress. Coverage75/167, findings77.
See [alignment](SHORT_BASIS_ALIGNMENT.md).

Prime-harmonic checkpoint verification: Lean v4.36.0-rc2 full build passed (10493 jobs); actual axiom audit passed for all 5801 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 3516 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records are intact. Ubuntu available space: 15.98 GiB. Actual factorial floors and prime-power summability construct the weighted prime-logarithm error constant; the actual Abel integral and exact real cutoffs prove the source prime-harmonic estimate with inverse-log error. Actual component deletion, internally proved prime-count and defective-vertex budgets give retained count>=d_xy-(2/3)B log(1/a)-K_a B/log B uniformly over all critical pairs, with K_a before C. No weighted-error, prime-harmonic, PNT-remainder or retained-count estimate is an unproved input. Graph short-cycle length/rank estimates and full short-basis assembly remain open; article13.1 stays in progress. Coverage75/167 (main27/73, companion48/94); findings77. Only one selective Log.Sum cache file was fetched; no additional Paper C source, manuscript-byte change or Palomar registration.


## Actual greedy independence and complete short-vector reduction

`GreedyShortKernel` proves the actual witness-edge deletion argument.
A nonzero short kernel vector has an actual nonzero coordinate. Deleting
that coordinate and recursing gives independent vectors: the chosen
coordinate vanishes on the span of all later vectors. If every remaining
set of more than r columns has a kernel vector of support<=k, the actual
spanned subspace has dimension>=#columns-r and an actual basis of such
vectors. Literal physical support transfers through the actual linear map.

`ColumnDependencies` constructs actual unit or difference vectors for
zero and equal columns. `BinaryIncidenceShortVectors` specializes these
to loops and unordered parallel endpoints, including characteristic2
and the exact finite-function/Finsupp correspondence. These cases have
support1 and2; no simple-graph short-cycle bound is inferred from them.

`ComponentSelectionSupport` identifies the actual support of selecting
one retained component with its actual physical vertex set, of size<=M.
`ShortBasisCycleReduction` combines the proved greedy construction,
actual medium-prime map, physical selection and actual final cut. Its
**explicit local hypothesis** is: every edge subset of cardinality>r
has a nonzero vector of the actual incidence kernel, supported there
and of cardinality<=k. Under this hypothesis it constructs an actual
complete-relation image with

    dimension >= #retained - r - (pi(z)+2),
    basis physical support <= M*k*(pi(z)+3).

Both physical projections and the actual common square-class map are
injective. The conditional statement is finite preparation, not the
full source theorem. The local existence hypothesis with the required
logarithmic k and residual r is still open for actual simple graphs.
Final source asymptotic assembly also remains open. Coverage75/167,
confirmed findings77. No additional external estimate, Paper C source,
manuscript-byte change or Palomar registration is introduced.

Lean v4.36.0-rc2 full build passed (10503 jobs); actual axiom audit passed for all 5821 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 3536 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records are intact. Ubuntu available space: 15.97 GiB. Actual witness-coordinate deletion constructs an independent short-kernel family and its actual basis. Loops, unordered parallel columns and the finite incidence correspondence are proved. Actual component unit-selection supports are their actual physical vertex sets. Under the explicit local short-vector hypothesis, the actual final complete-relation image has dimension at least #retained-r-(pi(z)+2), a basis of physical support at most M*k*(pi(z)+3), and injective physical and square-class maps. The local short-vector hypothesis with the source logarithmic length and residual-edge bounds remains open; article13.1 stays in progress. Coverage75/167 (main27/73, companion48/94); findings77. No unproved short-cycle estimate is counted as a completed numbered result. No new external estimate, additional Paper C source, manuscript-byte change or Palomar registration.


## Actual finite Moore bound and complete short-basis construction

`LabelledEdgeCore` proves actual pruning by finite-set induction, with
an exact edge-deletion budget. If e>2d*n, a nonempty actual vertex set
retains incident degree at least2d. Edge labels are preserved, including
loops and parallel edges. An exact double count bounds the sum of
incident degrees on a set by twice its number of touching edge labels.

`ShortIncidenceRoutes` represents a vertex by an actual bounded-support
edge vector with boundary delta(root)+delta(vertex). Adding an actual
edge extends the route. In the absence of kernel vectors of support
at most2r+1, every actual edge with both endpoints in the radius-r ball
is exactly the difference of its actual endpoint route vectors. Actual
independent single-edge coordinates in their actual finite span give
#insideEdges<=#ball. No forest or BFS-rank estimate is assumed.

`IncidenceBallGrowth` constructs the actual finite route balls. The
proved rank and incidence bounds give d*#ball(r)<=#ball(r+1) in a core
of incident degree>=2d. Hence #ball(r)>=d^r. Comparing with the actual
vertex set proves the finite Moore-type statement

    e>2d*n and n<d^r => an actual nonzero incidence-kernel vector
                         of support<=2r+1 within these edge labels.

This proof treats labelled incidence maps directly; no simple-graph
conversion, girth result or external short-cycle theorem is a premise.

`ShortBasisFiniteConstruction` applies this bound to the actual
retained components, actual medium-prime equations and constructed
incidence endpoints. The proved injective augmentation transports the
actual kernel vector back to the actual medium-prime map. With
n=#mediumPrimes+1 and n<d^r, the actual constructed complete-relation
image has

    dimension >= #retained - 2d*n - (pi(z)+2),
    basis physical support <= M*(2r+1)*(pi(z)+3).

Both physical projections and the actual common square-class map are
injective. The earlier local short-vector hypothesis is now discharged
in this finite construction. The remaining obligations for full13.1
are the numerical choice of d,r and the source logarithmic estimates
and asymptotic assembly. Coverage75/167, confirmed findings77; no new
source-conclusion error, optimized bound, Paper C source, manuscript-
byte change or Palomar registration is claimed.

Lean v4.36.0-rc2 full build passed (10511 jobs); actual axiom audit passed for all 5855 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 3570 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records are intact. Ubuntu available space: 15.96 GiB. Actual labelled vertex pruning, exact incidence double counting, bounded edge-vector routes and their actual finite span rank prove a finite Moore bound internally: e>2d*n and n<d^r force an actual nonzero incidence kernel vector of support<=2r+1. Applying it to actual retained components and actual medium-prime columns discharges the earlier local short-vector hypothesis. The actual complete-relation construction has dimension>=#retained-2d*n-(pi(z)+2), basis physical support<=M*(2r+1)*(pi(z)+3), and injective physical and square-class maps. Numerical logarithmic parameter choices and full source asymptotic assembly remain open; article13.1 stays in progress. Coverage75/167 (main27/73, companion48/94); findings77. No unproved graph, BFS, girth, rank or cycle-length estimate, additional Paper C source, manuscript-byte change or Palomar registration.


## Complete article short-basis theorem13.1

Article13.1 is complete. Actual labelled incidence balls, witness-edge deletion, final sparse small-prime/parity constraints, actual range-basis transport and all logarithmic choices prove the full source dimension and physical-support estimates. Both actual physical projections and the common square-class map are injective; every nonzero vector selects nonempty even sets and a nonzero common class. Multiplicative constants depend on a alone, before C, propagating P1-MATH-0006; P1-MATH-0078 adds a=1. The explicit safe support constant is352/a. Compatibility, nonalignment and disjoint numerical windows are unnecessary. Coverage76/167(main28/73,companion48/94), confirmed findings78. See [alignment](SHORT_BASIS_ALIGNMENT.md).

Lean v4.36.0-rc2 full build passed (10519 jobs); actual axiom audit passed for all 5879 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 3594 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records are intact. Ubuntu available space: 15.94 GiB. Full article13.1 is proved: the actual complete-relation subspace and its actual transported basis have dimension >=d_xy-(2/3)B log(1/a)-KD(a) B/sqrt(log B) and literal physical support<=KS(a) B^a log B/loglog B. Both physical projections and the actual common square-class map are injective; every nonzero vector selects nonempty even sets in both formal blocks and has nonzero common class. All actual prime estimates, retained-component bounds, labelled incidence-core/route/ball arguments, witness deletion, final sparse kernel cuts, basis transport and logarithmic numerical estimates are internally proved. Constants KD(a),KS(a) precede C, with a C-dependent threshold; KS(a)=352/a is a safe explicit choice. P1-MATH-0006 propagates this constant order, and P1-MATH-0078 adds the endpoint a=1. No compatibility, nonalignment, non-overlap, short-cycle, sparse-basis or target-bound premise. Coverage76/167 (main28/73, companion48/94); findings78. No optimized constant, source-conclusion error, new external estimate, added Paper C source, dependency download, manuscript-byte change or Palomar registration.


## Growing-degree analytic reduction with an explicit BCN input

The actual profile endpoint estimate, its cap-growth-free variant, all logarithmic weights and uniform little-o limits are proved. Actual plane-polynomial grids and exact real box membership are constructed. Under the ordinary explicit named BCN plane bound, article13.5 has both its exact uniform big-O bound and uniform o(B) conclusion, strengthened to upper power caps with0<=a<1/2. The external BCN proof and geometric specialization remain open:13.4 is in progress,13.5 conditional, and proved coverage stays76/167. P1-MATH-0079 records the cap improvement; confirmed findings79. See [alignment](GROWING_DEGREE_ALIGNMENT.md).

Lean v4.36.0-rc2 full build passed (10525 jobs); actual axiom audit passed for all 5900 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 3616 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records are intact. Ubuntu available space: 15.93 GiB. Actual finite plane-polynomial integer grids, exact real floor boxes and a negation bijection to the previously used offset grid are proved. Convex logarithmic degree profiles prove the endpoint maximum and the cap-growth-free bound4sqrt(H)+e*(M^2+(log H)^2). All real-logarithmic weights and uniform little-o limits are internally proved. The actual source big-O and uniform o(B) grid-count conclusions retain PlaneCurvePointCount.UniformBound c kappa as an ordinary explicit argument. The external BCN proof and geometric plane-polynomial specialization remain open; no global axiom or completed proof of13.4 is introduced. Article13.5 is conditional and adds no proved coverage. P1-MATH-0079 records that only an upper degree cap and0<=a<1/2 are needed. Coverage76/167 (main28/73, companion48/94); confirmed findings79. The exact primary author version arXiv2302.04209v2, Theorem2 equation(27), page7 was checked. No extra Paper C source, dependency download, manuscript-byte change or Palomar registration.


## Actual complete-relation words, squares and common curve

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

Lean v4.36.0-rc2 full build passed (10531 jobs); actual axiom audit passed for all 5927 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 3643 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records are intact. Ubuntu available space: 15.92 GiB. Actual complete relations map injectively to actual offset words at i-1. Literal supports, total physical support, actual image bases, dimension and both projection injectivities are preserved. Actual prime-parity equations prove the selected product square, including the zero-product case, and exact label casts prove square-valued word evaluation at the actual centers. The actual relation certificate with rank>=2, support<=2q and the explicit point threshold constructs the actual common curve; its actual grid count uses the original relation-space rank and exceptional constant6. No separate square, arbitrary word basis, support correspondence or target grid count is assumed. Critical asymptotic threshold assembly, degree-one alignment and the final nonaligned contradiction remain open for13.6; BCN remains separately explicit and unformalized. Coverage76/167 (main28/73, companion48/94); confirmed findings79. No new mathematical correction, external input, Paper C source, cache download, manuscript-byte change or Palomar registration.


## Actual degree-one common curve forces alignment

`BivariateLineGeometry` proves that an actual total-degree-one
nested integer polynomial is a literal nonconstant linear form. Its
actual zero points satisfy the exact collinearity determinant.

`BoundedPointAlignment` proves that two distinct actual integer points
p,q in[-B,B]^2, collinear with a center(x,y) having x,y>B, force
positive reduced coefficients a,b<=2B and

    abs(b*x-a*y) <= (a+b)B.

Ordering the first coordinates forces the second coordinates to have
the same order, because both center differences are positive. Actual
gcd division gives positive coprime coefficients, the small coefficient
bounds and the exact reduced affine error. For B>=2 this is the actual
source alignment with allowed coefficient height B^3.

`LinearCurveAlignment.actual_linear_case` applies the already proved
actual common-curve grid bound. At total degree1, actual relation rank
at least9 leaves at least two bounded integer points after the safe
exceptional budget6. The actual positive-center alignment follows.
Consequently, nonalignment excludes degree1 for such an actual common
curve. No line coefficient-height estimate, sign input or additional
functional-square/root-matching witness is supplied.

P1-MATH-0080 records this proof simplification. It does not remove the
common-curve construction or its point threshold from the full argument.
The critical asymptotic threshold assembly, the actual degree>=2 BCN
input/geometric specialization, and the final nonaligned contradiction
remain open. Article13.6 stays in progress. Coverage76/167, confirmed
findings80; no new external theorem, Paper C source, dependency download,
manuscript-byte change or Palomar registration.

Lean v4.36.0-rc2 full build passed (10537 jobs); actual axiom audit passed for all 5935 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 3651 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records are intact. Ubuntu available space: 15.90 GiB. Every actual degree-one nested integer polynomial has a proved nonconstant linear form and actual collinear zero points. Two actual bounded distinct integer points and a center with both coordinates>B give positive reduced alignment coefficients<=2B and exact affine error<=(a+b)B. Actual gcd reduction, sign, coefficient bounds and source-height conversion are proved. The already proved actual common-curve grid lower bound supplies two such points at relation rank>=9 when D=1. Nonalignment therefore excludes degree1 for that actual common curve. P1-MATH-0080 records the proof simplification: no coefficient-height sign argument or additional functional-square/root-pairing witness is needed in the linear branch. The original curve construction and point  threshold remain necessary. Critical threshold assembly, unformalized BCN/geometric specialization and the final nonaligned contradiction remain open;13.6 stays in progress. Coverage76/167 (main28/73, companion48/94); confirmed findings80. No optimized threshold, source-conclusion error, new external theorem, added Paper C source, cache download, manuscript-byte change or Palomar registration.


## Full nonaligned critical reduction under explicit BCN

The complete actual nonaligned-rank argument is now proved under
the ordinary explicit integer-polynomial BCN input
`IntegerCurvePointInput.UniformBound c kappa`, with c>0. The source
BCN theorem and its specialization remain unformalized. This is a
conditional result and does not increase proved numbered coverage.

For every epsilon>0 choose the actual exponent

    a = exp(-3epsilon/8)/2,
    (2/3)log(1/a) = (2/3)log2 + epsilon/4,

and b=(a+1/2)/2, so a<b<1/2. The proved source short basis13.1 has
physical basis support at most2q for q=floor(B^b), once B is large.
The actual q satisfies1<=q<=B. All floor, logarithmic and power
estimates are proved. The critical geometry B<=U logN and the actual
budget q^2 log(B+1)=o(B) discharge the explicit common-curve threshold
(B+1)^(1000000q^2)<N.

If d_xy>((2/3)log2+epsilon)B, the extracted actual rank exceeds
epsilon B/2. Its actual common curve has D<=48B^b. The proved
degree-one branch gives literal source alignment when extracted
rank>=9 and x,y>B, so nonalignment forces D>=2. The actual grid
rank budget is

    rank <= #integerGrid + 1 + 6D^2.

The loss1+6D^2 is at most epsilon B/4 eventually. The named external
integer BCN input, through the proved growing-degree analytic
estimate, bounds that same actual grid by epsilon B/8. This gives
the contradiction. No compatibility assumption is used.

`critical_rank_bound` has one N0 before every length in the fixed
critical band and every actual dyadic pair. `nonalignedPairs`,
`maximalRank` and `maximalRatio` construct the actual finite maximum,
with value0 for an empty pair set. Its uniform bound and the literal
Filter.limsup inequality hold for every eventually critical length
function L(N). The numerical inequality(2/3)log2<1/2 is proved
unconditionally by rational power/log bounds. A single sigma<1/2
is chosen before every band constant C, giving a uniform half-window
gap under the same explicit external input.

The field-polynomial input used for conditional13.5 and the integer-
polynomial input here are separately named. Their rational/Gauss
presentation bridge has not been claimed proved. No global axiom,
assumed target rank bound or hidden external theorem is introduced.
Article13.6 is now conditional;13.4 remains in progress and13.5
conditional. Proved coverage76/167 (main28/73, companion48/94),
confirmed findings80. No added Paper C source, dependency download,
manuscript-byte change or Palomar registration.

Lean v4.36.0-rc2 full build passed (10545 jobs); the actual axiom audit passed for all5956 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All3673 distinct ledger/finding declarations were directly checked. All138 original manifest entries and167 numbered records are intact. Ubuntu available space:15.88 GiB. The actual critical short basis, support floor q=floor(B^b), common-curve point threshold, degree<=48q, degree-one exclusion, real grid rank budget, sublinear degree loss and final contradiction are kernel-checked. The actual finite nonaligned-pair maximum, literal Filter.limsup bound and a fixed sigma<1/2 before every C retain the ordinary explicit integer-polynomial BCN input. The numerical threshold<1/2 is unconditional. BCN and its rational/Gauss/geometric presentation specialization remain unformalized. Article13.6 is conditional; proved coverage76/167 (main28/73, companion48/94), confirmed findings80 unchanged. No added Paper C source, dependency download, manuscript-byte change or Palomar registration.


## The integer/rational BCN bridge is proved

The integer-to-rational presentation bridge is now proved.
`IntegerCurveRationalization.coefficientMap` is the literal nested
coefficient ring map. An injective coefficient map preserves actual
total degree and the entire actual finite integer grid. Every unit
of a nested polynomial ring over a domain has total degree0.

The rational nested ring is constructed as two successive polynomial
localizations of the integer nested ring at nonzero integer constants.
An actual irreducible integer polynomial is prime in that UFD. Its
image is nonzero by coefficient injectivity and is not a unit because
its positive total degree is preserved. The pinned localization prime
mapping theorem therefore proves actual rational irreducibility.
No primitive-content, Gauss-bridge or irreducibility conclusion is
assumed. The field input applied at K=Q now gives the exact integer
input, with identical c,kappa,D,H and actual grid cardinality.

`NonalignedRankFieldBCN` consequently proves the full uniform rank
bound, literal source limsup and uniform strict half-window gap from
the same single `PlaneCurvePointCount.UniformBound c kappa` argument
already used in13.5. The integer input is a proved specialization of
that field input, not a second independent unformalized assumption.
BCN itself and the geometric-to-plane-polynomial theorem presentation
remain unformalized.13.4 stays in progress;13.5 and13.6 stay
conditional. Proved coverage76/167, confirmed findings80 unchanged.
No new Paper C source, dependency download, manuscript-byte change or
Palomar registration. One additional pinned Mathlib localization
module was compiled locally from existing sources.

Lean v4.36.0-rc2 full build passed (10551 jobs); actual axiom audit passed for all5965 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All3682 distinct ledger/finding declarations were directly checked. All138 original manifest entries and167 numbered records are intact. Ubuntu available space:15.87 GiB. The actual nested coefficient map preserves total degree and every integer grid. Two actual polynomial localizations, actual coefficient injectivity and the total-degree nonunit obstruction prove rational irreducibility of every positive-degree irreducible integer nested polynomial. The integer BCN input is derived from the field-polynomial input with unchanged c,kappa,D,H and actual grid cardinality. Full13.6 rank, actual maximum, limsup and strict half-window gap now use the same single field-polynomial BCN argument as13.5. No independent integer/Gauss bridge assumption remains. BCN itself and its geometric presentation remain unformalized;13.4 is in progress,13.5 and13.6 conditional. Coverage76/167 (main28/73, companion48/94), findings80. No extra Paper C source, dependency download, manuscript-byte change or Palomar registration.


## All triple-rank and joint probability conclusions under explicit BCN

All three source conclusions of article13.8 are now proved under
the same ordinary explicit field-polynomial BCN input as13.5 and13.6.
The external BCN proof and geometric presentation remain unformalized;
this row is conditional and adds no proved numbered coverage.

The actual finite-dimensional relation spaces satisfy

    rho({x,y,z}) <= L + min(d_xy,d_xz,d_yz).

This is proved from actual insertion-nullity and pair-intersection
identities, not assumed. Every actual three-element set can be
reconstructed from any two of its distinct members. Known alignments
use the proved compatible half-window bound13.7, including exact
contact; nonaligned pairs use the proved reduction13.6 under BCN.
The actual enlarged alignment predicate is transported with exact
coefficient heights. The B=L+1 to L conversion is proved uniformly.
Thus compatible triple nullity is at most(3/2+epsilon)L. A triple
containing a nonaligned pair has nullity at most
(1+(2/3)log2+epsilon)L, even without compatibility.

The probability step can be shortened. The proved critical local
rigidity gives the actual cap p_x<=2*2^(-L), including zero marginals.
The exact compatible pair identity, and a separate zero-mass case,
give the unconditional finite bridge

    q(I) <= q({x,y}) <= 4*2^(-2L+d_xy)

whenever I contains distinct x,y with the stated local marginal caps.
The cap itself is proved uniformly for all actual dyadic starts.
No third-window rank or marginal estimate enters this step.
The exponential identity for this finite mass, the exact critical
band error and absorption of its fixed constant into N^epsilon are
proved. Under the same BCN input, one threshold precedes all actual
families of cardinality at least2, giving q(I)<=N^(-3/2+epsilon),
with no order bound or compatibility restriction. In particular all
actual triples satisfy the source probability bound. An actual finite
maximum over the three-element subsets is constructed by a zero-
adjoined max fold and satisfies the same uniform estimate.

P1-MATH-0081 records the shorter pair-based probability proof, explicit
finite factor4 and extension to every larger family. P1-MATH-0082
records removal of compatibility from the stronger nonaligned-triple
rank bound. Neither claims an improved N exponent or a proof of BCN.
Proved coverage76/167 (main28/73, companion48/94), confirmed findings82.
No added Paper C source, dependency download, manuscript-byte change
or Palomar registration.

Lean v4.36.0-rc2 full build passed (10561 jobs); actual axiom audit passed for all5988 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All3705 distinct ledger/finding declarations were directly checked. All138 original manifest entries and167 numbered records are intact. Ubuntu available space:15.85 GiB. Actual triple insertion/nullity, the minimum pair-rank bound, reconstruction from any pair, the exact critical local marginal cap and the finite pair/family probability bound with factor4 are proved without BCN. The B=L+1 to L conversion, exact binary-mass exponential identity and critical N-exponent absorption are proved. Under the same single field-polynomial BCN input as13.5 and13.6, all compatible pairs have a uniform half-window rank bound, all compatible triples have nullity<=(3/2+epsilon)L, every triple containing a nonaligned pair has the stronger1+(2/3)log2 bound without compatibility, and every actual family of cardinality>=2 has joint mass<=N^(-3/2+epsilon). The literal finite triple-probability maximum is constructed and bounded. P1-MATH-0081 and0082 record the larger-family probability proof and compatibility-free nonaligned-triple scope. BCN itself and its geometric presentation remain unformalized;13.8 is conditional, not proved coverage. Coverage76/167 (main28/73, companion48/94), confirmed findings82. No added Paper C source, dependency download, manuscript-byte change or Palomar registration.


## Exact actual retained-reference identity and norm

The actual finite retained-reference identity and ordinary l1 bound
are proved. The source cardinality coefficients F_r,G_r and their
literal binomial-count/grouping correspondence remain to be verified;
T17.2 stays in progress and adds no completed numbered coverage.

Equal compressed nullity makes extension by zero from the actual pair
relation kernel surjective. Every actual relation therefore vanishes
outside the compressed pair. Proper nonempty restrictions other than
that pair have no full-support relation. The proved actual Fourier
criterion kills their actual centered moments. Finite centered-moment
reconstruction then proves the exact heterogeneous identities

    q(I)=prod_x p_x                     for direct I,
    q(I)=q(e)*prod_(x in I\e) p_x       for pair-compressed I.

Local admissibility is explicit; global affine incompatibility is not
discarded. Incompatible compressed families have their actual zero
joint moment. All factorization steps are proved internally, rather
than assumed as target probability identities.

Direct families and families containing one compressed pair have an
actual disjoint finite enumeration. A dependent pair is unique, so
the sum over edges and admitted extensions has no multiplicity. A
literal union/erasure bijection reindexes every admitted extension.

For arbitrary heterogeneous positive actual marginals on any finite
admissible ground set and any chosen family of dependent pairs, the
retained reference equals the independent Bernoulli product plus the
sum of pair corrections, minus the two actual independent deficit
polynomials. Each deficit sums the actual excluded subsets or failed
compressed extensions. Their ordinary l1 costs are bounded by the
corresponding independent weights times2^(original cardinality),
with no suffix factor or unproved independence assumption.

On the actual regular dyadic ground set with actual goodEdges,
the exact marginal identities specialize the product reference to
b^n+beta*Delta^2*b^(n-2), where beta is the actual sum of good-edge
joint moments. For every N>=2,L>0 and every real cutoff H,
`finite_identity` and `finite_norm_bound` prove the finite source form
with subset-defined deficits. The remaining F_r,G_r cardinality
grouping is not silently identified with this already proved form.

P1-MATH-0083 records the heterogeneous finite extension. No BCN,
unproved literature input, Paper C port, dependency download,
manuscript-byte change or Palomar registration is introduced.
Proved coverage76/167, confirmed findings83.

Lean v4.36.0-rc2 full build passed (10575 jobs); actual axiom audit passed for all6033 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All3750 distinct ledger/finding declarations were directly checked. All138 original manifest entries and167 numbered records are intact. Ubuntu available space:15.84 GiB. Equal compressed nullity is proved to force actual relation support inside the pair. The exact heterogeneous direct/compressed joint formulas follow from actual Fourier full-support and centered-moment reconstruction, including globally incompatible families by their actual zero mass. Direct/pair families have a proved disjoint enumeration and literal extension/union bijection. The finite heterogeneous retained-reference product identity and ordinary l1 bound are proved on arbitrary admissible finite grounds, with no assumed target probability factorization. On actual regular starts and actual goodEdges the product reference is exactly b^n+beta*Delta^2*b^(n-2), for everyN>=2,L>0 and every realH. P1-MATH-0083 records this heterogeneous finite extension. The originalF_r,G_r cardinality grouping remains open, soT17.2 is in progress. Coverage76/167 (main28/73, companion48/94), confirmed findings83. No BCN input, added external theorem, Paper C port, dependency download, manuscript-byte change or Palomar registration.


## Completed companionT17.2 with exact cardinality deficits

CompanionT17.2 is now proved in full, including the literal source
cardinality coefficients, their binomial counts, every zero convention,
the total weighted deficits, actual signed-measure identity and ordinary
l1 estimate. The theorem holds for everyN>=2,L>0 and real cutoffH;
the critical-band instance needs no further asymptotic argument.

`directAt` is exactly the r-element subfamilies of the actual regular
set whose addition map is injective. `gamma` is exactly the h-element
subsets of G\e whose singleton spaces and the actual compressed block
are in direct sum. Both source interpretations are proved. The actual
complement counts equal

    choose(n,r)-#directAt(r),
    choose(n-2,h)-#gamma(e,h).

Their nonnegativity and the equality between natural subtraction and
the corresponding real difference are proved. The actual F_r is
p^r times the first difference. Each edge contributes to G_r its
actual joint moment times p^(r-2) times the second difference, with
G_0=G_1=0 by the literal r<2 guard. F_0=F_1=0, all coefficients
are nonnegative, and both sequences vanish for r>n.

An exact finite fiber partition by cardinality proves every polynomial
and weighted-mass regrouping. In particular the two subset-defined
deficit polynomials sum to

    sum_r scalar(F_r+G_r)*Delta^r,

and their independent masses are the exact source sums of2^r F_r
and2^r G_r. These totals are also proved equal to the infinite tsums,
using the verified zero tails. No finite/infinite grouping or binomial
coefficient convention is assumed.

`companion_T17_2` proves the literal retained-reference identity and
ordinary l1 bound. `companion_T17_2_measures` transports them to actual
atomic signed measures and the sum of absolute singleton masses.
The actual coefficients are Bochner joint moments of the original
infinite prime-sign model. All direct/compressed probability formulas,
affine-zero cases and unique-pair enumeration were proved internally
in the preceding finite checkpoint.

P1-MATH-0083 remains the heterogeneous finite extension. Its equal-
marginal specialization now has the complete source cardinality form.
No new mathematical finding, BCN input, literature premise, Paper C
port, dependency download, manuscript-byte change or Palomar
registration. Proved coverage77/167 (main28/73, companion49/94),
confirmed findings83.

Lean v4.36.0-rc2 full build passed (10581 jobs); actual axiom audit passed for all6070 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All3787 distinct ledger/finding declarations were directly checked. All138 original manifest entries and167 numbered records are intact. Ubuntu available space:15.82 GiB. Literal source directAt and gamma definitions are proved equivalent to actual addition-map and compressed directness. Exact binomial complement counts, valid natural-to-real subtraction, nonnegative F_r,G_r, r=0,1 and r>n zero conventions, shifted-cardinality fiber grouping, both deficit polynomials and both independent weighted masses are proved. Ftotal,Gtotal equal the source infinite weighted tsums. companion_T17_2 proves the exact source reference identity and l1 bound, and companion_T17_2_measures proves their actual atomic signed-measure and absolute singleton-tsum forms. All probability coefficients are actual Bochner moments and all direct/compressed factorization and unique-pair enumeration steps are proved internally. The complete source theorem holds for everyN>=2,L>0 and realH, without needing a critical-band argument. T17.2 is proved. P1-MATH-0083 remains the heterogeneous finite extension; no new finding is added. Coverage77/167 (main28/73, companion49/94), confirmed findings83. No BCN input, new literature premise, Paper C port, dependency download, manuscript-byte change or Palomar registration.


## Complete conditional growing-order bound forT19.4

The missing bounded second-moment seed and the full growing-order
source conclusion of companionT19.4 are now proved under the single
ordinary explicit field-polynomial BCN input already used for13.5,
13.6 and13.8. The deterministic exception, actual infinite-model
independence, first logarithmic rate and recurrence remain unconditional.
The result is conditional and adds no proved numbered coverage.

`SecondMomentPairCap.finite_bound` splits actual ordered pairs into
zero-full-loss pairs and the actual full-loss hosts. The zero-loss
contribution is at most N^2*(2^(-L))^2, with actual affine deficiencies
handled by the proved zero-loss implication. The remaining contribution
is at most the actual host cardinality times a bound for actual distinct
pair joint probabilities. This is an unconditional finite theorem;
the asymptotic pair cap is discharged in the next step, not assumed
as a completed conclusion.

The proved host bound with epsilon=1/8 and the conditional pair joint
bound with epsilon=1/8 give an exceptional contribution at most

    N^(1+1/8)*N^(-3/2+1/8) = N^(-1/4) <= 1.

The nominal critical mean is at most2^C. Consequently
`BoundedSecondMomentUnderBCN.uniform_bound` proves the explicit actual
seed F_2<=(2^C)^2+1, uniformly before every critical length. This does
not assert that actual heterogeneous marginals equal the nominal one.
No weighted residual estimate, bounded pair moment, independence
premise or fixed-order extrapolation is supplied as an input.

`OrderDependentMomentsUnderBCN.uniform_source_growth` combines this
seed with the existing actual recurrence and absorbs its fixed
constant into the exponential, obtaining

    F_k <= exp((k-2)*H/2 + K_C*(k*h+k^(3/2)*H/h))

simultaneously for every2<=k<=H, where H=logN and h=logH. The positive
K_C is chosen before the BCN constants c,kappa; these affect only the
eventual threshold. The absorption uses h>=1 and the actual order
range, with all real powers and denominator signs proved. This
implies the source statement, including its allowed fixed prefactor.

The external BCN proof and its geometric-to-plane-polynomial
presentation remain unformalized. T19.4 is therefore conditional,
with exactly the same named BCN input, and remains outside proved
coverage77/167 (main28/73, companion49/94). No additional external
input or new mathematical finding is introduced. P1-MATH-0030 retains
the unconditional smaller exception improvement. Confirmed findings83.
No Paper C port, manuscript-byte change or Palomar registration.

Lean v4.36.0-rc2 full build passed (10587 jobs); actual axiom audit passed for all 6074 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 3791 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records remain intact. Ubuntu available space: 15.81 GiB. The bounded actual seed F_2<=(2^C)^2+1 and complete T19.4 growing-order source conclusion are proved under the existing single field-polynomial BCN input. The positive exponential constant precedes the BCN constants; those affect only the threshold. Finite branching and its smaller exception remain unconditional. T19.4 is conditional and adds no proved coverage. Coverage77/167 (main28/73, companion49/94); confirmed findings83. No additional unformalized input, Paper C port, dependency download, manuscript-byte change or Palomar registration.


## Actual finite Poisson–Charlier conversion without a convolution logarithm

The full analytic finite conversion is now proved for actual atomic
signed measures. Finite signed laws carry their ordinary l1 ring norm;
its nondegeneracy and exact scalar behavior are proved. Their completion
is a real Banach algebra. Singleton evaluation extends continuously,
and every completed element has an absolutely summable coefficient
sequence whose ordinary l1 sum is bounded by its completion norm.
Consequently all norm estimates below control genuine actual signed
measures, including their infinite tails.

The convolution exponential exp(mu*Delta) is proved coefficientwise
equal to the actual Poisson mass exp(-mu)*mu^k/k!. Its positivity and
probability interpretation are proved for mu>=0. Convolution byDelta
is actual translation minus the identity; convolution byDelta^2 gives
the literal second difference. The completed quadratic reference is
proved equal to the existing actual signed-measure Q(mu,alpha).

For every elementv of a real Banach algebra, absolute exponential
series prove a Taylor tail at every order, with no small-norm premise.
Finite-product perturbation and actual quadratic cancellation give

    ||(1+v)^n-exp(v)^n+(n/2)*v^2*exp(v)^n||
      <= (2n||v||^3+n^2||v||^4)*exp((n+2)||v||).

No convolution logarithm is used. For every integern>=2,0<=p<=1,
np<=A and arbitrary realbeta,c2, write mu=np and alpha=2c2-np^2.
The actual finite reference b^n+beta*Delta^2*b^(n-2) satisfies

    ||reference-Q(mu,alpha)||_1
      <=4|beta-c2|
        +16exp(2A+4)*(np^3+(np^2)^2)
        +16exp(2A+2)*|c2|*(p+np^2).

Both finite binomial expansions in the source proof, the deletion of
two Bernoulli factors, the exact quadratic coefficient and the
beta-replacement cost are proved. The source restriction2p<1 is
unnecessary for this analytic step; the valid finite scope is0<=p<=1.

The critical mean and p<=2^C/N are proved inputs, not assumptions.
An explicit positive errorConstant(C), chosen before everyN,L,n,beta,
c2, yields

    ||reference-Q||_1
      <=4|beta-c2|+K_C*(N^(-2)+|c2|/N)

for everyN>=2,2<=n<=N and critical-bandL. The actual regular-set
cardinality is proved eventually at least2 under one uniform
threshold. Thus the same estimate holds for the literal actual
RetainedReferenceTheorem.binomialReference, with its actual good-edge
joint-moment sum beta. All measures and the ordinary sum of absolute
singleton differences are included.

The arithmetic bound C_2=O(a_N) used in the source is not yet proved.
No such bound is assumed or counted as completion: T17.4 is in progress,
with exactly this remaining obligation. Proved coverage remains77/167
(main28/73, companion49/94). P1-MATH-0084 records the logarithm-free
finite extension; confirmed findings84. No external mathematical input,
BCN argument, Paper C port, dependency download, manuscript-byte change
or Palomar registration is added.

Lean v4.36.0-rc2 full build passed (10619 jobs); actual axiom audit passed for all 6130 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 3847 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records remain intact. Ubuntu available space: 15.83 GiB. Actual finite-law l1 completion, summable singleton coefficients, exact Poisson exponential and quadratic signed-measure identification, unrestricted Banach exponential Taylor bounds, finite-product perturbation and explicit finite Poisson–Charlier conversion are proved. The actual regular-set reference has uniform error4|beta-c2|+K_C*(N^(-2)+|c2|/N), with no2p<1 premise. The arithmetic covariance scale C_2=O(a_N) remains open; T17.4 is in progress and adds no proved coverage. Coverage77/167 (main28/73, companion49/94); confirmed findings84. No external mathematical input, BCN premise, Paper C port, dependency download, manuscript-byte change or Palomar registration.


## Heterogeneous conversion with actual mean and second cumulant

The full finite analytic statement of main15.1 is now proved for
actual signed measures, with the explicit constant C_M=16exp(2M).
The restriction p_*<=1/4 is unnecessary for this step: every actual
Bernoulli marginal in0<=p_i<=1 is allowed. A nonnegative P only needs
to dominate the marginals; it need not be small. Pair weights may have
either sign, and any selected family of two-element subsets is allowed.
No independence or covariance-sign assumption is used.

The new generic real Banach-algebra estimate is

    ||prod(1+v_i)-prod exp(v_i)
       +(sum v_i^2/2)*prod exp(v_i)||
    <=(2*sum||v_i||^3+(sum||v_i||^2)^2)*exp(sum||v_i||).

It follows by exact insertion identities, absolute exponential Taylor
tails and finite-product norm bounds. There is no logarithm or
small-norm restriction. The first-order estimate and deletion of any
actual two Bernoulli factors are also proved. Exact exponential sums,
scalar sums and pair corrections identify the resulting reference with
the actual Poisson–Charlier signed measure.

Writing mu=sum p_i, s_j=sum p_i^j, C_2=sum c(e),
A_2=sum|c(e)| and alpha=2C_2-s_2, the full finite bound is

    ||B_2-Q(mu,alpha)||_1
      <=16exp(2M)*(s_3+s_2^2+A_2*(s_2+P)),

whenever mu<=M. The actual ordinary sum of absolute singleton masses
is bounded, including its infinite tail. All covariances retain their
signs before taking this final norm, including incompatible pairs.
The exact finite reference and its completed-algebra image are proved
equal; no coefficient, convolution or tail identity is assumed.

The actual original-run specialization uses exact infinite-model
Bochner marginals and centered pair coefficients on every deterministic
subset G of the dyadic block. The exact identity

    secondFactorialCumulant(G)=2*sum c(e)-sum p_x^2

is proved from actual factorial moments, the finite subset formula and
the full square expansion. Thus the signed reference uses the actual
count mean and actual variance-minus-mean parameter, with its diagonal
term retained.

All actual marginals are proved in[0,1]. The already proved critical
local cap gives p_x<=2^(C+1)/N; its sum gives the actual mean bound,
and every power-sum substitution is proved. One threshold before all
critical lengths and all deterministic subsets gives

    ||B_2-Q(actual mean,actual second cumulant)||_1
      <=K_C*(N^(-2)+A_2/N).

This applies in particular to the full admissible set, with no
zero-marginal replacement or local-independence assumption. The
remaining source application requires A_2=O(N^(-2/3+epsilon)). That
arithmetic estimate remains open and is not supplied as a hypothesis
or counted as proved. Main15.1 is in progress for that final numerical
rate. Coverage remains77/167 (main28/73, companion49/94).

This extends P1-MATH-0084 to heterogeneous marginals without adding a
separate finding: confirmed findings84. No external mathematical
input, BCN premise, Paper C port, dependency download, manuscript-byte
change or Palomar registration is introduced.

Lean v4.36.0-rc2 full build passed (10631 jobs); actual axiom audit passed for all 6169 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 3886 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records remain intact. Ubuntu available space: 15.81 GiB. The full finite heterogeneous conversion is proved with C_M=16exp(2M) for every true marginal in[0,1], with arbitrary signed pair weights. Actual infinite-model means, centered pair coefficients and the exact second factorial cumulant with its diagonal correction are identified. A uniform actual bound K_C*(N^(-2)+A_2/N) holds before every critical length and deterministic dyadic subset. The source numerical rate remains open for the arithmetic pair-activity estimate; main15.1 is in progress. Coverage77/167 (main28/73, companion49/94); confirmed findings84, extending P1-MATH-0084 without a new finding. No external mathematical input, BCN premise, Paper C port, dependency download, manuscript-byte change or Palomar registration.


## Exact integer mean bias and an actual finite nonzero criterion

The exact integer identity and quantum in main17.3 are now proved
for everyN>=2 and positive lengthL, without a critical-band assumption.
The more general finite statement holds for every deterministic subsetG
of the dyadic block, with nominal mean#G*2^(-L).

`deficiency` is exactly L minus the actual square-class rank, proved
nonnegative. `localMultiplicity` is zero when the actual infinite
marginal vanishes and otherwise2^deficiency. Its equality with the
source compatibility indicator times2^deficiency is proved through the
actual finite affine system. The actual Bochner marginal is exactly
2^(-L) times this natural multiplicity; rank truncation and every cast
are justified. Thus the actual count mean minus the nominal mean is
exactly2^(-L) times an actual finite sum of integer coefficients.
No heterogeneous marginal is replaced by a nominal one.

The mean equals the nominal mean if and only if the integer bias is
zero. Every nonzero bias has absolute value at least2^(-L), with the
explicit critical lower constant (2^C)^(-1)/N. This includes both signs
and makes no assertion of infinitely many nonzero scales.

The proved critical one-window rank theorem gives deficiency at most1
under one threshold before every length. Define actual zero windows
by marginal0 and actual double windows by marginal2*2^(-L). Their
identification with local multiplicities0 and2 is proved. They are
disjoint and partition the irregular set. Regular windows have
multiplicity1. Consequently the literal integer bias satisfies

    M = #double - #zero = 2*#double - #irregular,
    |M| <= #irregular,
    M mod2 = #irregular mod2.

An odd irregular cardinality therefore forces a nonzero mean bias at
that scale. Both the finite criterion and its uniform critical version
are proved. P1-MATH-0085 records this exact signed classification and
parity criterion. It does not claim odd cardinalities or nonzero biases
at infinitely many scales.

The analytic reference comparison is also proved independently:
if0<=mu,nu<=M and alpha>=-1, then

    ||Q(mu,alpha)-Q(nu,alpha)||_1
      >=exp(-M)/2*|mu-nu|.

It uses the actual signed measures and their zero singleton mass;
the exponential difference and all infinite sums are justified. The
parameter assumptions are explicit and are not counted as an actual
law approximation. The remaining conclusions of main17.3 concern
the true count law and require the still-open approximation theorem.
The result is in progress and adds no proved numbered coverage.

Coverage77/167 (main28/73, companion49/94), confirmed findings85.
No new external mathematical input, BCN premise, Paper C port,
dependency download, manuscript-byte change or Palomar registration.

Lean v4.36.0-rc2 full build passed (10637 jobs); actual axiom audit passed for all 6201 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 3918 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records remain intact. Ubuntu available space: 15.80 GiB. Exact finite integer mean quantization, source affine compatibility, the nonzero quantum, critical signed zero/double-window classification, parity and the odd-irregular-count criterion are proved. Actual quadratic signed references have explicit mean-separation lower bound exp(-M)/2 for0<=mu,nu<=M andalpha>=-1. No infinitely-many-scales or true-count law approximation is claimed. Main17.3 remains in progress for its true-law distance conclusions. Coverage77/167 (main28/73, companion49/94); confirmed findings85. No new external mathematical input, BCN premise, Paper C port, dependency download, manuscript-byte change or Palomar registration.


## Actual independent Poisson jumps and explicit Hermite error

The actual probabilistic and analytic reference step of main19.1
is now proved. General jump-Poisson exponentials exp(b*(delta_j-delta_0))
have absolutely convergent series of actual atomic masses. Their
singleton coefficients are proved to be the pushforward of the actual
Poisson masses by n->j*n, for every naturalj including0. They define
actual probability measures for b>=0 and have completion norm exactly1.
The ordinary Poisson exponential consequently has norm exactly1 too.

The general compound reference pi_a*jumpPoisson(j,b) is proved equal
to the actual law of U+jV, where U,V are the coordinate maps on the
actual product of Poisson measures of meansa,b. Both coordinate laws,
their independence, every actual product singleton and the full
pushforward count law are proved. All series products, coefficient
transport, normalization and infinite tails are justified; none is
supplied as an input.

For0<=alpha<=mu, the Hermite reference is the actual probability law
of U+2V with independent meansmu-alpha andalpha/2, including both zero
parameter endpoints. Its completed reference factors exactly as

    H(mu,alpha)=pi_mu*exp((alpha/2)*Delta^2).

The exact source quadratic reference is identified as an actual signed
measure, and absolute Taylor tails give the explicit bound

    ||H(mu,alpha)-Q(mu,alpha)||_1<=4alpha^2 exp(2alpha).

The completed algebra inequality also holds for any realalpha when
mu>=0, with exp(2|alpha|); the probability interpretation requires
the stated nonnegative Poisson means. No small-alpha or upper-mean
assumption is used in this finite comparison. For every actual
probability lawP, a proved finite transfer gives

    TV(P,H)<=||P-Q||_1/2+2alpha^2 exp(2alpha).

No bound for ||P-Q|| is assumed or counted as a count-law approximation.

Actual exponential sums and Bochner integrals are also proved. The
general compound law has mean a+j*b and exponential moment

    exp(a*(exp(t)-1)+b*(exp(j*t)-1))

for every realt. The Hermite law has actual meanmu and exponential
moment exp(mu*(exp(t)-1)+(alpha/2)*(exp(t)-1)^2). Integrability is
proved before using each actual Bochner integral. These properties
concern the constructed reference, not the original run count.

The actual/truncated parameter admissibility at largeN, the numerical
law approximation, and the fixed-height hierarchy rates and leading
equivalents in main19.1 remain open. No matching lower bound for the
exact-parameter Hermite error is asserted. The source row is in
progress and adds no proved numbered coverage. Coverage77/167
(main28/73, companion49/94); confirmed findings remain85.
No new mathematical finding, external input, BCN premise, Paper C
port, dependency download, manuscript-byte change or Palomar
registration is introduced.

Lean v4.36.0-rc2 full build passed (10647 jobs); actual axiom audit passed for all 6238 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 3955 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records remain intact. Ubuntu available space: 15.78 GiB. Actual independent Poisson product coordinates, all natural jump sizes, absolutely convergent atomic series, exact coefficient pushforwards and norm-one probability exponentials are proved. The actual Hermite law has meanmu, every real exponential moment, factorization pi_mu*exp(alpha*Delta^2/2), explicit ordinary l1 error4alpha^2 exp(2alpha) and a finite TV transfer for any probability law. Integrability precedes all actual Bochner integrals. Eventual admissibility of model/truncated parameters and the source count-law rates remain open; main19.1 is in progress. Coverage77/167 (main28/73, companion49/94); confirmed findings85. No new finding, external input, BCN premise, Paper C port, dependency download, manuscript-byte change or Palomar registration.


## Universal analytic conversion without a mean bound

A further strengthening of the finite analytic conversion is proved:
the constant is universal, C=16exp(2), with no upper bound on the total
mean. For arbitrary finite Bernoulli marginals0<=p_i<=1, arbitrary
signed weights on selected two-element subsets, and any nonnegative
upper marginal capP,

    ||B_2-Q(mu,2C_2-s_2)||_1
      <=16exp(2)*(s_3+s_2^2+A_2*(s_2+P)).

No mean bound mu<=M or small-marginal condition is required. The actual
Bernoulli convolution factors and actual Poisson factors are proved to
have normone. Their finite products are contractions. Exact insertion
identities and absolute exponential tails then need only the local
increment cap ||p_i*Delta||<=2, rather than a bound involving their sum.
Every contraction premise of the generic algebra lemma is discharged
for the actual probability factors; the target conversion is not an
input. All actual signed singleton masses and infinite tails remain
controlled by the ordinary l1 norm.

The universal inequality is instantiated on actual original-run
Bochner marginals and centered pair coefficients, with the actual count
mean and exact variance-minus-mean parameter. The full diagonal term
and all covariance signs are retained. It holds for every deterministic
dyadic subset, with no mean-cap argument and no asymptotic premise.

The homogeneous specialization is proved too. For every integern>=2,
0<=p<=1 and arbitrary realbeta,c2, the actual finite binomial pair
reference satisfies

    ||reference-Q(np,2c2-np^2)||_1
      <=4|beta-c2|+16exp(2)*
          (np^3+(np^2)^2+|c2|*(np^2+p)).

No upper bound onnp is assumed. A selected single pair in the full
finite heterogeneous theorem gives the exact covariance-reference
bound; the beta replacement has its proved cost4|beta-c2|. The source
natural subtractionn-2, omitted-product cardinality and all finite
products/sums are checked.

P1-MATH-0084 records the earlier removal of the logarithm and small-p
restriction. New P1-MATH-0086 records the independent removal of the
bounded-mean premise and the universal constant. This changes no
asymptotic exponent. Main15.1 remains in progress for the arithmetic
pair-activity rate A_2=O(N^(-2/3+epsilon)); companionT17.4 remains in
progress for C_2=O(a_N). Neither bound is assumed or counted proved.
Coverage77/167 (main28/73, companion49/94), confirmed findings86.
No external mathematical input, BCN premise, Paper C port, dependency
download, manuscript-byte change or Palomar registration is added.

Lean v4.36.0-rc2 full build passed (10655 jobs); actual axiom audit passed for all 6254 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 3971 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records remain intact. Ubuntu available space: 15.77 GiB. The universal constant16exp(2) is proved for the actual finite heterogeneous Poisson–Charlier conversion, with no bounded-mean argument and every true Bernoulli marginal in[0,1]. Every contraction premise is discharged for actual probability factors. Actual original-run means, signed covariances and exact second cumulants are retained. The homogeneous binomial pair conversion has the same universal constant with no bound onnp. Arithmetic pair-activity and covariance scales remain open; main15.1 and companionT17.4 are in progress and add no proved coverage. Coverage77/167 (main28/73, companion49/94); confirmed findings86. No new external input, BCN premise, Paper C port, dependency download, manuscript-byte change or Palomar registration.


## Finite reciprocal-pivot arithmetic and dyadic transfer

The finite arithmetic reduction of companionT19.15 is proved for the
actual largest prime with odd valuation, including the prime2. Its
value on a square is1. The cutoff predicate agrees exactly with the
existing intrinsic defect predicate. The pivot is at most the actual
largest prime factor, and equals the largest prime factor of the
canonical squarefree kernel for every positive integer.

The canonical square-part map is proved injective and lands in the
actual finite domain a>=1, a<=sqrt(X), 1<=v<=floor(X/a^2). Positive
summation therefore proves, with literal natural floors,

    S_plus(X)<=S_kappa(X)<=sum_{1<=a<=sqrt(X)} S_plus(floor(X/a^2)).

No squarefree counting estimate or multiplicity bound is assumed.
For every integer cutoffA>=1, the actual a>A contribution is at most
2X/A, by a proved reciprocal-power tail. Thus the finite small-a sum
plus2X/A bounds the actual reciprocal-pivot sum.

The exact dyadic transfer is also proved. Multiplication by any power
of2 preserves every actual pivot greater than2. The least doubling
exponent sends each 1<=n<=N into [N,2N), and is bounded by
Nat.clog2N. The pair (exponent,image) is injective. Actual finite
positive sums give, for everyN>=1,

    S_kappa(N)<=2*(floor(sqrt(N))+1)+(Nat.clog2N+1)*D_kappa(N),
    D_kappa(N)<=S_kappa(2N).

The first term is proved by the existing defect representation count
at cutoff2. No dyadic preimage count, square-part injection, pivot
invariance or small-pivot estimate is supplied as a premise.

These finite statements prepare the exact asymptotic ofT19.15.
The cited Erdos--Ivic--Pomerance ordinary reciprocal-prime asymptotic,
the explicit saddle scales, their uniform comparison on the small-a
range and the final logarithmic equivalents remain unformalized.
T19.15 is in progress, not proved or conditionally complete.
Coverage77/167 (main28/73, companion49/94), findings86 unchanged.
The PaperC port is limited to the pivot definition, positive lower
bound, cutoff equivalence and pivot population definition at the
recorded immutable commit/blob; its unproved analytic interfaces are
not imported. All other reduction, injection, tail and dyadic proofs
are new P1 code. No new external mathematical argument, dependency
download, source-byte change or Palomar registration is introduced.

Lean v4.36.0-rc2 full build passed (10663 jobs); actual axiom audit passed for all 6289 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 4006 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records remain intact. Ubuntu available space: 15.74 GiB. Actual reciprocal-pivot comparison, canonical square-part injection, literal finite sum reduction, the2X/A tail and logarithmic-preimage dyadic transfer are proved with no analytic premise. The exact Erdos--Ivic--Pomerance and uniform saddle asymptotics remain open; T19.15 is in progress. Coverage77/167 (main28/73, companion49/94); confirmed findings86. Only the exactly attributed elementary pivot fragments are ported from PaperC; no old analytic assumption or binary is imported. No new external mathematical input, dependency download, source-byte change or Palomar registration.


## Coarse actual pair activity and cumulant decay under the common BCN input

The literal actual absolute pair mass A2 now has an unconditional finite
host reduction. The exact factor2 from unordered pairs to ordered tuples
is proved. Zero full pair loss forces zero covariance, including every
actual affine compatibility case. An injective tuple-to-host map gives

    2*A2(full)<=#full_loss_hosts*M+actual_host_independent_mass

wheneverM bounds actual joint masses of distinct pairs. The independent
term retains the actual heterogeneous products p_x*p_y. Every smaller
deterministic ground set has no greater absolute pair mass.

Under precisely the same explicit field-polynomial BCN argument already
used for main13.5,13.6,13.8, the checked actual host count N^(1+epsilon)
and actual pair cap N^(-3/2+epsilon) imply, uniformly before every
critical length and every deterministic dyadic subsetG,

    A2(G)<=N^(-1/2+epsilon),
    ||B2(G)-Q(actual_mean,actual_second_cumulant)||_1<=N^(-3/2+epsilon).

These are coarse rates. They do not supply the stronger manuscript
A2=O(N^(-2/3+epsilon)) or the optimal conversion exponent5/3, and they
do not compare the original count law with the retained reference.

The exact second factorial cumulant, including its negative diagonal
term, satisfies |alpha(G)|<=2*A2(G)+sum p_x^2. Its actual diagonal is
bounded byK^2/N using the proved critical marginal cap. The same BCN
argument therefore gives |alpha(G)|<=N^(-1/2+epsilon), and hence a
uniform eventually-small statement with the threshold beforeL andG.
No cumulant or activity bound is supplied as a premise of these rates.

Independently of BCN, the actual full count mean satisfies eventually

    (2^C)^(-1)/2<=mu<=2*2^C.

The lower bound uses the actual regular population, whose size is at
leastN/2, and its actual nominal marginal; the upper bound uses the
proved actual marginal cap. Under BCN this gives |alpha|<=mu/2 and
alpha<mu uniformly in the critical band. Nonnegativity ofalpha is NOT
proved here, so the remaining Hermite admissibility condition remains
open, as do the original and explicit-parameter approximation rates.

Main15.1 and19.1 remain in progress. Neither this weaker conversion nor
a partial parameter gap adds proved numbered coverage. Coverage77/167
(main28/73, companion49/94), confirmed findings86 unchanged. The only
unformalized input is the existing ordinary BCN argument, explicitly
passed at every dependent theorem. The finite host identities and the
mean bounds are unconditional. No new external estimate, PaperC port,
dependency download, manuscript-byte change or Palomar registration.

Lean v4.36.0-rc2 full build passed (10671 jobs); actual axiom audit passed for all 6305 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 4022 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records remain intact. Ubuntu available space: 15.73 GiB. The exact finite2A2 host reduction and unconditional actual two-sided mean bounds are proved. Under the same explicit unformalized BCN argument, actual pair activity and actual second cumulants are at mostN^(-1/2+epsilon), actual conversion is at mostN^(-3/2+epsilon), and the upper parameter gap |alpha|<=mu/2 holds uniformly. No target activity, covariance or cumulant rate is assumed. Positivity ofalpha and the sharper source rates remain open; main15.1 and19.1 are in progress. Coverage77/167 (main28/73, companion49/94); confirmed findings86. No new external input, PaperC port, dependency download, manuscript-byte change or Palomar registration.


## Unconditional positive cumulant and actual probability parameters

The actual second factorial cumulant is now proved eventually positive
without any unformalized analytic or geometric input. A finite identity
on actual distinct full-loss hosts shows that, for every selected
ordered host populationF,

    alpha>=sum_{(x,y) in F} actual_q_xy-actual_host_independent_mass-sum p_x^2.

The exact ordered/unordered multiplicity2 is proved for arbitrary
weights by a finite tuple/pair bijection. Zero full loss gives zero
actual covariance. Summation on all distinct hosts then gives the
selected-joint lower bound; no sign of a covariance is assumed.

Every private fixed-channel source is proved to be a distinct full-loss
host by its actual normalized-union rank and exact overlap cardinality.
Apply the finite bound to the actual ordered2:3 channel with cutoff6B.
Its already proved positive phase gives c_C*L*N^(-2/3). The actual host
independent mass is at mostN^(-5/6), and the actual marginal diagonal is
at mostK_C^2/N. These errors are absorbed uniformly. Thus, for a positive
constantd_C and one threshold before all critical lengths,

    alpha_N>=d_C*L*N^(-2/3)>0.

This lower bound and positivity are unconditional Lean theorems. They
do not use BCN, the complete pair profile, other channel estimates,
the count-law approximation or the asymptotic equivalent foralpha.
P1-MATH-0087 records this simpler positivity route and its input scope.
It supplies no new sharp exponent or leading equivalent.

The actual mean also has the explicit unconditional bias estimate

    |mu_N-N*2^(-L)|<=2^C*N^(-1+epsilon).

The previously proved actual mean interval m_C<=mu_N<=M_C has
m_C=(2^C)^(-1)/2 andM_C=2*2^C. Under the SAME explicit ordinary BCN
argument as before, the coarse actual cumulant upper bound gives
alpha_N<mu_N and uniform eventual smallness. The actual Hermite
reference with Poisson meansmu_N-alpha_N andalpha_N/2 is therefore
an actual probability law for all sufficiently largeN.

The quadratic reference is also proved to be an actual probability.
A generic sufficient domain derived from its exact integer Charlier
minimum is: if0<m<=mu<=M, alpha>=0 andalpha<=m^2/(M+1), then
Q(mu,alpha) is a probability. All these bounds are discharged for the
actual original-run parameters under the same explicit BCN argument.
No probability status or parameter admissibility is an assumption.

Main1.1 is now in progress for its exact mean-bias clause and its
conditional probability-reference clause. Main3.3 gains the
unconditional positive cumulant lower bound; its full pair profile
and asymptotic equivalents remain open. Main19.1 gains actual
exact-parameter admissibility; its count-law approximation, explicit
fixed-height parameters and optimal hierarchy rates remain open.
All three rows remain in progress. Coverage77/167 (main28/73,
companion49/94), confirmed findings87. No new external mathematical
input, PaperC port, dependency download, source-byte change or
Palomar registration.

Lean v4.36.0-rc2 full build passed (10681 jobs); actual axiom audit passed for all 6330 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 4047 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records remain intact. Ubuntu available space: 15.71 GiB. The actual second cumulant has the unconditional lower bound d_C*L*N^(-2/3)>0, from the actual selected-joint host identity and the private2:3 channel. No BCN, full pair profile, covariance sign or count-law approximation is assumed for this positivity theorem. The actual mean bias has explicit unconditional constant2^C. Actual quadratic and Hermite probability status is proved uniformly under the same existing explicit BCN input for the coarse upper bound. Sharp pair and law rates and explicit fixed-height parameters remain open; main1.1,3.3,19.1 are in progress. Coverage77/167 (main28/73, companion49/94); confirmed findings87. No new external input, PaperC port, dependency download, manuscript-byte change or Palomar registration.


## Unconditional fixed-height explicit probability references

The literal finite-height channel coefficients are now defined with the
source reduced interior numerators b/2<a<b, gcd(a,b)=1, heights3<=b<=h,
and the exact rational weight2*(2a-b)/(ab). The index is(heightb,numeratora).
The finite signed polynomial S_{a,b}(L) is the already checked integer
source sum, including its empty-sum convention. Exact finite grouping
proves the literal source coefficient

    alphaHat_h=lambda^2/N*sum_{b=3..h} sum_a w_ab*S_ab(L).

For every fixedh>=3 and bandC, one threshold precedes allN,L. The actual
finite coefficient satisfies positive two-sided bounds

    d_C*L*N^(-2/3)<=alphaHat_h<=K_(C,h)*L*N^(-2/3),
    alphaHat_h<=N^(-2/3+epsilon) for everyepsilon>0.

Every summand is proved nonnegative in that range, and the included2:3
channel gives the positive lower bound. No pair-profile theorem,
cumulant comparison, BCN or count-law approximation is an input.
The threshold and upper constant may depend onh; no growing-height
uniformity is asserted. A uniform eventually-small statement is proved.

The nominal mean has its exact critical bounds
(2^C)^(-1)<=lambda<=2^C. The generic Charlier sufficient domain and the
actual independent-Poisson construction then prove, UNCONDITIONALLY,
for every fixedh>=3 and all sufficiently largeN in the critical band,

    0<alphaHat_h<lambda,
    Q(lambda,alphaHat_h) is an actual probability,
    H(lambda,alphaHat_h) is an actual probability.

These are the literal source parameters. No parameter positivity,
probability property, comparisonalphaHat_h~alpha or target estimate is
assumed. The height4 coefficient is proved exactly equal to
lambda^2/(3N)*(S_23+S_34). Its actual quadratic singleton masses have
exactly the displayed formula in main1.4, includingk=0,1. The mass
formula itself is a signed-measure identity for everyN>0; probability
status is the eventual statement, not a small-N assertion.

The moving-phase constant c_b(r) is also defined literally. Its finite
sum is strictly positive for everyb>=3, becausea=b-1 is a reduced
interior numerator and every summand is positive. The first constants
are checked exactly:

    c3(r)=(r+2)/(18*2^(r/3)), c4(r)=(r+3)/(24*2^(r/4)),
    c5(r)=17*(r+4)/(300*2^(r/5)), c6(r)=(r+5)/(45*2^(r/6)).

The generic height increment is proved. The height5 increment is the
sourceM5=lambda^2/N*((2/15)*S_35+(3/10)*S_45). ForL=5q+r, q>=1,r<5,
its exact displayed closed polynomial, with coefficients17,13,87,620,
113,127, is checked from the two signed integer channel identities.
No asymptotic equivalent for a distance is inferred from these finite
phase and polynomial identities.

Main1.4,18.1,18.3 are now in progress for their exact finite algebra
and probability-reference clauses. Their count-law and cumulant
remainder estimates, sharp distances, equivalents and optimality are
still open. Main19.1 gains unconditional probability status for every
literal fixed-height explicit Hermite reference; its distance rates
remain open. Finding87 is extended to record this second, entirely
finite route to reference admissibility, without comparison to the
actual cumulant. Coverage77/167 (main28/73, companion49/94), findings87.
No new external mathematical input, BCN argument, PaperC port,
dependency download, manuscript-byte change or Palomar registration.

Lean v4.36.0-rc2 full build passed (10691 jobs); actual axiom audit passed for all 6374 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 4091 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records remain intact. Ubuntu available space: 15.69 GiB. Every literal fixed-height coefficient has direct unconditional positive vanishing bounds, and its actual quadratic and Hermite references are probabilities without BCN, actual-cumulant comparison or count-law approximation. Exact height4 parameters and masses, c_b positivity, phases at heights3..6, generic height increments and the exact height5 polynomial are checked. Sharp count-law and cumulant remainders, distances, equivalents and optimality remain open; main1.4,18.1,18.3,19.1 stay in progress. Coverage77/167 (main28/73, companion49/94); confirmed findings87. Finding87 is extended to the direct explicit-parameter route. No new external input, BCN premise, PaperC port, dependency download, manuscript-byte change or Palomar registration.


## Uniform moving-parameter phase of every fixed finite channel height

The literal finite height contribution now has its complete uniform
leading phase equivalent. For each fixed heightb>=3 and bandC, with
r=L modb andlambda=N*2^(-L), put

    heightMass_b=lambda^2/N*T_b(L),
    phaseMass_b=c_b(r)*lambda^(2-1/b)*L*N^(-1+1/b).

For everyepsilon>0, a threshold precedes allN,L in the critical band:
phaseMass_b>0 and

    |heightMass_b/phaseMass_b-1|<=epsilon,
    |heightMass_b-phaseMass_b|<=epsilon*phaseMass_b.

The moving residue and moving nominal mean are retained. No restriction
to a fixed phase subsequence is imposed. The heightb is fixed before
the threshold; no growing-height uniformity is asserted.

The original integer signed sum has an exact normalized Euclidean
formula atL=bq+r. Division byq*2^q leaves its positive leading
coefficient and only inverse-q and geometric terms. Their actual
limits prove each residue limit for the finite height sum. The actual
finite residue set is then assembled into one common threshold,
followed by Euclidean division for every sufficiently largeL. Critical
window geometry transports that common length threshold to the source
quantifier order beforeN,L.

The conversion to the source N,lambda expression is an exact real-power
identity, usingN/lambda=2^L. The positive nominal prefactor cancels;
it is not frozen or replaced by a constant. All fixed-residue limits,
finite sums, nonzero denominators, positivity and uniform assembly are
proved, not supplied as premises.

This proves the leading equivalent of the finite omitted-height term
appearing in the proof of main18.1, including the finite height5 and
height6 phases used in18.3. It does NOT prove the actual-cumulant
remainder, the count-law remainder, a total-variation equivalent or
optimality. The complete actual pair profile in3.3 remains open too.
All three numbered rows stay in progress. Coverage77/167
(main28/73, companion49/94), confirmed findings87 unchanged.
No new mathematical finding, external estimate, BCN input, PaperC
port, dependency download, source-byte change or Palomar registration.

Lean v4.36.0-rc2 full build passed (10697 jobs); actual axiom audit passed for all 6393 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 4110 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records remain intact. Ubuntu available space: 15.68 GiB. The literal finite height contribution has the full uniform source leading phase equivalent, with moving residue and nominal mean. Exact normalized integer identities, reciprocal/geometric limits, actual finite residue assembly and real-power transport are checked. No fixed-residue subsequence or frozen nominal mean is used in the final theorem. Actual pair-profile, cumulant and law remainders, distance equivalents and optimality remain open; main3.3,18.1,18.3 are in progress. Coverage77/167 (main28/73, companion49/94); confirmed findings87. No new mathematical finding, external estimate, BCN input, PaperC port, dependency download, manuscript-byte change or Palomar registration.


## Explicit Hermite comparison and universal reference-distance stability

The comparison of every literal fixed-height explicit Hermite reference
with its quadratic reference is now proved at the full source analytic
error scale, without any unformalized input. For each fixedh>=3, bandC
and everyepsilon>0, one threshold precedes allN,L and

    ||Q(lambda,alphaHat_h)-H(lambda,alphaHat_h)||_1<=N^(-4/3+epsilon).

The norm is the ordinary infinite sum of actual signed singleton
masses. The completed-algebra norm is only a proved majorant; it is
not substituted for the ordinary measure norm. Every coefficient and
both actual signed measures are identified exactly. The finite bound
4*alpha^2*exp(2*|alpha|), the proved literal coefficient rate and
uniform smallness give the displayed numerical rate. No comparison
with the exact cumulant, BCN or count-law error is assumed.

Actual total variation on the naturals now has checked triangle and
reference-stability inequalities. The signed-measure distance is
identified with exactly2*TV. Actual probability witnesses for the
literal Q andH references therefore satisfy, uniformly for EVERY
actual probability lawP on the naturals,

    |TV(P,Q)-TV(P,H)|<=N^(-4/3+epsilon)/2.

The witnesses and common threshold do not depend onP. In particular
this comparison is available for the actual run-count law, without
asserting either distance is already small.

The actual scalar phase of every omitted heightb>=3 also has a
positive uniform lower bound d_(C,b)*L*N^(-1+1/b), and hence d_(C,b)/N.
It follows that for everyepsilon>0 and fixedh>=3, eventually uniformly
in the critical band and for everyP,

    |TV(P,Q_h)-TV(P,H_h)|<=epsilon*phaseMass_(h+1).

The positive omitted-height phase retains the actual moving residue
and nominal mean. Its lower bound uses the included numeratorb-1,
the actual finite main terms and the previously proved uniform phase
equivalent. The final comparison proves negligibility on this scalar
phase without assuming a leading distance equivalent for either law.

These results complete the explicit-reference analytic comparison in
the proof of main19.1. Its original run-count approximation, the
quadratic hierarchy remainder and leading distance/optimality claims
remain open; the exact-parameter Hermite rate remains open too.
Main19.1 stays in progress, as do main18.1 and18.3. No numbered result
is added: coverage77/167 (main28/73, companion49/94), findings87.
No new mathematical finding, external estimate, BCN argument, PaperC
port, dependency download, manuscript-byte change or Palomar registration.

Lean v4.36.0-rc2 full build passed (10707 jobs); actual axiom audit passed for all 6406 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 4123 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records remain intact. Ubuntu available space: 15.66 GiB. Actual signed explicit quadratic/Hermite error is at mostN^(-4/3+epsilon), unconditionally for every fixed height. Actual probability witnesses have distance-to-P changes bounded by half that error for every probability lawP, with P after the common threshold. The change is negligible on the actual moving first-omitted-height scalar phase, whose positive lower bound is proved. Original-count approximation, distance equivalents and optimality remain open; main18.1,18.3,19.1 remain in progress. Coverage77/167 (main28/73, companion49/94); confirmed findings87. No new mathematical finding, external input, BCN premise, PaperC port, dependency download, manuscript-byte change or Palomar registration.


## Coarse actual triple activity and third cumulant under explicit BCN

A first vanishing estimate for the actual absolute triple activity
and third factorial cumulant is proved under the existing single explicit
field-polynomial BCN input. Set

    g = 1/2 - (2/3)*log(2) > 0.

For every critical-band constantC and epsilon>0, one threshold precedes
allN,L and every actual G contained in the dyadic block. The connected
triple joint mass, full absolute triple activityA3 and absolute third
factorial cumulant are each at mostN^(-g+epsilon). Choosing epsilon=g/2
gives an explicit vanishing power. Zero-marginal sites are included in
the A3 and cumulant bounds; there is no regular-set substitution.

The arithmetic split is exact. For any fixed sourceX, actual aligned
targets have cardinality at most(4D+1)*(L+1)^10, by an injection of each
integer strip into[-R,R] and the actual bounded alignment codes. Thus
the all-pairwise-aligned triple population has cardinality at most
25*|G|*(L+1)^20, uniformly N^(1+epsilon) in the critical band. Its actual
joint mass is at mostN^(-1/2+epsilon) under BCN. Every other connected
triple contains a nonaligned pair. The retained stronger pair-rank
coefficient (2/3)*log2 gives its actual joint cap
N^(-2+(2/3)*log2+epsilon), without compatibility. The connected host
countN^(3/2+epsilon) yields the positive gapg. No dense-triple estimate
is assumed.

For every positive-joint family, the actual compatible-nullity bound
and exact joint formula give |c(I)|<=2^|I|*q(I). Nonzero compatible
triple activity is connected. Every centered coefficient containing
a zero-marginal site is proved zero, by a finite probability argument
that permits zero-weight samples; this gives an exact restriction of
every centered activity sum to the positive-marginal ground set.

The literal independent-target deficit has the coarse numerical bound
D_(2,1)<=N^(-1+epsilon) under BCN. On the positive-marginal ground set,
the actual incompatible triple activity is at mostN^(-1+epsilon),
including both signs. Both A3-K3+ and |kappa3-6K3+| have the same coarse
bound; the first difference is nonnegative. All repeated-index terms
are retained, and their absolute cost is separately at most
N^(-3/2+epsilon). These are consequences of the proved coarse A2
estimate and actual marginal caps, not target-bound hypotheses.

Every displayed estimate has the uniform source quantifier order.
The exponentg is substantially weaker than the source41/30 activity
exponent, and the exponent1 deficit/comparison rate is weaker than
the source3/2. Main11.1,11.2,11.3,14.1 and14.6 remain in progress;
14.1 also lacks its lower bound and optimality. Main13.8 remains
conditional on BCN itself. No numbered completion is added:
coverage77/167 (main28/73, companion49/94), findings87 unchanged.
The existing finding82 is extended only with the analytic probability
consequence of its retained stronger nonaligned rank coefficient.
No new external input, PaperC port, dependency download, manuscript-byte
change or Palomar registration is introduced.

Lean v4.36.0-rc2 full build passed (10731 jobs); actual axiom audit passed for all 6448 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 4165 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records remain intact. Ubuntu available space: 15.62 GiB. Under the existing single explicit BCN input, actual connected triple joint mass, full A3 and absolute third factorial cumulant are at most N^(-g+epsilon), g=1/2-(2/3)log2>0. All-aligned target counting is unconditional; the stronger nonaligned actual probability cap retains the strict rank gap. Zero-marginal centered coefficients vanish exactly, so the full A3 and cumulant include all actual dyadic starts. The literal deficit and positive-ground incompatible/comparison costs have coarse exponent1; repeated-index cost has exponent3/2. Source sharp exponents and optimality remain open; no numbered completion is added. Coverage77/167 (main28/73, companion49/94), confirmed findings87. Finding82 is extended only with its stronger probability consequence. No new external input, PaperC port, dependency download, manuscript-byte change or Palomar registration.


## Universal parameter stability and the actual-to-nominal mean change

The finite analytic mean-change step used in main1.4 and the fixed-height
hierarchy is now checked for actual signed measures. For nonnegative
meansmu,nu and arbitrary realalpha,beta,

    ||Pi_mu-Pi_nu||_1 <= 2*|mu-nu|,
    ||Q(mu,alpha)-Q(nu,beta)||_1
      <= 2*(1+2*|alpha|)*|mu-nu| + 2*|alpha-beta|.

The same bounds hold first in the completed convolution algebra and
are transported coefficient by coefficient to the ordinary infinite
sum of absolute singleton masses. The Poisson estimate uses its
actual nonnegative series, the explicit bound
||Pi_t-delta_0||<=2*(1-exp(-t))<=2t and the norm-one convolution
semigroup. It needs neither a mean cap nor an exponential loss.
No reference probability or infinite-tail estimate is assumed.

For each fixed coefficient boundA>=0 and epsilon>0, one threshold
precedes everyN,L in the critical band and every |alpha|<=A. Holding
alpha fixed, changing the actual original count mean toN*2^(-L)
costs at mostN^(-1+epsilon). This uses the already proved actual mean
bias estimate and is unconditional. At every sufficiently large scale
where the literal integer mean bias is nonzero, the same signed
reference distance is at leastc_C/N for everyalpha>=-1, with

    c_C = exp(-2*2^C)/(2*2^C) > 0.

Both signs of the mean bias are included. This is a scale-by-scale
conditional lower bound, not an assertion that nonzero biases occur
infinitely often. The coefficient is held fixed in this lower bound;
no lower bound for simultaneous arbitrary parameter changes is claimed.
The true count-law distance in main17.3 remains open.

For every fixed heightb>=3 and epsilon>0, the exact-to-nominal mean
change is at mostepsilon times the actual moving scalar phase at
heightb, uniformly for every boundedalpha. The proof uses the full
positive phase lower boundd*L*N^(-1+1/b) and chooses a mean-bias loss
strictly smaller than1/b. A weaker d/N phase lower bound would not
suffice for this step. Neither the residue nor the nominal mean is
frozen along a subsequence.

For each literal finite channel coefficientalphaHat_h, h>=3, both
Q(actualMean,alphaHat_h) and the corresponding actual Hermite law
are eventually probabilities without BCN or a pair-profile input.
Positive actual mean bounds and direct smallness/positivity of the
finite channel sum establish admissibility. There are actual
probability witnesses for Q(actualMean,alphaHat_h) and
Q(nominalMean,alphaHat_h) whose distances to EVERY probability lawP
differ by at mostepsilon times phaseMass_(h+1). The threshold and
witnesses precedeP, and both references retain the same literal
finite coefficient. No count-law approximation or leading distance
equivalent is assumed or established.

These results complete the analytic mean-replacement step of main1.4
and18.1. Their original count-law and cumulant remainders, leading
distance equivalents and optimality remain open. Main17.3 remains
in progress for its true-law conclusions. No numbered completion is
added: coverage77/167 (main28/73, companion49/94), findings87 unchanged.
Finding85 is extended with its explicit actual-reference quantum.
No new external input, BCN premise, PaperC port, dependency download,
manuscript-byte change or Palomar registration is introduced.

Lean v4.36.0-rc2 full build passed (10737 jobs); actual axiom audit passed for all 6466 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 4183 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records remain intact. Ubuntu available space: 15.61 GiB. Actual Poisson and quadratic signed references have universal parameter Lipschitz bounds, without a mean cap. Holding a bounded quadratic coefficient fixed, exact-to-nominal mean replacement has unconditional cost N^(-1+epsilon), and at every nonzero integer-bias scale has lower bound exp(-2*2^C)/(2*2^C*N) for alpha>=-1. No infinitely-many-scales assertion is made. The change is negligible on the actual moving omitted-height phase for every fixed height, and literal explicit references at the actual mean are eventually probabilities without BCN. Stability holds for every actual probability law P, after the common threshold and witness choices. Original-count approximation, distance equivalents and optimality remain open; main1.4,17.3,18.1 remain in progress. Coverage77/167 (main28/73, companion49/94), confirmed findings87. Finding85 is extended with its actual-reference quantum. No new external input, BCN premise, PaperC port, dependency download, manuscript-byte change or Palomar registration.


## Actual negative Palm deviation after fixed sources

The negative-deviation and source-deletion step in the proof of
companionT2.7 is now proved without BCN, for every source set of any
fixed maximum cardinalityj, not only the selected good channel pairs.
Conditioning uses the actual prescribed source event with positive
joint massq(A). Each actual new conditional probability is precisely
q(A union{z})/q(A); it lies in[0,1] and its probability-event ratio is
identified under the original infinite measure.

With p=2^(-L), define the positive and negative deviations over the
fresh dyadic starts by max(0,conditional-p) and
max(0,p-conditional). The actual retained branching identity gives
conditional=p outside the deterministic badStarts set constructed
from the old raw-value prime pool. Thus, at finiteN,L,

    negativeDeviation <= #badStarts*p.

The complete fixed-j exceptional count and the critical nominal bound
give, for everyepsilon>0, eventually uniformly beforeN,L,A,

    negativeDeviation <= N^(-1/2+epsilon),
    #A*p <= N^(-1+epsilon),
    E[Z_N-#A | all sources inA active] >= lambda-N^(-1/2+epsilon).

The expectation is an actual conditional Bochner integral, not a
formal sum substituted for an unproved conditional law. Finite
indicator integrability and integral linearity identify it with the
sum of actual conditional probabilities over fresh starts. On the
source event all#A source indicators are one, so deleting them is
proved identical to subtracting#A from the full original count.
The exact signed decomposition is

    freshMean=lambda-#A*p+positiveDeviation-negativeDeviation.

The same negative bound holds after any finite nonnegative weighting
of source sets, including division by the actual positive total
weight. One threshold precedes the population and its weights.
Forj=2 this supplies the complete negative error and source-removal
part of the source Palm mean proof, including its actual conditional
expectation and arbitrary good-pair averaging.

The positive excess, its fixed-channel exponenteta_(a:b), the
asymmetric nonaligned pair profile and the resulting two-sided Palm
mean estimate remain open. No positive-excess bound or conditional
mean convergence is assumed or counted proved. CompanionT2.7 moves
from not_started to in_progress, without a numbered completion.
Coverage77/167 (main28/73, companion49/94), findings87 unchanged.
No new mathematical finding, external input, BCN premise, PaperC
port, dependency download, manuscript-byte change or Palomar
registration is introduced.

Lean v4.36.0-rc2 full build passed (10743 jobs); actual axiom audit passed for all 6485 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 4202 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records remain intact. Ubuntu available space: 15.59 GiB. For any fixed maximum source cardinality, actual negative conditional deviation is at mostN^(-1/2+epsilon), source deletion costsN^(-1+epsilon), and the actual conditional expectation of Z_N-#A is at leastlambda-N^(-1/2+epsilon), without BCN. Actual event probability ratios, finite indicator integrability, conditional Bochner mean identities, signed positive/negative decomposition and arbitrary weighted/normalized source averaging are proved. The fixed-channel positive excess and two-sided Palm estimate remain open; T2.7 is in progress. Coverage77/167 (main28/73, companion49/94), confirmed findings87. No new mathematical finding, external input, BCN premise, PaperC port, dependency download, manuscript-byte change or Palomar registration.


## Actual adjacent quadratic/Hermite reference distances

The actual distances between adjacent explicit references now have
their exact coefficient and uniform moving-phase equivalents, without
BCN, an actual-cumulant comparison or any count-law error input.
For every nonnegative common meanmu and arbitrary realalpha,beta,

    ||Q(mu,alpha)-Q(mu,beta)||_1
      = |alpha-beta|/2 * ||Pi_mu*Delta^2||_1.

This is the ordinary sum of absolute singleton masses of actual signed
measures. When the two references are probabilities, their actual
total variation is exactly |alpha-beta|/4 times the same norm.
All coefficients, infinite sums and the factor2 between l1 andTV
are proved, including the zero-mean endpoint of the signed identity.

The exact coefficient increment from heighth to h+1 is the literal
heightMass_(h+1), with no asymptotic substitution. Therefore the
ordinary adjacent-reference distance is exactly

    |heightMass_(h+1)|/2 * ||Pi_lambda*Delta^2||_1.

For each fixedh>=3, define the positive moving leading term

    E_h = phaseMass_(h+1)/2 * ||Pi_lambda*Delta^2||_1.

For everyepsilon>0, one threshold precedes allN,L in the critical band
and |gap_h/E_h-1|<=epsilon. The phase includes the actual residue and
nominal mean, and the Poisson norm is evaluated at that same moving
mean. Its positivity follows from the proved lower bound
||Pi_lambda*Delta^2||_1>=2exp(-lambda). Actual probability witnesses
for the two adjacent quadratic references have TV gap_h/2, hence
the full equivalent E_h/2=phaseMass_(h+1)*norm/4.

Adjacent literal Hermite probabilities have the SAME uniform leading
total-variation equivalent E_h/2. A proved four-law metric stability
inequality bounds the change of the pair distance by the sum of the
two quadratic/Hermite comparison costs. Their checked error is
negligible on E_h: a positive lower bound d_C,h/N for E_h/2 follows
from the phase lower bound and the compact nominal-mean bound.
The comparison uses actual probability witnesses and ordinary signed
singleton errors, not formal generating functions as distributions.

These statements compare two constructed references. They do not
prove a leading distance from the original count to either reference,
a count-law remainder, an actual-cumulant remainder or optimality.
Those parts of main18.1,18.3,19.1 remain open and all three rows stay
in progress. No numbered completion is added: coverage77/167
(main28/73, companion49/94), findings87 unchanged. No new mathematical
finding, external input, BCN premise, PaperC port, dependency download,
manuscript-byte change or Palomar registration is introduced.

Lean v4.36.0-rc2 full build passed (10749 jobs); actual axiom audit passed for all 6496 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 4213 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records remain intact. Ubuntu available space: 15.58 GiB. The ordinary same-mean quadratic signed distance is exactly|alpha-beta|*norm(Pi_mu*Delta^2)/2, including mu=0, and actual probability TV is half that. Literal adjacent-height quadratic references have the complete uniform moving-phase equivalent with exact coefficient increment, and adjacent Hermite probabilities have the same leading TV. Actual probability witnesses, signed singleton errors, four-law metric stability, positive leading lower bounds and all factors2 and4 are checked. These are reference-to-reference distances; original-count distance equivalents, cumulant/law remainders and optimality remain open. Main18.1,18.3,19.1 remain in progress. Coverage77/167 (main28/73, companion49/94), confirmed findings87 unchanged. No new mathematical finding, external input, BCN premise, PaperC port, dependency download, manuscript-byte change or Palomar registration.


## Actual direct-maximum envelope with all-order tails and moments

The complete actual direct-maximum envelope used in the proof of
companionT19.3 is now constructed and bounded, unconditionally and
at every order. For any deterministic regular ground setG, letR be
the maximum cardinality of an active subfamily whose actual effective
square-class spaces have zero relative nullity. The maximum is an
actual random variable under the original infinite prime signs;
a maximizing family is proved to exist and R<=Z_G pointwise.
Its value is transported exactly through a concrete finite cylinder.
Every real observable ofR is integrable, and its Bochner expectation
equals the explicit finite probability sum. Tail probabilities are
identified as actual event probabilities too.

The finite counting principle is proved for any hereditary family
containing the empty set. Allr-subsets of a maximizing active member
remain admissible and active. Thus choose(R,r) is bounded pointwise
by the number of active admissible r-subsets. Taking actual finite
expectations gives the sum of their actual joint probabilities.
For actual direct regular windows, the already proved joint formula
is exactlyp^|I|, p=2^(-L), and is supplied as a checked equality.
It is not an arithmetic estimate or an assumed target moment bound.

Writingn=|G| andmu=np, which is proved equal to the actual count mean
onG, the following hold for everyN>=2, L>0, everyr>=0 and everys>=1:

    E choose(R,r) <= choose(n,r)*p^r <= mu^r/r!,
    E (R)_r <= mu^r,
    P(R>=r) <= mu^r/r!,
    E s^R <= (1+p*(s-1))^n <= exp((s-1)*mu).

The exponential estimate is proved by the full finite subset
generator of the actual maximizing member. No independence of the
random maximum, stochastic binomial domination or unproved moment
generating-function identity is assumed.

The actual shifted envelopeV=R+1 consequently satisfies, for allk>=1,
r>=1 ands>=1,

    P(V>=k) <= mu^(k-1)/(k-1)!,
    E (V)_r <= mu^r+r*mu^(r-1),
    E s^V <= s*(1+p*(s-1))^n <= s*exp((s-1)*mu).

The exact falling-factorial shift retains its repeated-index term.
The empty ground set, zero mean and orders beyond the ground size
are included. These are finite all-order inequalities; no fixed-order
asymptotic theorem is used uniformly at growing order and no BCN
input or limiting argument is needed.

These statements concernR and its envelopeV, not a bound of the full
original count byV. The paper's modified count, its structural
domination outside the specified exceptional event and the numerical
exceptional-event/coupling error still require the open core estimates.
They are not assumed or counted proved. CompanionT19.3 moves from
not_started to in_progress for those remaining parts.
No numbered completion is added: coverage77/167 (main28/73,
companion49/94), findings87 unchanged. No new mathematical finding,
external input, BCN premise, PaperC port, dependency download,
manuscript-byte change or Palomar registration is introduced.

Lean v4.36.0-rc2 full build passed (10755 jobs); actual axiom audit passed for all 6534 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 4251 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records remain intact. Ubuntu available space: 15.56 GiB. The maximum actual direct active subfamily is constructed, attained and bounded by the original regular count. Every real observable is integrable and transported exactly to a concrete finite cylinder. Actual direct regular-window joint equalities prove binomial/Poisson choose/factorial bounds, actual tail probabilities and binomial/exponential moment bounds at every order, for every N>=2,L>0. The shifted maximum has all source envelope inequalities, retaining the falling-factorial repeated-index term. No fixed-order theorem is used at growing order and no BCN or numerical probability estimate is assumed. The specified modified original count, structural domination and exceptional-event/coupling estimate remain open; T19.3 is in progress. Coverage77/167 (main28/73, companion49/94), confirmed findings87 unchanged. No new mathematical finding, external input, PaperC port, dependency download, manuscript-byte change or Palomar registration.


## All-order direct envelope with the actual heterogeneous mean

Regularity is unnecessary for the actual direct-maximum moment
envelope. The same constructedR andV=R+1 now have every-order
Poisson-type bounds on ANY finite actual ground setG, using

    p_x = actual infinite marginal atx,
    mu = sum_(x inG) p_x.

The displayed mu is proved equal to the actual original count mean
for every dyadic ground subset. No nominal substitution is used.
The statements require onlyL>0; there is no critical band, BCN input,
positive-local-marginal requirement or regularity assumption.

The actual direct-family joint identity is proved in full scope:

    rho(I)=0 => q(I)=product_(x inI) p_x.

If all local marginals are positive, the existing direct Fourier
identity applies. If one marginal is zero, its singleton joint bound
forces the whole joint mass zero, and the product has that zero
factor. The empty family is included. Thus even local impossibility
is handled by the actual model, not by assuming consistency or
removing windows before the argument.

A finite all-order heterogeneous counting theorem first gives
E choose(R,r)<=e_r(p). The elementary symmetric inequality
r!*e_r(p)<=mu^r is proved by finite ground-set induction and a
nonnegative binomial lower bound, with no moment estimate as input.
The actual full subset generator gives

    E s^R <= product_(x inG) (1+(s-1)*p_x)
          <= exp((s-1)*mu)       (s>=1).

It follows for everyr>=0 that E(R)_r<=mu^r and
P(R>=r)<=mu^r/r!. ForV, every positive-order factorial moment is
at mostmu^r+r*mu^(r-1), its tail is at most
mu^(k-1)/(k-1)! for everyk>=1, and

    E s^V <= s*product_(x inG)(1+(s-1)*p_x)
           <= s*exp((s-1)*mu).

The bounds concern actual Bochner integrals and actual infinite-law
event probabilities, using the previously checked observable
integrability and exact finite-cylinder transport. No generating
function is asserted to be a distribution without construction.
All natural orders, zero means, zero marginals and empty ground sets
are included, without a growing-order asymptotic substitution.

P1-MATH-0088 records removal of regularity for this direct-maximum
envelope part ofT19.3. This does not remove regularization from the
full approximation theorem, or prove domination of the full original
count byV. The specified modified count, exceptional-event structure
and numerical coupling/error estimate remain open;T19.3 stays in
progress. Coverage77/167 (main28/73, companion49/94), findings88.
No new external input, BCN premise, PaperC port, dependency download,
manuscript-byte change or Palomar registration is introduced.

Lean v4.36.0-rc2 full build passed (10761 jobs); actual axiom audit passed for all 6555 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 4272 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records remain intact. Ubuntu available space: 15.56 GiB. Actual direct-family joint factorization is proved for all finite actual ground sets, including zero marginals. The constructed maximum and its shifted envelope have all-order elementary-symmetric, Poisson factorial/tail and heterogeneous product/exponential bounds with the exact sum of actual marginals. This sum is identified with the actual dyadic count mean. All integrals and probabilities are transported through the actual finite cylinder; no regularity, critical band, BCN or unproved numerical estimate is assumed. P1-MATH-0088 records the regularity-free envelope extension. The specified modified count, structural domination and numerical exceptional-event/coupling estimate remain open; T19.3 stays in progress. Coverage77/167 (main28/73, companion49/94), confirmed mathematical improvements88. No new external input, PaperC port, dependency download, manuscript-byte change or Palomar registration.


## Actual retained-modified law, exact coupling and all-order bounds

An actual modified count is now constructed by retaining exactly the
active configurations in the geometric first retained class and setting
the count to zero otherwise. Its bad event is the literal measurable
complement of that retained-active class. Write its actual probability
asdelta. No smallness or numerical estimate fordelta is an input.

The deterministic step is proved in the actual effective spaces.
For a compressed pair e inI, deleting either endpoint ofe leaves
relative nullity zero. Hence every retainedI has a direct subfamilyD
with |I|<=|D|+1. Applied to the actual active set, this gives

    modifiedCount <= R+1,

whereR is the previously constructed actual largest direct active
subfamily. Outside the bad event, the count is the original count.
ForN>=2, every active subfamily there has actual relative nullity
at mostL/3+1, by the checked good-pair bound and retained heredity.
This proves the finite geometric retained-class part ofT15.2.
It does not estimate the probability of the union of arithmetic
seed obstructions used in the source proof.

The modified variable and the bad event are realized exactly through
one explicit finite prime cylinder. Its natural observation law is
an actual probability measure, identified with the measurable
pushforward of the original infinite measure. Every real observable
is integrable, and its actual law integral agrees with the original
Bochner integral and finite probability sum. The original count law
is constructed and identified with its own actual pushforward too.
These are probability measures with proved normalization, rather than
signed expansions treated as probabilities.

The original and modified variables disagree exactly on the bad
event. The finite coupling is transported to their actual probability
laws, proving

    TV(Law(originalCount),Law(modifiedCount)) <= delta.

Withmu=sum of the actual local marginals, the modified count has,
for everyk>=1,r>=1 ands>=1,

    P(modifiedCount>=k) <= mu^(k-1)/(k-1)!,
    E(modifiedCount)_r <= mu^r+r*mu^(r-1),
    E s^modifiedCount <= s*product_(x inG)(1+(s-1)*p_x)
                       <= s*exp((s-1)*mu).

The original count satisfies the same tail bound with+delta.
All these are finite all-order statements on every actual finiteG,
including irregular and zero-marginal windows, and require onlyL>0.
Their proof uses actual pointwise domination, integrable Bochner
monotonicity and event inclusion; no target moment or probability
bound is assumed. On a regular ground set the exact binomial factor
s*(1+p*(s-1))^|G| andmu=|G|p are recovered. A single checked theorem
packages all five source inequalities with the literaldelta.

The still-open arithmetic core estimates must supply
delta=O(N^(-4/5+epsilon)) and the comparison with the source's specified
seed-union event. No such rate or identification is inferred from
this finite construction. ThusT15.2 moves to in_progress andT19.3
stays in_progress; neither is counted complete. Finding88 is extended
with the actual heterogeneous retained-modified construction.
Coverage77/167 (main28/73, companion49/94), findings88 unchanged.
No new external input, BCN premise, PaperC port, dependency download,
manuscript-byte change or Palomar registration is introduced.

Lean v4.36.0-rc2 full build passed (10771 jobs); actual axiom audit passed for all 6598 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 4315 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records remain intact. Ubuntu available space: 15.54 GiB. Deleting a compressed-pair endpoint gives a direct subfamily, proving actual retained-active count domination byR+1. Outside the literal measurable bad event, every active subfamily has nullity<=L/3+1 forN>=2. The zeroed retained-count law and the original law are actual probability pushforwards of the original infinite signs; every observable is integrable and all finite-cylinder and law integrals agree. Exact disagreement is the bad event, giving actual TV coupling<=delta. All-order heterogeneous modified factorial/tail/product-exponential bounds, the original tail with+delta and all five regular-setT19.3 inequalities are proved. The source arithmetic estimate fordelta and identification with its seed-union event remain open; T15.2,T19.3 are in progress. Finding88 is extended; coverage77/167 (main28/73, companion49/94), confirmed improvements88. No new external input, BCN premise, PaperC port, dependency download, manuscript-byte change or Palomar registration.


## Actual retained-modification error tends uniformly to zero under BCN

The actual retained-modification error now converges uniformly to zero,
conditional on the existing explicit BCN plane-curve bound. For every fixed
critical-band width C and tolerance epsilon>0, there is a threshold N0 such that,
for every N>=N0, every critical L, every G contained in the dyadic block and
every real H,

    delta(H,N,L,G) <= epsilon,
    TV(Law(originalCount),Law(retainedModifiedCount)) <= epsilon.

Here delta is the literal probability that the actual active configuration is
not retained. No estimate for delta or convergence assertion is a premise.

The finite probabilistic step is unconditional: a nonretained active set has
positive relative nullity and hence contains an actual minimally dependent
subfamily of size at least two. For every finite cutoff K,

    delta <= actualMean/(K+1)
             + sum_(r=2..K) actualJointMass(primitiveFamilies of size r).

The expectation identity uses the exact finite cylinder of the original
infinite measure. The first term handles configurations with more than K
active starts; the remaining terms are actual joint probabilities, not
centered activities or formal weights. Empty ground sets and zero marginals
are included.

Under BCN, the two-site primitive joint mass is at most N^(-1/2+eta), using
the actual pair host count and actual joint-probability bound. Every fixed
order r>=3 has this same weaker bound from the unconditional primitive
estimate N^(1-r/2+eta). Only finitely many fixed orders are assembled.
The critical actual mean is uniformly bounded by M=2*2^C. Choose K after
epsilon so that M/(K+1)<=epsilon/2, then choose N0 to make the finitely many
primitive masses sum to at most epsilon/2. In particular K is fixed before
N, and no fixed-order constant is applied to an order growing with N.

This proves qualitative disappearance of the actual modification and its
coupling error. It does not prove the source rate N^(-4/5+eta), identify the
bad event with the specified source seed union, or establish a Poisson or
quadratic approximation for the original count. Companion T15.2 and T19.3
remain in progress. Numbered coverage stays 77/167 (main 28/73, companion
49/94), confirmed mathematical improvements stay 88. The BCN result remains
an ordinary explicit theorem argument; no new external input or axiom is
introduced. Original manuscript bytes and the Lean/Mathlib pins are preserved.

Verified Lean v4.36.0-rc2 full build (10777 jobs), actual Audit.lean kernel audit (6611 declarations; only propext, Classical.choice, Quot.sound), 4328 direct ledger/finding declaration checks, 138 source manifest entries and all 167 original statement hashes. Ubuntu root free space: 15.52 GiB. The literal retained bad-event probability and actual original-to-modified TV tend uniformly to zero under the ordinary explicit BCN premise. Finite cutoff K is fixed after the tolerance and before N. No source quantitative rate, Poisson approximation, new numbered completion or new mathematical finding is claimed. Coverage 77/167 (main 28/73, companion 49/94); confirmed improvements 88.


## Actual fixed count moments are uniformly bounded under BCN

Actual fixed-order dependent-family mass is now bounded under the existing
explicit BCN premise. For every fixed r and eta>0, uniformly for critical L
and every G contained in the dyadic block,

    sum_(I subset G, |I|=r, rho(I)>0) P(all starts in I active)
       <= N^(-1/2+eta)

for all sufficiently large N. The argument does not assume this bound.
Every dependent I contains a primitive seed D of size between 2 and r.
Canonical injective enumerations transport actual unordered families to the
already proved ordered-tuple propagation theorem, with an explicit r! position
factor. Their joint masses are exactly those of the original infinite measure.
The zero masses of incompatible seeds are retained; no regularity or positivity
restriction is imposed. A finite cover over all seed sizes is taken before N.

More generally, every actual family of size s+k containing a seed from a
finite s-site seed family F has joint mass at most

    (s+k)! * N^eta * sum_(D in F) P(all starts in D active).

This propagation statement is unconditional and keeps the full actual seed
mass. BCN is used only for the primitive two-site mass needed in the final
coarse dependent-family estimate.

An unconditional finite decomposition then proves, with the exact
heterogeneous mean mu=sum_x p_x,

    E(Z_G)_r <= mu^r + r! * dependentJointMass(G,L,r).

The direct families have exactly their actual product marginals, and the
nonnegative elementary-symmetric inequality bounds their total. Under BCN,
for every fixed r and eta>0 this gives

    E(Z_G)_r <= mu^r + N^(-1/2+eta).

The critical mean is uniformly bounded. Hence every fixed factorial moment
and every fixed ordinary moment of the original count is uniformly bounded.
The passage to ordinary moments uses the checked finite integer inequality

    n^r <= (2*r)^r + 2^r * n.descFactorial(r),

including r=0. No moment hypothesis, Poisson-law approximation, small coupling
error, or large-order estimate is used to deduce these bounded moments.
The already proved regular-count transfer now has its higher-moment premise
discharged under BCN, yielding, for every fixed j>=1,

    |E Z_N^j - E Z_regular^j| <= K * N^(-1+eta).

Main 6.4 moves from not_started to in_progress: its bounded-moment clause is
proved under explicit BCN, but its two-sided factorial/ordinary expansions,
quadratic correction, sharp 4/5 remainder and all higher factorial cumulants
are not asserted. Main 3.1 retains its previously proved aligned scope;
the new moment-transfer consequence is conditional only on BCN. Numbered
coverage remains 77/167 (main 28/73, companion 49/94), confirmed improvements
remain 88. No new external input, axiom, dependency download, source-byte
change, or Palomar registration is introduced.

Verified Lean v4.36.0-rc2 full build (10789 jobs), actual Audit.lean kernel audit (6636 declarations; only propext, Classical.choice, Quot.sound), 4353 direct ledger/finding declaration checks, 138 source manifest entries and all 167 original statement hashes. Ubuntu root free space: 15.49 GiB. Unordered actual seed propagation is unconditional; fixed dependent-mass and original moment bounds use only the existing ordinary explicit BCN premise. All moment orders and finite seed-size covers are fixed before N. Main 6.4 is in progress: bounded original moments are proved under BCN, but no full sharp moment expansion is claimed. Coverage 77/167 (main 28/73, companion 49/94); confirmed improvements 88.


## Two-sided actual fixed factorial-moment convergence under BCN

Every fixed actual factorial moment now has a two-sided coarse estimate.
For the original full dyadic count, with its exact actual mean mu_N,
for every fixed r>=0 and eta>0, under the existing explicit BCN premise,

    |E(Z_N)_r - mu_N^r| <= N^(-1/2+eta)

eventually, uniformly for every critical length L in the fixed band. The
same estimate holds with the nominal mean lambda_N. These are actual
Bochner factorial moments of the original infinite prime-sign count.
No target moment expansion is assumed.

The new lower branch is unconditional. Exact deletion and insertion of a
marked coordinate give the finite identity

    sum_(distinct (r+1)-tuples) q(tuple)
      = sum_(distinct r-tuples t) sum_(z not in t) q(t union {z}).

For positive source mass, the inner sum is exactly that source mass times
its actual fresh conditional mean. Zero source masses are handled directly
by nonnegativity; no incompatible family is divided by its zero mass.
The previously checked negative conditional-deviation bound therefore gives

    E(Z_N)_r >= max(0,lambda_N-N^(-1/2+eta))^r

for every fixed r, without BCN. A bounded nonnegative power-difference
inequality yields lambda_N^r-E(Z_N)_r<=N^(-1/2+eta), still unconditionally.
All source cardinalities used in this induction are bounded by fixed r
before the final scale N is chosen.

The existing BCN-dependent upper bound uses the actual heterogeneous mean
and actual dependent-family mass. The exact mean bias estimate also gives,
unconditionally at every fixed r,

    |mu_N^r-lambda_N^r| <= N^(-1+eta).

Combining these checked branches proves the displayed two-sided estimates.
This is a first factorial-moment convergence result and is weaker than the
source quadratic expansion: the correction binom(r,2)*mu_N^(r-2)*alpha_N,
the source 4/5 error, ordinary-moment expansion and higher-cumulant estimate
remain open. It is not asserted to be an original-law total-variation or
Poisson approximation theorem. Main 6.4 remains in progress. Coverage stays
77/167 (main 28/73, companion 49/94), confirmed improvements stay 88.
The external BCN input is an ordinary explicit argument; no axiom, new
literature input, dependency download, source-byte change or Palomar
registration is introduced.

Verified Lean v4.36.0-rc2 full build (10799 jobs), actual Audit.lean kernel audit (6648 declarations; only propext, Classical.choice, Quot.sound), 4365 direct ledger/finding declaration checks, 138 source manifest entries and all 167 original statement hashes. Ubuntu root free space: 15.48 GiB. The actual fresh-tuple recurrence, lower factorial branch and power mean-bias estimate are unconditional. Two-sided actual and nominal fixed factorial-moment errors N^(-1/2+eta) use the existing ordinary explicit BCN premise. Orders and all bounded-order assemblies are fixed before N. No sharp quadratic expansion or original-law TV theorem is claimed. Main 6.4 remains in progress. Coverage 77/167; confirmed improvements 88.


## Uniform actual original-law Poisson approximation under BCN

The actual original count law now has a uniform qualitative Poisson
approximation, conditional on the existing explicit BCN plane-curve bound.
For every fixed critical-band width C and every tolerance epsilon>0 there
is one threshold N0 such that, for every N>=N0 and every critical length L,

    TV(Law(Z_N),Pois(mu_N)) <= epsilon,
    TV(Law(Z_N),Pois(lambda_N)) <= epsilon.

Here mu_N is the exact actual mean and lambda_N is the nominal mean. Both
Poisson references are actual normalized probability measures with singleton
masses exp(-mu)*mu^k/k!. Their parameters remain those of the current N,L;
no frozen limiting phase, fixed limiting mean, or convergence of the means
is assumed. Law(Z_N) is the actual pushforward law of the original infinite
prime-sign count, not a retained polynomial treated as a probability law.

The reconstruction argument is finite and unconditional before the arithmetic
moment estimates are inserted. For any finite Boolean family, write F_r for
its actual factorial moment and Delta=delta_1-delta_0. Its count law differs
from the finite polynomial sum_(r<k) F_r*Delta^r/r! in ordinary l1 by at most

    2^k * F_k / k!.

This follows from the already proved first-excluded-prefix expansion with
the hereditary cutoff |I|<k. Every boundary set has exactly k sites; its
suffix kernel stays positive and costs exactly its actual mass. Grouping
by cardinality identifies all coefficients with the actual factorial
moments. Comparing two such polynomials costs at most

    sum_(r<k) (2^r/r!) * |F_r-G_r|.

A new finite Banach-algebra estimate retains the factorial denominator:

    ||exp(x)-sum_(r<k) x^r/r!||
       <= ||x||^k * exp(||x||) / k!.

It is proved from the actual exponential series and the divisibility of
j!*k! into (j+k)!, not assumed as an interface. Applied in the completed
ordinary-l1 convolution algebra to x=mu*Delta, it bounds the Poisson
remainder by (2*mu)^k*exp(2*mu)/k!. Singleton coefficient comparison
transports the completed-norm bound to actual total variation. Universal
Poisson parameter stability TV(Pois(mu),Pois(nu))<=|mu-nu| is proved too.

For the actual original count, mu_N is uniformly bounded by M=2*2^C.
Choose the finite reconstruction order k AFTER epsilon, so that the
factorial tails for this fixed M are small. Only then assemble the
finitely many fixed-order moment estimates and choose N0. The original
moment of order k is bounded by mu_N^k+1, and the finite polynomial error
tends to zero by the checked fixed-order factorial estimates. The
convergent exponential series makes the reconstruction tails vanish.
No growing-order moment bound or target law approximation is a premise.

This proves leading Poisson approximation but not a quantitative TV rate,
the source optimal quadratic correction, its 4/3 remainder, or the exact
TV scale in main 1.2. Main 1.1 and 6.4 remain in progress; main 1.2 is not
counted complete. Numbered coverage remains 77/167 (main 28/73, companion
49/94); confirmed mathematical improvements remain 88. BCN is the same
ordinary explicit theorem argument already inventoried. No new external
input, axiom, dependency download, manuscript-byte change or Palomar
registration is introduced.

Verified Lean v4.36.0-rc2 full build (10809 jobs), actual Audit.lean kernel audit (6668 declarations; only propext, Classical.choice, Quot.sound), 4385 direct ledger/finding declaration checks, 138 source manifest entries and all 167 original statement hashes. Ubuntu root free space: 15.46 GiB. Finite factorial count-law reconstruction, the factorial Banach remainder and actual Poisson parameter stability are unconditional. Uniform original-law TV convergence to actual and nominal Poisson references uses the existing ordinary explicit BCN premise. Reconstruction order is chosen after tolerance and before N. No quantitative TV rate, optimal quadratic correction, new numbered completion or new mathematical finding is claimed. Coverage 77/167 (main 28/73, companion 49/94); confirmed improvements 88.


## Half-power actual triple activity and third cumulants under BCN

The actual absolute triple activity and actual third factorial cumulant
now satisfy the stronger coarse half-power estimates under explicit BCN:
for every eta>0, uniformly in every critical L and every G contained in
the dyadic block, eventually

    sum_(I subset G, |I|=3) |c(I)| <= N^(-1/2+eta),
    |kappa_3^factorial(Z_G)| <= N^(-1/2+eta).

These improve the earlier coarse exponent g=1/2-(2/3)*log(2)>0. The sharper
source exponents in main 14.1 and 14.6, and the sharp comparison remainder
in main 11.3, remain open. The new result does not replace those aligned
statements or count them complete.

The proof first uses the newly checked second and third factorial-moment
estimates for the full original count. With its actual mean mu,

    kappa_3 = (F_3-mu^3) - 3*mu*(F_2-mu^2),

and mu is uniformly bounded, so the full third cumulant has the half-power
bound. Next, deleting zero-marginal sites is proved to preserve all actual
joint-mass sums, every factorial moment and this cumulant exactly. A joint
family containing a zero-marginal site has actual mass zero; it is never
divided by a zero probability.

On the positive ground set, the existing actual incompatible-activity and
cumulant comparisons cost at most N^(-1+eta). These compare the full third
cumulant with six times the positive connected activity, and the latter
with the actual absolute triple activity. Exact zero-marginal restriction
recovers the activity on the full dyadic block. Since absolute activity
is a nonnegative sum, restriction to every G costs nothing. Finally the
exact third-cumulant identity, including its actual repeated-index cost
N^(-3/2+eta), gives the same half-power cumulant bound for every G.
All fixed orders and thresholds are assembled before N; heterogeneous
marginals, incompatible families and repeated indices remain explicit.

No new external input or axiom is introduced: BCN is the same ordinary
explicit plane-curve argument. Main 11.3, 14.1 and 14.6 remain in progress.
Coverage stays 77/167 (main 28/73, companion 49/94), confirmed improvements
stay 88. Original manuscript bytes, compiler/dependency pins and the later
Palomar milestone are preserved.

Verified Lean v4.36.0-rc2 full build (10813 jobs), actual Audit.lean kernel audit (6675 declarations; only propext, Classical.choice, Quot.sound), 4392 direct ledger/finding declaration checks, 138 source manifest entries and all 167 original statement hashes. Ubuntu root free space: 15.45 GiB. Exact deletion of zero-marginal sites preserves every actual factorial moment and the third cumulant. Under the existing ordinary explicit BCN premise, full absolute triple activity and the third factorial cumulant are uniformly at most N^(-1/2+eta) for every dyadic subground. All repeated and incompatible costs remain explicit. The sharp source exponents remain open; main 11.3,14.1,14.6 stay in progress. Coverage 77/167; improvements 88.


## Actual retained-modified moments and Poisson laws converge under BCN

The actual retained-modified count now agrees asymptotically with the
original count at every fixed ordinary moment, under explicit BCN.
For every fixed j>=0 and tolerance epsilon>0 there is a threshold N0,
uniform over every critical length L, every G contained in the dyadic
block and every real H, such that

    |E Z_G^j - E modified(H,N,L,G)^j| <= epsilon.

This is not inferred from small total variation alone. An unconditional
finite-cylinder theorem gives the actual quantitative truncation inequality
for every finite G, every j<=q and every R>0:

    |E Z_G^j - E modified^j|
       <= R^j * delta + E Z_G^q / R^(q-j).

Here delta is the literal probability of the actual bad event, and the
original count and modified variable are evaluated on the same finite
prime cylinder. The original and modified observables have their exact
Bochner integrals; every real original observable is proved integrable.
The finite modified count is pointwise bounded by the original count,
and their disagreement probability is exactly delta. No numerical estimate
for delta or moment bound is assumed in this finite theorem.

For convergence take the fixed higher order q=j+1. The previously proved
BCN-dependent uniform original moment bound gives E Z_G^(j+1)<=B.
Choose R=1+2B/epsilon before N, then apply the uniform actual bad-event
convergence with tolerance epsilon/(2R^j). The two truncation terms are
at most epsilon/2. The order, truncation level and bad-event tolerance
are all fixed before the final scale; no growing-order substitution occurs.

The actual modified law also converges uniformly, for every H, in total
variation to both actual Poisson references Pois(mu_N) and Pois(lambda_N)
on the full dyadic block. This follows from the checked original-law
Poisson theorem and the exact original-to-modified coupling by delta.
The references use the original actual and nominal means; no identity
between the modified mean and original mean is asserted at finite N.

The source numerical bad-event rate and identification with its specified
seed union remain open. Companion T15.2 and T19.3 remain in progress.
No new numbered completion, mathematical finding, external input, axiom,
dependency download, manuscript-byte change or Palomar registration occurs.
Coverage 77/167 (main 28/73, companion 49/94), improvements 88.

Verified Lean v4.36.0-rc2 full build (10817 jobs), actual Audit.lean kernel audit (6682 declarations; only propext, Classical.choice, Quot.sound), 4399 direct ledger/finding declaration checks, 138 source manifest entries and all 167 original statement hashes. Ubuntu root free space: 15.44 GiB. Finite original-to-modified moment truncation and original-observable integrability are unconditional. Every fixed original-to-modified moment difference and both modified-law Poisson TV distances converge uniformly under the existing ordinary explicit BCN premise. Higher order q=j+1, truncation level and bad-event tolerance are fixed before N. The sharp source error rate stays open. Coverage 77/167; confirmed improvements 88.


## Exact heterogeneous fourth cumulant and its first BCN-dependent bound

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


## Actual absolute centered activity at every fixed positive order

The actual absolute centered activity now has a uniform half-power bound
at every fixed positive order under the existing explicit BCN premise.
For every fixed r>=1 and eta>0, every critical L and every G contained in
the dyadic block, eventually

    sum_(I subset G, |I|=r) |c(I)| <= N^(-1/2+eta).

The connected subfamily satisfies the same bound. These are absolute sums
of the actual centered Bochner coefficients, not absolute values of signed
sums or a consequence of scalar factorial-moment cancellation. Zero
marginals and incompatible affine families are included. The order and
all finite lower-order assemblies are fixed before N.

The finite decomposition is unconditional. Nonempty direct families have
zero actual centered coefficient, including their zero-marginal cases.
Expanding the absolute heterogeneous centering transform and separating its
direct and dependent subfamilies gives, with mu=sum_x p_x,

    A_r <= 2^r * productDependentMass_r
           + sum_(s=0..r) jointDependentMass_s * mu^(r-s)/(r-s)!.

Both masses use actual geometric dependence rho>0. In the second mass,
q(A) is the actual joint probability, and the complementary marginals
are their actual heterogeneous products. Exact disjoint-subset incidence
and the previously proved cardinality convolution give this finite bound.
No absolute-activity estimate is a premise.

A new unconditional estimate proves, for every fixed r and eta>0,

    productDependentMass_r <= N^(-1+eta).

Every dependent family contains a primitive seed. A finite seed-cover
inequality preserves its entire nonnegative heterogeneous product weight:
for s-site seeds and total size s+k, completion costs at most
mu^k/k! times the actual seed product mass. Primitive host counts,
the actual local marginal cap, and the actual mean bound give the displayed
product estimate; no BCN or actual joint estimate is used here.

For the full absolute activity, the actual dependent joint masses at the
finitely many orders 0..r are at most N^(-1/2+eta) under BCN. The actual
mean is uniformly bounded, so the finite decomposition yields the claimed
half-power bound after absorbing fixed constants. BCN is the already
inventoried ordinary explicit plane-curve argument.

Companion T14.1 moves from not_started to in_progress. Its sharper connected
4/5 exponent and its separate N^(-1+eta) absolute contact bound are not
claimed. The proof makes no growing-order use of fixed-order estimates.
No numbered result or new mathematical finding is counted complete.
Coverage stays 77/167 (main 28/73, companion 49/94), improvements stay 89.
Original manuscript bytes, compiler/dependency pins and the later Palomar
milestone are preserved; no dependency download or axiom is introduced.

Verified Lean v4.36.0-rc2 full build (10835 jobs), actual Audit.lean kernel audit (6714 declarations; only propext, Classical.choice, Quot.sound), 4431 direct ledger/finding declaration checks, 138 source manifest entries and all 167 original statement hashes. Ubuntu root free space: 15.41 GiB. The finite absolute-activity decomposition and fixed-order dependent product mass N^(-1+eta) are unconditional. Full and connected actual absolute centered activity at every fixed positive order are at most N^(-1/2+eta) under the existing ordinary explicit BCN premise, uniformly over all dyadic subgrounds. Zero marginals and incompatible families are included; no fixed-order theorem is used at growing order. Companion T14.1 stays in progress for its sharper connected 4/5 exponent and contact bound. Coverage 77/167; improvements 89.


## Actual quartic component factorization and source-scale repeated-index error

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


## Unconditional actual pair rows and source-scale overlapping-edge costs

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


## Pause at the requested usage threshold — 2026-11-02

The user authorized autonomous continuation until approximately 5% of the
Codex usage quota remained. The displayed remaining quota reached 5% after
the pair-row and overlapping-edge checkpoint had passed the full build and
kernel audit. No further mathematical development was started. This is a
pause at the requested usage threshold, not completion of the formalization.

The current compiler remains Lean v4.36.0-rc2. Numbered coverage is 77/167:
28/73 main and 49/94 companion, with 89 confirmed mathematical improvements
recorded for a future manuscript revision. The original v1.6 sources remain
byte-for-byte preserved. Work, dependencies and caches remain on the Ubuntu
root partition; the last measured free space is 15.38 GiB.

Recent proved results include convergence of the actual original count to
Poisson in total variation under the existing explicit BCN premise, transfer
to the actual retained modification, the exact heterogeneous fourth factorial
cumulant identity, a source-scale repeated-index error, unconditional per-site
pair rows and source-scale overlapping-edge product costs. Qualitative Poisson
convergence does not establish the manuscript's optimal rate or its quadratic
reference approximation.

On resumption, the immediate finite task for main 16.1 is to isolate the
product cost from disjoint non-direct edge pairs, using the already checked
repeated-edge and star-square bounds for all overlapping cases. The next
geometric task is to identify the full unordered direct edge-pair sum with
the disconnected quartic population. Its sharp comparison with half the
squared signed pair sum, and the incompatible/connected quartic bounds,
remain open. The numbered-result ledger and the dedicated fourth-cumulant
alignment document record the exact current scope.

Other remaining manuscript claims include sharp third-order and higher-order
rates, growing-order estimates, the source retained-event identification and
sharp exceptional-event rate, and the optimal quadratic/Poisson approximation.
Palomar registrations remain deferred until full coverage and final alignment
checks. No registration or completion claim is made at this checkpoint.


## Resumed development: literal disjoint non-direct pair residual

The user has authorized further work until exhaustion of the quota, superseding the earlier 5% pause.

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


## Exact canonical D22 population and connected-quartic reduction

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


## Unrestricted actual components and a complete coarse quartic comparison

The actual finite-set version of main 4.4 is now checked without a
positive-marginal/admissibility premise. For every finite original family I,
L>0 and every actual relation-direct partition P, the original q(I), c(I)
and relative nullity factor exactly over the original images of its parts.
The same unique finest canonical partition satisfies the complete existing
CanonicalRunPartitionConclusion, with no positive-marginal argument supplied
by the caller. If a marginal vanishes, its unique containing part has zero
joint and centered coefficients, and both full products vanish exactly.
The positive case uses the already checked effective-space factorization.
Empty families and all zero-mass cases are retained. This completes the
unrestricted original-model statement directly rather than relying on a
standing admissibility convention. Main 4.4 stays proved; no new numbered
completion or manuscript correction is counted.

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


## Unconditional weak/irregular pair classes and absolute-cumulant equivalence

Two source-scale parts of companion T7.1 are now proved unconditionally
on the actual original model. Weak dependent pairs are defined literally by
rho(e)<=eta*L or q(e)=0. Their absolute activity is at most
N^(-1+eta+epsilon), for every fixed eta>=0 and epsilon>0. The finite
coefficient bound is 2*2^(eta*L)*prod_(x in e)p_x; the already checked
N^(-1+epsilon) product mass of dependent families supplies the total bound.
No common marginal, positive source mass or BCN premise is required.

Every covariance edge touching an irregular start has total absolute
activity at most N^(-1+epsilon). A finite marked-star cover bounds its mass
by the row sum over the marked sites. The unconditional actual row bound
and actual irregular marginal mass prove the estimate, including zero
marginals. An explicit disjoint three-part partition of the actual dependent
pairs separates the irregular class, the weak class after its removal, and
the remaining class. Their activity sums exactly to A2. Every remaining
pair is compatible, avoids irregular sites and has rho(e)>eta*L.
The remaining rational-channel/dense nonaligned analysis is not asserted.
T7.1 therefore moves from not_started to in_progress, not to proved.

All actual incompatible pair activity is also bounded unconditionally by
the dependent product mass, hence by N^(-1+epsilon). The exact pair sign
identity is A2-C2=2*A2_incompatible, with C2 the signed pair sum. The exact
heterogeneous second-cumulant formula consequently yields

    A2(G)-alpha(G)/2 = 2*A2_incompatible(G)+sum_(x in G)p_x^2/2.

The right side is nonnegative and eventually at most N^(-1+epsilon),
uniformly for all critical lengths and dyadic subgrounds. For the full
original dyadic count, the independently proved positive 2:3 channel lower
bound alpha>=d*L*N^(-2/3) gives the stronger quantitative equivalence

    alpha>0,
    0 <= 2*A2/alpha-1 <= N^(-1/3+epsilon).

These statements keep the actual moving mean, second cumulant, irregular
windows and all zero-marginal cases. They do not assume a full pair profile,
a sharp upper bound on A2 or the external BCN estimate. This new corollary
is recorded as improvement P1-MATH-0090 for later manuscript integration.
It does not prove the remaining full profile, the source A2 upper bound,
the good-channel partition or sharp triple/quartic errors. Main 3.3 remains
in progress. Coverage stays 77/167 (main 28/73, companion 49/94); confirmed
improvements increase to 90. No new external input, axiom, dependency
download, source-byte change or Palomar registration is introduced.

Verified Lean v4.36.0-rc2 full build (10905 jobs), actual Audit.lean kernel audit (6818 declarations; only propext, Classical.choice, Quot.sound), 4535 direct ledger/finding declaration checks, 138 source manifest entries and all 167 original statement hashes. Ubuntu root free space: 15.30 GiB. Weak dependent activity N^(-1+eta+epsilon), irregular-touching and incompatible pair activity N^(-1+epsilon), the exact initial disjoint partition, and the quantitative full-count equivalence 0<=2*A2/alpha-1<=N^(-1/3+epsilon) are unconditional. No BCN, complete signed profile or target A2 estimate is supplied as a premise. T7.1 and main 3.3 remain in progress; coverage 77/167, confirmed improvements 90.


## All-order actual canonical blocks and a quadratic nonconnected remainder

Actual canonical components are now handled as original finite subsets
at every finite order. Their union recovers I, every part is nonempty and
connected, and the original coefficient satisfies c(I)=prod_(C in P(I))c(C).
The absolute identity also holds exactly. Reindexing the subtype parts is
injective, so no duplicate part or hidden multiplicity is introduced.
If c(I)!=0, every part has at least two sites. Every nonempty nonconnected
family has at least two canonical parts. These finite statements include
zero marginals and incompatible families; only L>0 is needed for the
probability factorization.

A separate arbitrary-weight finite polymer lemma proves the tail bound

    sum_(P subset A, |P|>=2) prod_(C in P)w(C)
        <= (W^2/2)*exp(W),  W=sum_(C in A)w(C), w>=0.

An actual decomposition whose union recovers its source family is injective
as a finite record, so the same bound controls any covered family with
at least two blocks. No independence of arbitrary polymers is assumed.
Applying this to the actual canonical components gives, for every fixed r>=1,

    A_r - A_r_connected = A_r_nonconnected >= 0,
    A_r_nonconnected <= (W_r^2/2)*exp(W_r),

where W_r is the literal absolute activity of all connected original blocks
of sizes 2 through r. The finite bound and exact difference are unconditional.
Under the existing ordinary explicit BCN premise, the already checked
fixed-order half-power estimates at the finitely many orders up to r give

    0 <= A_r - A_r_connected <= N^(-1+epsilon)

eventually uniformly over critical lengths and all dyadic subgrounds.
The threshold depends on r before N; no growing-order conclusion is made.
This is a sharper remainder for nonconnected families. The source 4/5
connected bound and separate contact estimate of T14.1 remain open.
Main 4.4 stays proved and companion T14.1 stays in progress. Coverage stays
77/167 (main 28/73, companion 49/94), confirmed improvements stay 90.
No new external input, axiom, dependency download, source-byte change or
Palomar registration is introduced.

Verified Lean v4.36.0-rc2 full build (10913 jobs), actual Audit.lean kernel audit (6838 declarations; only propext, Classical.choice, Quot.sound), 4555 direct ledger/finding declaration checks, 138 source manifest entries and all 167 original statement hashes. Ubuntu root free space: 15.28 GiB. Exact canonical original block images, connectedness, coefficient/absolute factorization, nonzero block size and the finite quadratic polymer tail are unconditional. Under existing explicit BCN, nonconnected activity and the absolute all/connected activity difference are at most N^(-1+epsilon) at every fixed positive order, uniformly over dyadic subgrounds. Growing orders and the source sharp connected/contact bounds are not claimed. Main 4.4 stays proved; companion T14.1 stays in progress. Coverage 77/167, improvements 90.


## Unconditional subpower moments at every fixed order

Every fixed nonnegative order now has an unconditional subpower bound
on the actual original model. For every fixed r>=0 and epsilon>0,

    sum_(I subset G, |I|=r)q(I) <= N^epsilon,
    E[(Z_G)_r] <= N^epsilon,
    E[Z_G^r] <= N^epsilon,

eventually uniformly over all critical lengths and every dyadic subground.
No BCN premise is used. The order, exponent and threshold are fixed before N.
For r>=1, every r-site family contains a singleton seed. The checked
unordered positive propagation bound and bounded exact actual mean give
the first estimate, with its factorial coefficient absorbed only afterward.
The exact factorial-moment subset formula gives the second. The elementary
pointwise comparison n^r<=(2r)^r+2^r*(n)_r gives the third. Order zero is
included explicitly. Irregular windows and zero marginals remain present.

These are weaker than uniform boundedness or convergence to the Poisson
factorial moments; the stronger existing boundedness/convergence theorems
remain conditional on their already explicit BCN premise. The new
unconditional subpower bounds can be used in fixed-order truncation and
contact estimates without assuming the source full fixed-moment asymptotic.
Main 6.4 remains in progress. Coverage stays 77/167 (main 28/73, companion
49/94), improvements stay 90. No new external input, axiom, dependency
download, source-byte change or Palomar registration is introduced.

Verified Lean v4.36.0-rc2 full build (10915 jobs), actual Audit.lean kernel audit (6841 declarations; only propext, Classical.choice, Quot.sound), 4558 direct ledger/finding declaration checks, 138 source manifest entries and all 167 original statement hashes. Ubuntu root free space: 15.28 GiB. Actual joint subset masses, factorial and ordinary moments are at most N^epsilon at every fixed nonnegative order, unconditionally and uniformly over all dyadic subgrounds. The proof uses positive singleton-seed propagation and the bounded actual mean, not BCN or assumed moment bounds. This does not claim uniform boundedness or the complete source asymptotic. Main 6.4 stays in progress; coverage 77/167, improvements 90.


## Unconditional fixed contact activity at the source exponent

The contact conclusion of companion T14.1 is now proved at its full
N^(-1+epsilon) scale, unconditionally, on every original dyadic subground
and at every fixed order r>=2. The actual population consists exactly of
r-site families containing distinct sites x<y<=x+L, with no connectedness
restriction. Irregular starts, incompatible families and zero marginals
are included. The separate source connected 4/5 conclusion remains open,
so T14.1 remains in progress and no numbered result is counted complete.

The proof gives a more general finite statement on an arbitrary finite
Boolean probability space. For actual heterogeneous marginals p_x, a
family containing one of the specified two-site seeds satisfies

    sum_I |c(I)| <= R^(r-2) * sum_e(q(e)+3*prod_(x in e)p_x)
                   + E[(Z+mu)^m]/R^(m-r),

for every R>0 and fixed integer m>=r. No independence, regularity, common
marginal or positive seed mass is assumed. Absolute centered products are
bounded by products of J_x+p_x. The finite seed-cover inequality bounds
the family sum by the positive seed sum times (Z+mu)^(r-2). Below R this
costs R^(r-2) times the seed sum; above R the full product is bounded by
the higher moment divided by R^(m-r). The seed expectation is exactly
q(e)+3*prod p, retaining all four Boolean expansion terms.

For the original arithmetic model, a positive joint close pair must have
y=x+L, by exact run separation. The actual endpoint seed count bounds its
total joint mass. An explicit forward-neighbor cover proves
sum_(close e)prod p <= L*p_max*mu, including all heterogeneous marginals.
The contact seed kernel is therefore at most N^(-1+delta) for every fixed
delta>0. Every fixed positive-envelope moment E[(Z+mu)^m] is also at most
N^delta, using the newly checked unconditional subpower count moments.
Choose delta=epsilon/(4(r+1)), then one fixed higher moment m before N,
and finally R=N^delta. Both truncation terms have the required exponent;
the last constant is absorbed only after these exact estimates.

This replaces the source contact proof's use of uniformly bounded fixed
moments by the weaker unconditional subpower estimates. It also removes
the regular-ground/common-marginal restriction from this contact conclusion.
The proof is recorded as improvement P1-MATH-0091 for a future manuscript
revision. It asserts no source error, connected 4/5 bound, growing-order
control or complete fixed-moment asymptotic. Main 6.4 and T14.1 remain in
progress; coverage 77/167 (main 28/73, companion 49/94), improvements 91.
No new external input, axiom, dependency download, source-byte change or
Palomar registration is introduced.

Verified under Lean v4.36.0-rc2: full lake build (10931 jobs), source and ledger checks, actual axiom audit of 6864 declarations (only propext, Classical.choice and Quot.sound), and 4581 direct ledger/evidence declaration checks; Ubuntu root free space 15.24 GiB. Original manuscript bytes and all 167 statement hashes preserved.


## Unconditional finite good-channel activity

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


## The literal principal two-channel edge family

The actual principal edge family is now the union of the compatible,
private, dependent unordered populations in channels 2:3 and 3:4.
An exact displacement argument proves their disjointness once
29(L+1)<N: simultaneous channel alignments force the first center
below 29(L+1), contradicting its dyadic location. Its cardinality is at
most 26(L+1)N. Its joint mass beta is exactly half the sum of the two
ordered channel masses; probability-zero pairs were removed without
changing these masses.

For every fixed C,D there are positive c,k and one threshold such that,
for every critical L and 8(L+1)<=H<=D(L+1),

    c*L*N^(-2/3) <= beta <= k*L*N^(-2/3).

This is the source positive phase for the literal two-channel beta,
unconditionally. The correction from beta to its own absolute centered
activity is nonnegative and at most N^(-1+epsilon), uniformly in H.
Combining this exact subfamily with the already checked full
absolute-activity/cumulant gap also proves the one-sided comparison

    2*beta - actual_alpha <= N^(-1+epsilon),

without BCN or a complete pair profile. This is only one side of the
source absolute residual estimate. The reverse inequality at exponent
4/5, the full bad-pair activity and the complete signed pair profile
remain open. Main 3.4 stays in progress. Coverage stays 77/167 (main
28/73, companion 49/94), confirmed improvements 91. No new correction,
external input, axiom, dependency download, original-source change or
Palomar registration is introduced.

Verified under Lean v4.36.0-rc2: full lake build (10947 jobs), source and ledger checks, actual axiom audit of 6902 declarations (only propext, Classical.choice and Quot.sound), and 4619 direct ledger/evidence declaration checks; Ubuntu root free space 15.20 GiB. Original manuscript bytes and all 167 statement hashes preserved.


## Actual principal-edge activation and improvement P1-MATH-0092

The literal positive count Xi of active edges in any deterministic finite
pair family is now constructed on the original infinite prime-sign model.
Its value is the number of edges all of whose sites are active. Exact
finite-cylinder transport proves its first moment is the sum of actual
joint masses and its positivity event is precisely the union of the edge
events. A finite combinatorial estimate bounds Xi by Z_G^2. For every
R>0 and fixed m>=2 the actual truncation inequality is

    sum_(e in F)q(e) <= R^2*P(Xi>0)+E[Z_G^m]/R^(m-2).

The first Bonferroni correction is proved for every integer-valued finite
count, then transported to the actual original edge count:

    0 <= E[Xi]-P(Xi>0) <= E[Xi*(Xi-1)]/2.

For the literal principal channels 2:3 and 3:4, E[Xi]=beta exactly.
Their already proved positive beta phase and the unconditional subpower
fixed count moments imply, for every fixed epsilon>0 and C,D, one uniform
threshold for all critical lengths and 8(L+1)<=H<=D(L+1),

    N^(-2/3-epsilon) <= P(Xi>0) <= N^(-2/3+epsilon).

The proof chooses delta=epsilon/4, one fixed higher moment m=2+k with
delta*k>=2, and R=N^delta. The tail is bounded by N^(-3/2), which is
absorbed into half the positive beta lower bound. This needs neither BCN,
a complete signed pair profile, uniformly bounded fixed moments nor the
sharp second-factorial-moment estimate. The logarithmic rare-event exponent
is recorded as improvement P1-MATH-0092 for later manuscript integration.
It does not imply P(Xi>0)~beta or E[(Xi)_2]~beta^2; those sharp assertions
of T1.17 remain open. T1.17 moves from not_started to in_progress; main
3.4 stays in progress. Coverage remains 77/167 (main 28/73, companion 49/94),
confirmed improvements 92. No new external input, axiom, download,
original-source change or Palomar registration is introduced.

Verified under Lean v4.36.0-rc2: full lake build (10957 jobs), source and ledger checks, actual axiom audit of 6923 declarations (only propext, Classical.choice and Quot.sound), and 4640 direct ledger/evidence declaration checks; Ubuntu root free space 15.18 GiB. Original manuscript bytes and all 167 statement hashes preserved.


## Uniform active-family moments and improvement P1-MATH-0093

A general original-model positive-family theorem now applies to every
fixed positive cardinality s and fixed positive moment order r. Let F be
any deterministic family of s-element subsets of any dyadic subground G,
Xi_F the number of fully active members, and M_F=sum_(e in F)q(e).
For every fixed epsilon>0, one threshold works uniformly for all critical
lengths, subgrounds and such families, and gives

    E[Xi_F^r] <= N^epsilon*M_F,
    M_F*N^(-epsilon) <= P(Xi_F>0) <= M_F.

There is no independence, common-marginal, regularity, positive-source-mass
or BCN premise. F may vary after N. The fixed s,r,epsilon precede the
threshold. The theorem does not cover growing s or growing r.

The proof transports the checked source propagation to unordered joint
rows after every nonempty seed of bounded cardinality. A finite recurrence
expresses each seeded count moment of degree k as the sum of the moments
after one inserted target. Iteration costs A^k when each row costs A.
Since Xi_F<=Z_G^s, this controls Xi_F^r after the first active member by
s(r-1) extra targets. The exponent margin is chosen before this iteration.
No division by the source mass is used, including when M_F=0.
A separate finite linear truncation converts E[Xi_F^2]<=B*M_F into
M_F<=4B*P(Xi_F>0), and the last constant is absorbed into the exponent.

This supplies a general probability and moment corollary of main 6.3,
recorded as improvement P1-MATH-0093. It includes the literal principal
edge family as s=2 and strengthens the route to its logarithmic activation
exponent. It does not give P(Xi_F>0)~M_F, a sharp second factorial moment,
the full signed pair profile, or any growing-order bound. Main 6.3 stays
proved; main 3.4 and T1.17 stay in progress. Coverage remains 77/167 (main
28/73, companion 49/94), confirmed improvements 93. No new external input,
axiom, dependency download, original-source change or Palomar registration
is introduced.

Verified under Lean v4.36.0-rc2: full lake build (10965 jobs), source and ledger checks, actual axiom audit of 6936 declarations (only propext, Classical.choice and Quot.sound), and 4653 direct ledger/evidence declaration checks; Ubuntu root free space 15.17 GiB. Original manuscript bytes and all 167 statement hashes preserved.


## Exact-contact refinements and improvement P1-MATH-0094

The literal dyadic exact-contact edge family is now constructed as
{x,x+L} with both starts in I_N. If the full union window of length 2L
is regular, every prescribed pair atom is exactly 2^(-2L). This follows
from a general full-effective-rank tuple uniformity theorem; affine
compatibility is proved by full rank rather than assumed. Uniform
irregular-window counts apply at length 2L with the enlarged logarithmic
width, and at least N/2 admissible contact starts have regular unions.
Consequently there is a positive c_C with

    c_C*N^(-1) <= M_contact <= N^(-1+epsilon)

for all sufficiently large critical N,L. The lower bound retains the
actual moving length phase through 2^(-2L). The general positive-family
activation theorem then gives

    N^(-1-epsilon) <= P(an active exact-contact edge) <= N^(-1+epsilon).

A generic positive-mass cover theorem proves that deleting probability-zero
members preserves the actual activation probability. Every positive-mass
close pair has separation exactly L, so the same probability bounds hold
for the event that two original active starts have distance at most L.
All statements concern the original infinite prime-sign probability law,
with both dyadic endpoints enforced and no BCN premise.

For centered coefficients the regular unions contribute zero, since their
actual pair rank loss is zero. Only the irregular full unions remain.
Their subpower count, the actual N^(-2+epsilon) point mass cap and exact
heterogeneous marginal caps prove the stronger bound

    sum_(exact-contact e) |c(e)| <= N^(-2+epsilon).

This improvement is specific to exact separation L. Strictly closer,
incompatible pairs can have negative centered coefficients and are not
included in that stronger exponent. It does not improve the already proved
N^(-1+epsilon) bound for all close-pair centered activity at arbitrary
fixed order. These positive-probability and exact covariance refinements
are recorded as improvement P1-MATH-0094. Main 6.3 stays proved; T7.1 and
T14.1 stay in progress. Coverage stays 77/167 (main 28/73, companion 49/94),
confirmed improvements 94. No full pair profile, multiplicative contact
probability equivalent, growing-order result, external premise, axiom,
dependency download, original-source change or Palomar registration is
introduced.

Verified under Lean v4.36.0-rc2: full lake build (10979 jobs), source and ledger checks, actual axiom audit of 6960 declarations (only propext, Classical.choice and Quot.sound), and 4677 direct ledger/evidence declaration checks; Ubuntu root free space 15.14 GiB. Original manuscript bytes and all 167 statement hashes preserved.


## The actual nonprivate fixed-channel activity

Every actual pair joint mass is now bounded by
p_nominal^2*2^(full pair loss), without regularity or affine compatibility.
The proof uses the complete actual tuple rank, including its zero-mass
branch, and the exact identity rank+full_loss=2L. Every fixed rational
channel a:b, a<b, now has individual actual joint and absolute centered
weights at most N^(-2+1/b+epsilon) on all exact-unit source pairs. The
uniform aligned residual rank theorem supplies the missing nonprivate
rank factor. Heterogeneous marginal caps retain irregular and zero sites.

For the literal badSources family whose normalized union is not private
above H, the already proved N^(1/2+epsilon) count therefore gives both
unordered joint mass and absolute centered activity at most

    N^(-3/2+1/b+epsilon),

uniformly for critical lengths and 2b(L+1)<=H<=D(L+1), with a,b,D fixed
before N. This is the normalized-defect contribution used in T7.1; for
b>=3 it is smaller than N^(-1+epsilon). No disjointness of normalization
representations is assumed: image sums are bounded by positive source
sums, retaining every probability-zero pair. The proof is unconditional.

T7.1 and main 3.3 stay in progress: the regular macroscopic nonaligned
sector, full rational-channel classification and complete signed pair
profile remain open. Coverage stays 77/167 (main 28/73, companion 49/94),
confirmed improvements 94. This checkpoint proves an existing source-scale
contribution and introduces no new mathematical correction, external
premise, axiom, dependency download, original-source change or Palomar
registration.

Verified under Lean v4.36.0-rc2: full lake build (10985 jobs), source and ledger checks, actual axiom audit of 6967 declarations (only propext, Classical.choice and Quot.sound), and 4684 direct ledger/evidence declaration checks; Ubuntu root free space 15.13 GiB. Original manuscript bytes and all 167 statement hashes preserved.


## The complete exact-unit channel tail up to height (L+1)^3

The channel weight bounds are now uniform simultaneously over all
reduced a:b with 0<a<b, b0<=b<=(L+1)^3, where only b0,C,epsilon are fixed
before the threshold. Actual joint and absolute centered weights of every
exact-unit pair are at most N^(-2+1/b0+epsilon), without BCN, private
normalizations or regular-site assumptions. The proof uses the genuinely
uniform aligned rank theorem; it does not take a growing maximum of
fixed-channel thresholds.

The literal unordered union over all these channels is constructed. A
finite weighted cover has cost at most 4(L+1)^8*N times a common pointwise
weight cap. It counts at most 4(L+1)^6 coefficient pairs and uses the
actual N(L+1)^2 source cover in each channel. Duplicate edge or source
representations require no disjointness assumption. The whole logarithmic
factor is absorbed only after these finite counts.
Consequently both joint mass and absolute centered activity of the full
exact-unit channel union are at most

    N^(-1+1/b0+epsilon).

For b0=3 this gives N^(-2/3+epsilon) over every channel of height up to
(L+1)^3. For b0=5 it proves the source residual N^(-4/5+epsilon) for the
entire exact-unit high-channel tail, including nonprivate and irregular
sources. The parameter varying with N here is the channel height, not the
number of windows or moment order.

This proves another source-scale part of main 3.3 and T7.1. It does not
identify all aligned pairs with exact-unit pairs, treat zero-unit enlarged
alignments, prove the macroscopic nonaligned sector, or complete the signed
pair profile. Main 3.3 and T7.1 stay in progress. Coverage stays 77/167
(main 28/73, companion 49/94), confirmed improvements 94. No new correction,
external premise, axiom, dependency download, original-source change or
Palomar registration is introduced.

Verified under Lean v4.36.0-rc2: full lake build (10991 jobs), source and ledger checks, actual axiom audit of 6975 declarations (only propext, Classical.choice and Quot.sound), and 4692 direct ledger/evidence declaration checks; Ubuntu root free space 15.12 GiB. Original manuscript bytes and all 167 statement hashes preserved.


## Full enlarged aligned tail with zero exact units

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
