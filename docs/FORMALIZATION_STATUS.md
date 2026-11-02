# Formalization status

Stage: **exact probability identities and uniform arithmetic foundations**, 2 November 2026.
Neither document is fully formalized.

- Baseline: P1 V1.6, 167 numbered results: main 73, companion 94.
- Numbered results completed: **73 / 167**: article Propositions 3.1, 4.1, 5.2, 6.2, 6.3, 9.1, 13.7, 19.2, Corollaries 9.2, 10.2, 10.3, Theorem 10.1 and Lemmas 2.1, 3.5, 4.2, 4.3, 4.4, 5.1, 6.1, 7.1, 7.2, 7.3, 7.4, 8.1, 14.2; companion Lemmas T1.1, T1.2, T1.3, T1.6, T1.9, T1.11, T2.5, T2.6, T9.1, T9.2, T9.3, T9.4, T12.1, T12.2, T19.1, T22.2 and Propositions T1.15, T19.2, T19.5, T19.6, T19.7, T19.9, T19.12, T20.3, T22.4, T23.1, together with Proposition T9.5, Lemmas T19.8, T19.11, T19.13, T2.1, T2.2, T4.1, T4.2, T20.1, T20.2, T20.5, T20.7, T21.2, T21.3, T22.3 and Corollary T2.3, and Lemmas T5.2, T6.1, T6.2, T6.3, and Propositions T1.14 and T22.7.
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
- The project currently has **5593 audited theorem/lemma declarations**. This
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
  Unproved literature propositions encoded as assumptions: none.
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
