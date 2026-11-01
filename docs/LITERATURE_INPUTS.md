# External mathematical inputs

No literature proposition is currently encoded as an unproved assumption in the
Lean development. The arithmetic and analytic input inventory is **not complete**.
The paper's claims of unconditionality remain manuscript claims until their
inputs and proofs have been accounted for.

For each later input record: stable ID, exact reference and locator, full
statement, coefficient and degree dependence, quantifier order, uniformity,
Lean type, uses, and status (`proved`, `mathlib`, `explicit_hypothesis`, or
`unresolved`). Include the exact upstream commit for Mathlib results.

If a literature result is intentionally left unformalized, pass it as an
ordinary explicit theorem argument and state that conditional scope in the
coverage and Palomar metadata. Do not introduce a global `axiom`, and do not
describe a theorem conditional on an external estimate as having proved it.

Start with the cited sources behind the split-product, quadratic-equation,
determinant and local rigidity bounds in companion T1 and article Section 2.
Compare the stronger uniformity required here with the exact interfaces in
Paper C; importing an old interface alone cannot discharge this comparison.

## Fixed-window exposure and full-vector independence

Stable ID: `P1-ARITH-FIXED-WINDOW-BRANCHING`. Status: **proved**, complete T1.15.

- The entire actual new relative vector has its fair product law and
  Mathlib `IndepFun` from all old raw values whenever its supported-value
  count is at most one. Every conditional word mass and the literal
  joint pushforward are proved; unrealizable old vectors have zero mass.
- Finite prime-cardinality and positive-integer reciprocal-half-power
  bounds prove the source explicit rounded exceptional estimate. A
  smaller deterministic set removes the contact term and halves the
  pool coefficient, as recorded in P1-MATH-0030. The actual critical
  prime-pool count proves the uniform fixed-j exponent.
- No independence, conditional word law, prime-cardinality, Euler or
  exceptional-count estimate is assumed. Injective complete-boundary
  embeddings and transposes prove the exact laws of all selected subsets
  and fitted positive fixed dilations. Arbitrary bounded old observations,
  fixed enlarged logarithmic widths, positive height multiples and
  injective center reindexings are included, with thresholds before all
  such choices. No additional Paper C source or unproved literature
  statement is introduced. See
  [alignment](FIXED_BRANCHING_ALIGNMENT.md).

## Conditional rank after old raw observations

Stable ID: `P1-ARITH-CONDITIONAL-RANK`. Status: **proved**, complete T21.2.

- The actual old square-class span and prime pool are constructed.
  Private new prime coordinates restrict the relative kernel to the
  supported even space, giving rho<=(t-1)_+.
- The complete boundary equivalence and injective character pairing
  preserve that kernel. Finite affine counting and annihilator duality
  prove the exact conditional laws, including all incompatible targets
  and realizability when rho=0. Original infinite-model old and joint
  probabilities are transported, with a proved positive denominator.
- The original conditional Bochner expectation is the sum of the exact
  conditional probabilities. A finite incidence budget proves the source
  conditional mean bound and the sharper coefficient P1-MATH-0029.
- Actual old windows supply a finite logarithmic prime-pool budget
  O_j((log N)^2). The proved prime-budget Euler bound and squares give
  matching N^(1/2+o(1)) pool size. Exact critical binary factors and
  integer floors give both sides of the source final term's logarithmic
  scale, uniformly over every old-window choice and all critical lengths.
- No rank, compatibility, conditional probability, incidence, Euler or
  asymptotic estimate is supplied as a target premise. No new Paper C
  code or unproved literature input is introduced. See
  [alignment](CONDITIONAL_RANK_ALIGNMENT.md).

## Rare arithmetic cylinder and exponential-moment divergence

Stable ID: `P1-ARITH-PRIME-CYLINDER-DIVERGENCE`. Status: **proved**.

- Target: companion Proposition T19.7, page 71, `p1:limits:cylinder`.
- Lean: `PrimeCylinderLiminf.companion_T19_7_liminf` and the explicit
  threshold formulation `PrimeCylinderDivergence.companion_T19_7`.
- Elementary prime-valuation arithmetic constructs actual positive runs;
  residue-class counts give a finite lower bound for their number.
  Exact finite-cylinder probability and expectation transfer give lower
  bounds for the original infinite-model exponential moments.
- The already formalized sharp PNT proves the scaled cylinder cost limit.
  Elementary real limits prove the start contribution. Mathlib's
  infinitude-of-primes theorem proves that the odd-prime filter is
  nontrivial. The literal extended-real liminf and divergence above
  every real level follow. No probability or asymptotic estimate is
  assumed; the sufficient source threshold t>2 is retained.
- No new Paper C code or unproved literature statement is introduced.
  The three additional Paper C Stein-related modules inspected at this
  checkpoint are recorded as **not ported** in `PAPER_C_REUSE.md`.
  Their explicit positive-rate input is not treated as a closed proof.
  See [alignment](PRIME_CYLINDER_ALIGNMENT.md).

## Private-rank deletion and positive core components

Stable ID: `P1-AFFINE-PRIVATE-RANK-PEELING`. Status: **proved**.

- Target: every conclusion of companion Lemma T19.8, page 71,
  `p1:limits:peeling`.
- Lean: `PrivateRankPeelingTheorem.companion_T19_8`.
- A terminal deletion trace is constructed. The actual rank decrease
  proves the deletion budget for every trace. Exact erased-kernel counts
  give the full-support lower bound; a common solution proves the
  compatible Fourier phases and preserves the original affine moments.
- The already constructed canonical direct partition is used. Rank
  additivity on every restriction preserves private ranks within parts,
  and a finite weighted average supplies the dense component and all
  source size and nullity bounds. No target rank, probability or component
  estimate is a hypothesis. The finite improvement is P1-MATH-0028.
- No new Paper C source or unproved literature statement is introduced.
  Mathlib at the pinned revision supplies finite-dimensional linear
  algebra and finite sums. See
  [alignment](PRIVATE_RANK_PEELING_ALIGNMENT.md).

## Exact local blocks and the original Bernoulli laws

Stable ID: `P1-ARITH-EXACT-LOCAL-BLOCKS`. Status: **proved**.

- Target: every conclusion of companion Proposition T19.2, page 67,
  `p1:limits:local-blocks`.
- Lean: `LocalBlocksTheorem.companion_T19_2`; the finite formulation is
  `finite_conclusion`. The actual square-product population is identified
  by `LocalRelationBlocks.mem_relations_iff_square_product`.
- The already proved critical rank-one theorem supplies local uniqueness.
  Physical set encodings, interval geometry, the predecessor Fourier phase,
  actual Bernoulli pushforward laws and all finite sum identities are
  proved internally. Deterministic separation supplies the count support;
  no independence between blocks is assumed.
- At most two endpoint truncations give the original correction. The
  nonempty clipped-block improvement is recorded in P1-MATH-0027.
  There is no assumed Fourier phase, probability or endpoint estimate.
- No new Paper C source is ported and no unproved literature proposition
  is added. Mathlib at the pinned revision supplies finite sums, linear
  algebra, integer intervals and elementary real arithmetic. See
  [alignment](LOCAL_BLOCKS_ALIGNMENT.md).

## Forced offset planes and their original affine mass

Stable ID: `P1-ARITH-OFFSET-FORCED-PLANE`. Status: **proved**.

- Target: the complete companion Proposition T20.3, page 82,
  `p1:offset:forced-plane`.
- Lean: `OffsetPlaneTheorem.companion_T20_3_shared` and its stronger
  generic divisibility version `uniform_stronger`.
- The actual shared odd-valuation population and canonical offsets are
  constructed. Integer determinant and cross-product identities give
  the source thresholds and coefficient heights. Actual square-class
  projection rigidity gives all three nonzero normal coordinates.
- Distinct actual real plane sets have at most N common integer centers
  in the dyadic cube, proved by an injective coordinate projection.
  The finite plane family is constructed from physical offsets.
- Exact affine probabilities and joint-activation antitonicity prove
  the p^2 bound, including incompatible systems. The ordered primitive
  triple mass is a nonnegative subsum of a larger actual population.
  Fixed logarithmic-polynomial bounds give the uniform critical-band
  estimate. No target mass, determinant or point-count bound is assumed.
- No new Paper C source is ported and no unproved literature statement
  is added. Mathlib at the pinned revision supplies finite counting,
  linear algebra, integer arithmetic, real powers and logarithms. See
  [alignment](OFFSET_PLANE_ALIGNMENT.md) and P1-MATH-0026.

## Whole prime products and offset counts on a line

Stable ID: `P1-ARITH-OFFSET-LINE-PRODUCT`. Status: **proved**.

- Target: all conclusions of companion T20.1, page 82,
  `p1:offset:line-product`.
- Lean: `OffsetLineTheorem.companion_T20_1`, with the original three-
  regular-window specialization and all uniform logarithmic conclusions.
- The actual prime pool has an exact source-membership iff. Above H>=B,
  every prime has one physical offset per window, and the chosen point
  population is proved equal to all actual odd-valuation occurrences.
  Integer collinearity is explicitly bridged from real affine lines.
- Bezout identities construct the primitive direction and all lattice
  parameters. Every prime divides a common integer minor; actual square
  classes prove some minor is nonzero. Its exact value bound gives the
  whole prime-product estimate, not an assumed geometric count.
- Logarithms of the actual product give the finite distinct-offset bound.
  Critical-band scales and elementary logarithmic limits give the uniform
  O(B/logB) and o(B) statements. No determinant estimate or prime-density
  theorem is needed. No additional Paper C source is ported.
- Mathlib at the pinned revision supplies integer gcd/Bezout, finite
  products, prime divisibility and real logarithms. See
  [alignment](OFFSET_LINE_PRODUCT_ALIGNMENT.md), P1-MATH-0024 and
  P1-MATH-0025 for the precisely delimited improvements.

## Norms of actual Poisson differences

Stable ID: `P1-PROB-POISSON-DIFFERENCE-NORMS`. Status: **proved**.

- Target: all three conclusions of article Proposition 19.2, page 58,
  `p1:discussion:charlier-norm`.
- Lean: `PoissonSecondDifferenceNorm.main_19_2`, with actual signed
  measures, exact floor/ceiling endpoints, negative-index zero convention,
  and every natural difference order including zero.
- The original cited Charlier orthogonality bound is not left as an
  external input. Exact factorial moments of the signed difference and a
  finite coefficient sum prove the required diagonal square identity.
  An elementary summed quadratic inequality proves the square-root bound.
- The second-difference sign interval and its nonemptiness are proved
  algebraically; a finite telescoping identity gives the exact norm.
  The source constants at mean two are evaluated symbolically.
- Mathlib at the pinned revision supplies Poisson masses, finite sums,
  HasSum operations, real square roots, floor/ceiling and signed measures.
  No additional Paper C source is ported.
- See [alignment](POISSON_DIFFERENCE_NORMS_ALIGNMENT.md) and P1-MATH-0023
  for the separately strengthened unnumbered lower coefficient bound.

## Marked-isolate graph generating function

Stable ID: `P1-COMB-MARKED-GENERATOR`. Status: **proved**.

- Target: article Lemma 7.4, page 24, `p1:core:generator`.
- Lean: `MarkedGraphGenerator.main_7_4`, with the exact admissible family,
  nonnegative activity and actual finite-graph maximum degree.
- A minimal finite singleton/edge cover has a private vertex in each
  member. Choosing these as leaves partitions the covered set into
  disjoint graph stars and marked singletons. Existence, disjointness,
  exact covering and graph incidences are proved internally.
- A finite polymer sum/product comparison and the powerset generating
  identity give the stronger star bounds. An elementary proved Mathlib
  exponential inequality implies the original rational conclusion.
- No connected-set enumeration, spanning-tree count or cluster estimate
  is an unproved input. No additional Paper C source is ported. Mathlib
  at the pinned revision supplies finite sets, products and exponentials.
- See [alignment](MARKED_GENERATOR_ALIGNMENT.md) and P1-MATH-0022 for
  all-activity, degree-profile and heterogeneous-weight improvements.

## Incoming and outgoing saturation degrees

Stable ID: `P1-ARITH-SATURATION-DEGREES`. Status: **proved**.

- Target: article Lemma 7.3, page 24, `p1:core:degrees`.
- Lean: `SaturationDegrees.main_7_3`, including both directed degrees and
  the maximum degree of the actual finite symmetrized graph.
- Actual anchor kernels and receiver prime pools have internally proved
  product and cardinality budgets. Bounded prime subsets and offset
  assignments enumerate all qualifying congruence certificates. Each
  product at least N fixes at most one center in the interval of N points.
- A finite powerset generating identity gives the explicit incoming bound
  without an assumed binomial estimate or an extra large-N size condition.
  The exact growing ceiling and logarithmic limits give the uniform power.
- No prime estimate beyond the internally proved product budget is used.
  Mathlib at the pinned revision supplies finite powersets, products,
  elementary exponential inequalities and finite simple graph definitions.
  No additional Paper C source is ported.
- See [alignment](SATURATION_DEGREES_ALIGNMENT.md) and P1-MATH-0021 for the
  separately verified lower threshold. It concerns the degree bounds only.

## Moderate congruence certificates — both conclusions proved

Stable ID: `P1-ARITH-MODERATE-CERTIFICATES`. Status: **proved**.

- Target: article Lemma 7.2, page 23, `p1:core:moderate`.
- Lean: `ModerateCertificateAsymptotic.main_7_2`, retaining both original
  conclusions and the exact growing-order quantifiers.
- Actual truncated kernels, prime supports, squarefreeness, coprimality,
  product bounds, all assignments and receiver congruences give the exact
  finite count. The source population has an explicit membership theorem.
- Distinct centres make the weighted population empty above order N.
  The proved exponential-series estimate gives its exact finite-parameter
  majorant. The literal ceiling order satisfies m*loglogN/logN -> 2/A;
  the factorial budget and bounded nominal mean give the weighted power.
- Mathlib at the pinned revision supplies finite products, prime factors,
  logarithms, factorial bounds, exponentials and filter limits. No external
  estimate is assumed and no additional Paper C source is ported.
- The full build and actual audit validate both conclusions. See
  [alignment](MODERATE_CERTIFICATE_ALIGNMENT.md) and P1-MATH-0020 for the
  precisely delimited stronger parameter ranges.

## Root separation on a rational offset line

Stable ID: `P1-ARITH-OFFSET-ROOT-SEPARATION`. Status: **proved**.

- Target: both conclusions of companion T20.5, page 83,
  `p1:offset:root-separation`.
- Lean: `OffsetRootPolynomials.companion_T20_5`, and stronger
  `root_separation` requiring only first-window regularity.
- The arithmetic argument uses actual parity vectors and even-selection
  maps. Regular rank is proved to imply the needed injectivity.
  Proportional positive pairs give a common nonzero even square class,
  contradicting the assumed directness of the actual source spaces.
- The rational root identities and exceptional-coordinate construction are
  proved. A finite injection bounds the number of disjoint equation
  supports touched by that set. The exact substituted products are shown
  squarefree with pairwise disjoint roots.
- Mathlib at the pinned revision supplies linear-map rank-nullity,
  finite sums and the separability of products of distinct linear factors.
  No root-count or polynomial-squarefreeness conclusion is assumed.
- No additional Paper C source is ported. `P1-MATH-0019` records the weaker
  regularity assumption. See [alignment](OFFSET_ROOT_SEPARATION_ALIGNMENT.md).

## Product certificates with fixed source windows

Stable ID: `P1-ARITH-FIXED-SOURCE-PRODUCT-CERTIFICATE`. Status: **proved**.

- Target: companion T4.2, page 27, `p1:fixed:CRT`.
- Lean: `UniformFixedSourceCertificates.companion_T4_2`, with a stronger
  upper-width and non-strict product version in
  `certificateTargets_le_power_eventually`.
- The actual source and target values, signed-offset dictionary, finite
  certificate alphabet, code count, coprime congruence combination and
  uniqueness in a half-open interval are all proved. No CRT conclusion
  or candidate population is assumed as an external input.
- The existing proved `DivisorSubpolynomial.card_divisors_le_rpow_eventually`
  applies uniformly to every source value. Existing logarithmic-width
  subpolynomiality supplies the remaining position factor. No divisor
  asymptotic is left as a hypothesis.
- Mathlib at the pinned revision supplies natural divisors, the finite lcm
  and its equality with the coprime product, finite function counts and
  real-power algebra. No additional Paper C source is ported.
- `P1-MATH-0018` records the relaxed product threshold and width condition.
  See [alignment](FIXED_SOURCE_PRODUCT_CERTIFICATE_ALIGNMENT.md).

## Weighted offset-pattern counts

Stable ID: `P1-ARITH-OFFSET-PATTERN-RANKIN`. Status: **proved**.

- Target: both conclusions of companion T21.3, page 88,
  `p1:consequences:rankin-patterns`.
- Lean: `OffsetPatternRankin.companion_T21_3`; explicit broader versions
  are `prime_patterns_explicit` and `integer_patterns_explicit`.
- Actual squarefree values map injectively to their prime-factor supports.
  The integer support population is proved exhaustive for every finite
  support above the threshold and below the product cutoff. Both source
  weights are identified exactly, including the empty support/product one.
- Finite Rankin is proved from actual product inequalities. Clipping the
  decreasing power weight lets finite Abel comparison and the proved
  primorial bound control prime tails, with the logarithmic saving. Arbitrary
  integer tails use the previously proved p-series integral comparison.
- Mathlib at the pinned revision supplies prime-factor reconstruction for
  squarefree integers, finite products and real-power identities. No prime
  tail, product count or external asymptotic estimate is an assumption.
- No additional Paper C source is ported. `P1-MATH-0017` records the wider
  parameter ranges with their precise constant dependence. See
  [alignment](OFFSET_PATTERN_RANKIN_ALIGNMENT.md).

## An arbitrary prime set under a logarithmic budget

Stable ID: `P1-ARITH-LOGARITHMIC-PRIME-BUDGET`. Status: **proved**.

- Target: both conclusions of companion T22.3, page 90,
  `p1:uniform:prime-budget`.
- Lean: `PrimeBudgetRankin.companion_T22_3`, `source_uniform_log_bound`,
  and stronger `log_values_le`; the actual integer population is
  `SmoothSquarefreeCount.values`.
- A finite square-root fibre argument proves the Euler-product count.
  The convergent positive-integer series defining zeta(2*sigma) is retained
  in the source corollary; its lower bound one is proved.
- The primorial bound gives every initial logarithmic prime sum.
  Mathlib's finite Abel comparison gives the power-weighted sum, and a
  fixed 1/8 logarithmic loss proves a common bound for all exponents in
  [0,3/4]. Splitting the given prime set at Y then uses its actual budget.
- Mathlib at the pinned revision supplies finite Abel comparison, real-power
  and logarithm identities, p-series summability and finite product algebra.
  No PNT, prime partial-summation estimate or zeta upper bound is assumed.
- `P1-MATH-0016` records the stronger finite constant and uniform range.
  No additional Paper C file is ported. See
  [alignment](LOGARITHMIC_PRIME_BUDGET_ALIGNMENT.md).

## Small truncated odd-prime kernels

Stable ID: `P1-ARITH-RANKIN-SMALL-KERNEL`. Status: **proved**.

- Target: article Lemma 7.1, page 23, `p1:core:rankin`; full elementary proof
  in companion `p14:comp:certificate-rankin`.
- Lean: `RankinSmallKernel.main_7_1`, with explicit constants and the stronger
  endpoint in `main_7_1_explicit` and `rankin_half`.
- The actual odd-prime kernel, small-prime support and square part are
  constructed from valuations. Their decomposition gives a finite cover.
  Finite square-root fibre bounds, finite reciprocal-power sums and the exact
  Euler product are proved. No zeta estimate or prime asymptotic is required.
- Mathlib supplies real powers, the interval integral of a real power,
  sum-integral comparison and finite product identities, at the pinned
  revision. No target count or analytic estimate is an assumed proposition.
- Three elementary comparison proofs are adapted from Paper C's exact
  `PaperCV11/RankinTilt.lean` blob
  `0e160cd09e337d5b6142c75524a2da9da7ec5584`, snapshot
  `b9fa9ba490f201b408a302a86f1594ee620b228b`, Apache-2.0. They were rebuilt
  and included in the actual Lean 4.36.0-rc2 axiom audit.
- `P1-MATH-0015` records sigma=1/2 and the explicit constants. See
  [alignment](RANKIN_SMALL_KERNEL_ALIGNMENT.md).

## Disjoint recovery — complete internal proof

Stable ID: `P1-LINALG-DISJOINT-RECOVERY`. Status: **proved**.

- Target: full article Lemma 6.1, page 21, `p1:fixed:recovery`.
- Lean: `DisjointRecoveryTheorem.main_6_1` is the literal binary coordinate
  specialization. `disjoint_recovery` proves the whole lemma over every field
  for any finite family of linear forms on a finite-dimensional space.
- Finite Bernoulli weights, exact joint recovery and failure probabilities,
  pointwise sequential rank budget, maximal stopping history and the literal
  sampling parameter are proved internally. No determinant or arithmetic
  literature estimate is an input.
- The last representation count is proved by a finite maximal disjoint family,
  its explicit transversal and an erase recursion. Disjoint label supports
  lift injectively to physical coordinate supports before recovery exclusion
  is applied. Linear independence implies the zero-sum-free property used in
  the more general counting lemma; no representation bound is assumed.
- Mathlib at commit `9d581dfff2e41de989072ea63abf3daf69311520` supplies finite
  product expansion, Bernoulli's inequality, finite-dimensional rank and dual
  annihilator/restriction identities. All remaining combinatorial arguments
  are proved in this project.
- The field/family extension is `P1-MATH-0013`; the sharper representation
  bound and zero-sum-free extension are `P1-MATH-0014`. See
  [alignment](DISJOINT_RECOVERY_ALIGNMENT.md).

## Constraints on at most three coordinates

Stable ID: `P1-LINALG-TERNARY-CONSTRAINTS`. Status: **proved**.

- Target: companion T2.3, page 21, `p1:arith:ternary-degree`.
- Lean: `TernaryConstraints.companion_T2_3`, its sharper bound and the
  existence wrapper constructing the actual regularized subspace via T2.2.
- All row restrictions, zero-coordinate deletions, repeated-support images,
  row classifications, graph-walk identities and unordered incidence covers
  are proved internally. The stronger constant is `P1-MATH-0012`.
- Mathlib at commit `9d581dfff2e41de989072ea63abf3daf69311520` supplies finite
  set product/image cardinalities and actual simple-graph walks. No degree,
  connected-component or regularization output is an unproved input.
- No further Paper C proof is ported. See
  [complete alignment](TERNARY_CONSTRAINTS_ALIGNMENT.md).

## Coordinate regularisation

Stable ID: `P1-LINALG-COORDINATE-REGULARISATION`. Status: **proved**.

- Target: companion T2.2, page 20, `p1:arith:coordinate-regularisation`.
- Lean: `CoordinateForms.companion_T2_2` and its stronger active-budget form.
- The selected coordinate kernels, exact codimension, two-element unordered
  decompositions, disjoint collisions, finite potential and stopping argument
  are proved internally, as is dimension preservation after deleting zero forms.
- Mathlib at commit `9d581dfff2e41de989072ea63abf3daf69311520` supplies
  `Module.Dual.finrank_ker_add_one_of_ne_zero`, injective finite-dimensional
  rank comparison, dual restriction and finite maxima. No coordinate
  regularisation theorem, loss bound or algorithmic output is assumed.
- The stronger initial active count and zero boundary parameters form
  `P1-MATH-0011`. No further Paper C proof is ported. See
  [complete alignment](COORDINATE_REGULARISATION_ALIGNMENT.md).

## Integer product tail

Stable ID: `P1-ANALYSIS-INTEGER-PRODUCT-TAIL`. Status: **proved**.

- Target: companion T20.2, page 82, `p1:offset:integer-tail`.
- Lean: `IntegerProductTail.companion_T20_2` with exact strict product cutoff,
  absolute convergence, and one explicit positive constant before all T>=1.
- Mathlib at commit `9d581dfff2e41de989072ea63abf3daf69311520` supplies
  `Real.summable_nat_rpow`, `AntitoneOn.tsum_comp_add_le_integral`,
  `integrableOn_Ioi_rpow_of_lt`, `integral_Ioi_rpow_of_lt`, and
  `harmonic_floor_le_one_add_log`. The one-dimensional tail, floor control,
  product decomposition and final logarithmic estimate are proved internally.
- No p-series tail estimate, target bound or unformalized literature input is
  passed as a premise. No additional Paper C proof is ported. See
  [complete alignment](INTEGER_PRODUCT_TAIL_ALIGNMENT.md).

## Small-prime coefficient budget

Stable ID: `P1-ARITH-SMALL-PRIME-BUDGET`. Status: **proved**.

- Target: companion T2.1, page 20, `p1:arith:smallpart-budget`.
- Lean: `SmallPrimeBudget.companion_T2_1`, including both the logarithmic
  sum and the exact exceptional-value count for every real A>0.
- The exact small odd-prime product, its sf/K identity, translated multiple
  count and factorial-valuation comparison are proved internally.
- Mathlib at commit `9d581dfff2e41de989072ea63abf3daf69311520` supplies
  `Nat.card_multiples`, `Nat.factorization_prod_apply`,
  `Nat.Prime.dvd_factorial`, `Real.log_nat_eq_sum_factorization`, and
  `primorial_le_four_pow`. These proved elementary facts give the explicit
  absolute remainder (log 4)B. No PNT or unformalized Chebyshev estimate
  is assumed. No additional Paper C proof is ported.
- See [complete alignment](SMALL_PRIME_BUDGET_ALIGNMENT.md). No new
  mathematical change entry is introduced for this verification.

## Weighted recurrence comparison and stability

Stable ID: `P1-PROB-WEIGHTED-RECURRENCE`. Status: **proved**.

- Target: companion T19.13, page 77, `p1:limits:weighted-residual`.
- Lean: `WeightedPoissonNorm.companion_T19_13` and
  `weightedNorm_stability_bounded`, with a stronger all-real stability form.
- The recurrence solution, factorial kernel bound, absolute convergence of
  its double series, antidiagonal regrouping and mass-zero norm estimate are
  proved internally. There is no first-moment premise or external Stein or
  recurrence comparison theorem.
- Mathlib at commit `9d581dfff2e41de989072ea63abf3daf69311520` supplies
  `NormedSpace.expSeries_div_hasSum_exp`,
  `Nat.factorial_mul_factorial_dvd_factorial_add`, the finite-antidiagonal
  equivalence, summable-series operations and actual countable probability
  masses. The Poisson reference is the actual Mathlib Poisson measure.
- The weaker parameter hypotheses form `P1-MATH-0010`. See
  [complete alignment](WEIGHTED_POISSON_NORM_ALIGNMENT.md).

## Exact positive moment perturbation

Stable ID: `P1-PROB-MOMENT-OBSTRUCTION`. Status: **proved**.

- Target: companion T23.1, page 93, `p1:obstruction:fixed`.
- Lean: `MomentObstruction.companion_T23_1` and its extended-interval form.
  These construct actual probability measures and identify the full signed
  perturbation, all factorial moments and the exact total variation scale.
- The proof uses internal exact finite-difference and coefficient identities,
  the already proved quadratic Poisson positivity and integer minimum, and
  the elementary exponential series at Mathlib commit
  `9d581dfff2e41de989072ea63abf3daf69311520`.
  `NormedSpace.expSeries_div_hasSum_exp`, `Real.pow_div_factorial_le_exp`
  (`Analysis/Complex/Exponential.lean`), binomial-factorial identities and
  `Nat.sum_range_choose` supply the proved library facts. Actual integrations
  use countable Dirac sums; integrability is proved by exponential domination.
- No fixed-moment equality, positivity, coefficient pattern, norm constant
  or moment bound is a theorem premise. The parameter extension is
  `P1-MATH-0009`. See [alignment](MOMENT_OBSTRUCTION_ALIGNMENT.md).
- The following unnumbered continuation is now proved separately by closed
  Poisson factorial sums, `Stirling.le_log_factorial_stirling` from
  `Analysis/SpecialFunctions/Stirling.lean`, the exact floor estimate, and
  `isLittleO_log_rpow_atTop` from `Analysis/SpecialFunctions/Pow/Asymptotics.lean`.
  Its actual probability family, literal parameters, fixed-order equalities,
  logarithmic error and strict comparison with every polynomial rate are
  all checked. No external asymptotic estimate is assumed. See
  [complete alignment](MOMENT_OBSTRUCTION_ASYMPTOTICS.md).

## Complete signed Palm identity

Stable ID: `P1-PROB-SIGNED-PALM`. Status: **proved**.

- Target: companion T19.12, page 76, `p1:limits:signed-palm`.
- Lean: `MeasureSignedPalm.companion_T19_12`, with exact conditional-law
  coefficients, raw recurrence norm, actual means and joint Bochner moments.
- The proof is internal finite probability and polynomial algebra, then
  exact transport through the finite indicator observation. The elementary
  source deletion, size-bias identity, translation isometry, diagonal
  coupling error and all signed coefficients are proved, not assumed.
- Mathlib at commit `9d581dfff2e41de989072ea63abf3daf69311520` supplies the
  additive monoid algebra lift (`Algebra/MonoidAlgebra/Lift.lean`), polynomial
  product differentiation and coefficient identities
  (`Algebra/Polynomial/Derivative.lean` and `Coeff.lean`), finite-support
  countable sums, and standard Bochner integration of indicators and finite
  observations. No literature estimate, Stein solution bound or model Palm
  cost is an input.
- Both the original heterogeneous statement and the equal-marginal formula
  are proved. See [complete alignment](SIGNED_PALM_ALIGNMENT.md).

## Exact quadratic Poisson positivity

Stable ID: `P1-ANALYSIS-POISSON-POSITIVITY`. Status: **proved**.

- Target: article Lemma 8.1, page 25, `p1:close:positivity`.
- Lean: `QuadraticPoisson.main_8_1_fract`, `reference_singleton`,
  `reference_total_mass`, `reference_eq_poisson_plus_secondDifference`.
- Mathlib at commit `9d581dfff2e41de989072ea63abf3daf69311520` supplies
  `ProbabilityTheory.hasSum_one_poissonMeasure`, its actual `poissonMeasure`
  and singleton formula in `Probability/Distributions/Poisson/Basic.lean`.
  The countable density construction is
  `Measure.withDensityᵥ` in `MeasureTheory/VectorMeasure/WithDensity.lean`;
  `integrable_count_iff` and `Summable.norm` prove its actual integrability.
  Countable integration and disjoint-union additivity identify the signed
  measure on every set from its singleton masses.
- The exact integer quadratic minimum, the negative-α obstruction, and both
  directions of the parameter criterion are proved internally. No source
  positivity claim or asymptotic parameter estimate is an input.
- See [complete alignment](QUADRATIC_POISSON_ALIGNMENT.md). No mathematical
  change entry is added for this verification of the original statement.

## Proved exact bivariate factor height

Stable ID: `P1-ARITH-BIVARIATE-HEIGHT`. Status: **proved**.

- Target: companion T9.4, page 41, `p13:rig:factor-height`.
- Every nonzero integer product P=Q R satisfies the exact source bounds for
  both H(Q) and H(R); primitivity is unnecessary (`P1-MATH-0008`).
- Lean: `BivariateFactorHeight.companion_T9_4_factor_and_quotient`.
- Mathlib inputs at commit `9d581dfff2e41de989072ea63abf3daf69311520`:
  `Polynomial.norm_coeff_le_choose_mul_mahlerMeasure`,
  `Polynomial.leadingCoeff_le_mahlerMeasure`, `Polynomial.mahlerMeasure_mul`,
  and `Polynomial.mahlerMeasure_le_sqrt_sum_sq_norm_coeff`, in
  `Analysis/Polynomial/MahlerMeasure.lean`; the exact Parseval identity
  `Polynomial.sum_sq_norm_coeff_eq_circleAverage` in
  `Analysis/Polynomial/Fourier.lean`; the circle-average integration rules.
  All are actual proved library results, not ordinary theorem premises.
- The elementary integer-leading-coefficient proof of Mahler measure at
  least one is given locally. It is the same standard argument behind
  Mathlib's `Polynomial.one_le_mahlerMeasure_of_ne_zero`, without importing
  the latter file's additional cyclotomic and number-field dependencies.
- Partial degrees, coefficient height, finite support and both integer
  factors are handled explicitly. No multivariate Mahler or Jensen theorem
  is assumed. See [complete alignment](BIVARIATE_FACTOR_HEIGHT_ALIGNMENT.md).

## Proved split-product bound

Stable ID: `P1-ARITH-SPLIT`. Status: **proved**.

- Target: companion T1.1, `p1:arith:runge`, page 5,
  `companion_sections/arithmetic_appendix.tex:19`.
- Scope: every `d = 2k ≥ 2`, real `R ≥ 1`, distinct integer shifts bounded
  in absolute value by R, integer `U ≥ 2R`, and an integer-square product.
  Conclusion `U ≤ (64R)^d`, with an absolute constant independent of degree.
- Lean theorem: `PaperP1.SplitProductBound.uniform_split_product_real_radius`.
- Inputs: proved finite binomial/formal-series identities, integral
  coefficient scaling, cancellation, integer-square separation, and the
  integral-polynomial root height bound. Exact Paper C source identities
  are recorded in the reuse ledger. Mathlib's compiled Cauchy root bound
  (`Polynomial.IsRoot.norm_lt_cauchyBound`,
  `Analysis/Polynomial/CauchyBound.lean`) is used at Mathlib commit
  `9d581dfff2e41de989072ea63abf3daf69311520`.
- The manuscript cites Munsch et al., Lemma 3.3, for the antecedent fixed-degree
  argument. No proposition from that reference is assumed by the Lean proof;
  the cited paper's statement has not been used to discharge a proof obligation.
- Degree dependence is fully explicit in the intermediate height estimate.
  This resolves T1.1 itself. The quadratic-equation count is resolved below;
  the determinant and local-rigidity inputs are separate
  obligations.

## Proved coefficient-uniform quadratic count

Stable ID: `P1-ARITH-PELL`. Status: **proved**.

- Target: companion T1.2, `p1:arith:pell`, page 5,
  `companion_sections/arithmetic_appendix.tex:62`.
- Quantifiers: for each fixed real A₀ > 0 and ε > 0, there exists N₀; for
  every N ≥ N₀ and every positive A,C and nonzero e with
  A,C,|e| ≤ N^A₀, the exact positive-solution count in the N^A₀ box is ≤ N^ε.
- Lean theorem: `PaperP1.UniformQuadraticCount.uniform_quadratic_equation_count`.
  Its exact floor-height membership equivalence is separately proved.
- Source comparison: [Tao, arXiv:2603.27990v3](https://arxiv.org/html/2603.27990v3),
  §2.5, Lemma 2.10 and proof; [Cilleruelo–Garaev,
  arXiv:1007.1526v2](https://arxiv.org/pdf/1007.1526v2), §3, Lemma 4 and
  Proposition 1. The primary statements and the polynomial-height substitution
  were inspected. See [exact alignment](QUADRATIC_COUNT_ALIGNMENT.md).
- Proof inputs: internally proved finite ideal-divisor and unit-orbit bounds,
  squarefree reduction, conductor descent, and elementary divisor
  subpolynomiality. Exact Paper C blobs are recorded in the reuse ledger.
  Standard quadratic-field, ideal-factorization, trace/norm and Pell-unit
  facts come from compiled Mathlib at
  `9d581dfff2e41de989072ea63abf3daf69311520`.
- No theorem from either cited paper is an unproved premise. No
  Nicolas–Robin estimate, fixed-discriminant constant, squarefree coefficient
  assumption or class-number bound remains in the final statement. The
  determinant estimate remains open. T1.3 and the complete local-rigidity
  specialization are proved below.

## Proved defect-count ingredients

Stable ID: `P1-ARITH-DEFECT`. Status: **proved**, full companion T1.3,
`p1:arith:defects`, page 6, `companion_sections/arithmetic_appendix.tex:90`.

The finite Chebyshev estimate and
weighted defect/Euler-product estimates are ported from exact Paper C sources,
with no literature assumption. Mathlib's `primorial_le_four_pow`
(`NumberTheory/Primorial.lean`) is a proved library input at the pinned
commit. The new global theorem
`PaperP1.GlobalDefectCount.global_defect_count_le_rpow_eventually` proves the
actual positive-set count ≤ N^(1/2+ε), with a threshold before all H,X in the
stated logarithmic/linear ranges. The two-defect count is now also proved by
explicit finite configurations and the proved T1.2 theorem. The new uniform
prime-support estimate, polynomial support heights and exact dyadic-window
reindexing are proved in P1, with no new literature assumption. See
[two-defect alignment](TWO_DEFECT_ALIGNMENT.md) and
[complete statement alignment](DEFECT_COUNTS_ALIGNMENT.md). The new uniform
prime budget and B/log B conversion prove the full local rate. Exact positive
integer-point definitions, rounded endpoint bounds and injective shifted
starts prove the fixed real affine versions. The complete
`UniformDefectCounts.companion_T1_3_run_length` and
`companion_T1_3_run_length_fixed_affine` declarations choose the local
constant before the error exponent and a common threshold before every
cutoff, interval and length. No arithmetic estimate is an unproved premise.

## Local rigidity: proved code bound and sharp prime asymptotic

Stable ID: `P1-CODE-GRIESMER`. Status: **proved**.
Reference: J. H. Griesmer, *A Bound for Error-Correcting Codes*, IBM Journal of
Research and Development 4(5) (1960), 532–542, Section 2, equation (2.10),
DOI [10.1147/rd.45.0532](https://doi.org/10.1147/rd.45.0532);
[original article](https://bitsavers.trailing-edge.com/pdf/ibm/IBM_Journal_of_Research_and_Development/045/ibmrd0405M.pdf).
The binary linear-code bound and the prefix redundancy form for every t≤r
are proved internally in `PaperP1.GriesmerBound`. The residual construction
is proved in `PaperP1.BinaryResidual`. No external proposition is assumed.
The arithmetic application uses the proved T1.1, with the exact `64B` scale.

Stable ID: `P1-ARITH-PNT`. Status: **proved**.
For every real η>0 there is B₀≥2 such that every integer B≥B₀ satisfies
`primeCount B ≤ (1+η) * B / log B`. The sequential limit
`π(B) log B / B → 1` is also proved, with the exact inclusive prime count.
There is no coefficient or degree parameter. The public declarations are
`PaperP1.SharpPrimeCount.primeCount_upper_eventually` and
`PaperP1.SharpPrimeCount.prime_counting_ratio_tendsto`.

Primary statement reference: Avigad, Donnelly, Gray and Raff,
*A formally verified proof of the prime number theorem*, ACM TOCL 9(1),
Article 2 (2007), DOI
[10.1145/1297658.1297660](https://doi.org/10.1145/1297658.1297660),
[preprint](https://arxiv.org/abs/cs/0509025), introduction, page 1.
Its explicit inclusive-prime-count limit agrees with the required convention.
The checked Lean proof below is independent of that Isabelle proof.

The selected Lean proof source is
`AlexKontorovich/PrimeNumberTheoremAnd`, commit
`127b50e33f6033e2147921167a117af96d9ba4ea`, Apache-2.0, Lean 4.35.0.
`WeakPNT` in `Wiener.lean` and `pi_alt'` in `Consequences.lean`, together with
their selected function-space, Fourier, cutoff and asymptotic dependencies,
are recompiled and audited under Lean 4.36.0-rc2 and the pinned Mathlib.
The unused unfinished bounded-variation decay block is excluded; the actual
proof uses the proved W21 Fourier estimates. Source blobs, scopes, licences,
statement comparison and version adaptations are recorded in
[PRIME_NUMBER_THEOREM_ALIGNMENT.md](PRIME_NUMBER_THEOREM_ALIGNMENT.md).
Mathlib's analytic continuation and nonvanishing facts are compiled inputs
at `9d581dfff2e41de989072ea63abf3daf69311520`. The historical Paper C PNT
interface is an unproved proposition and is not used as evidence or a premise.
No literature theorem is left as an unproved assumption in this PNT chain.

The exact finite inequality, all uniform asymptotic specializations and actual
relative-sign independence of article Lemma 2.1 are now proved. See
[local rigidity alignment](LOCAL_RIGIDITY_ALIGNMENT.md), including the weaker
base hypothesis and the exact critical-band marginal consequences.

## Checked measure-theory infrastructure

The general probability-space version of Proposition 4.1 uses already-proved
Mathlib facts at the pinned commit
`9d581dfff2e41de989072ea63abf3daf69311520`:

| Fact | Mathlib source | Role |
|---|---|---|
| `MeasureTheory.sum_measureReal_singleton` | `MeasureTheory/Measure/Real.lean` | Normalize finite observation weights |
| `MeasureTheory.map_measureReal_apply` | `MeasureTheory/Measure/Real.lean` | Identify actual event probabilities |
| `MeasureTheory.integral_fintype` | `MeasureTheory/Integral/Bochner/SumMeasure.lean` | Identify finite weighted expectation with Bochner integration |
| `MeasureTheory.integral_map` | `MeasureTheory/Integral/Bochner/Basic.lean` | Transport expectations through the measurable observation |
| `MeasureTheory.Measure.ext_of_singleton` | `MeasureTheory/Measure/Dirac/Basic.lean` | Identify the full count pushforward measure |

These are compiled library theorems, not literature assumptions passed as
unproved premises. Probability normalization, measurability and finite-measure
integrability are supplied or proved explicitly in the P1 modules.

## Checked infinite-cylinder infrastructure

The infinite prime-sign model and its finite restrictions use compiled Mathlib
results at the same pinned commit, with probability and measurability supplied
explicitly:

| Fact | Mathlib source | Role |
|---|---|---|
| `MeasureTheory.Measure.uniformOfFinset_apply` | `Probability/Distributions/Uniform.lean` | Normalize the two-point coordinate measure |
| `MeasureTheory.Measure.infinitePi_map_restrict` | `Probability/ProductMeasure.lean` | Identify every finite coordinate marginal of the infinite product |
| `MeasureTheory.Measure.pi_map_piCongrLeft` | `MeasureTheory/Constructions/Pi.lean` | Reindex observed prime coordinates |
| `MeasureTheory.integral_map` | `MeasureTheory/Integral/Bochner/Basic.lean` | Transport every actual finite-cylinder expectation |

These are proved library inputs. They supply no arithmetic counting bound or
asymptotic estimate. The no-constant-tail result uses only finite cylinders,
their masses tending to zero, and prime/square evaluations.

## Regular-set transfer: no additional external input

Main Proposition 3.1 is now proved using the internal T1.3 two-defect count,
full local rigidity and exact affine probabilities. Finite coupling, moment
truncation and the complete second factorial-cumulant identity are proved
internally. The source's bounded-fixed-moments premise remains an ordinary,
explicit mathematical hypothesis only for the conditional moment-transfer
clauses; no literature theorem or target transfer estimate is assumed.
It may hold just along one prescribed length sequence. See
[regular-set alignment](REGULAR_SET_ALIGNMENT.md).

## Local square threshold and critical defects

Companion T9.1 is proved directly from the internal T1.1 split-product bound,
with the stronger threshold recorded in `P1-MATH-0005`. Companion T9.2 is a
specialization of the proved T1.3 local count with cutoff 10B; the absolute
constant quantifier is recorded in `P1-MATH-0006`. No new external theorem,
analytic truncation estimate or admissibility premise is assumed. See
[alignment](LOCAL_SQUARE_THRESHOLD_ALIGNMENT.md).

## Missing-block and factorial-tuple estimates

Companion T22.2 is proved internally from finite relation-kernel cardinalities,
exact actual joint probabilities and active-tuple counting. Its factorial
moment is an actual infinite-measure expectation and is proved equal to the
sum over all ordered distinct tuples. No literature theorem, factorial-moment
bound or target tuple estimate is assumed. The general heterogeneous version
is recorded in `P1-MATH-0007`; see [alignment](MISSING_BLOCK_ALIGNMENT.md).

## Exact support and factorial lattice

Companion T19.1 uses no external mathematical input. The deterministic start
separation, finite interval packing with its exact ceiling, binary affine
mass lattice and unordered-subset factorial expansion are proved internally.
The existing exact cylinder transfer connects them to the actual infinite
count and moments, including incompatible systems. No probability, moment
or arithmetic estimate is assumed. See [alignment](SUPPORT_LATTICE_ALIGNMENT.md).

## Free-component graph foundations — initial partial checkpoint

The pinned-graph resolution and exact large-prime occurrence equations are
selected, attributed and recompiled Paper C proofs; see the exact commit and
blob records in [PAPER_C_REUSE.md](PAPER_C_REUSE.md). Their P1 cutoff is 10B.
The actual defective-count and component-selection bridges are new checked
P1 proofs. No external graph theorem or arithmetic estimate is assumed.
At that initial checkpoint, the complete-relation/small-prime rank comparison
remained open and T9.3 was not counted complete. The comparison is now proved
as recorded below; see [complete alignment](FREE_COMPONENT_ALIGNMENT.md).

## Complete free-component comparison

The remaining T9.3 comparison is now proved. Rank-nullity supplies the
complete-relation dimension, and an explicit finite constraint map imposes
all π(10B) small-prime coordinates and the two block parities. The internal
proved PNT is specialized with error parameter one to obtain the convenient
closed budget π(10B)+4≤24B/log B eventually. The actual defect count and
critical local-kernel bound are already proved. No external rank estimate,
prime-count proposition or target c-d_xy bound is assumed. See
[complete alignment](FREE_COMPONENT_ALIGNMENT.md).

## Companion T22.4 — Critical-order exact branching

The growing-order prime pool budget, variable tilt, logarithmic
correction and full-vector independence are proved internally. T22.3
supplies the already proved finite Rankin estimate. A finite square
remainder proves the negative 1/9 coefficient without an assumed
asymptotic expansion. The deterministic exception criterion is the
previously validated P1-MATH-0030 construction. No target exception
count, conditional independence or external mathematical estimate
is an input. No new Paper C code is ported. See
[alignment](CRITICAL_ORDER_BRANCHING_ALIGNMENT.md).

## Companion T19.11 — Closed scalar Stein factors

The Poisson solution and its two unit bounds are now proved from finite
Poisson balance, cumulative and tail factors, their monotonicity and
the exact signed difference kernel. No immigration/death-process
representation, unproved Stein-factor statement or literature estimate
is an input. Product Poisson mass identities prove stationarity of the
actual single/double reference. The total variation test and size-bias
identities are proved internally for actual probability measures.
The previously inspected Paper C modules are still not ported.
See [alignment](SCALAR_RECURRENCE_ALIGNMENT.md).

## Companion T20.7 — Exact covered-rank comparison

The coordinate restriction, graph reduction, component encoding and
proper-pair rigidity are closed internal proofs. The finite small-prime
target has dimension pi(H)+2 for every omitted block, including singleton
components, so no separate defective-count estimate is needed. The
critical-band constant uses the already proved elementary Chebyshev
bound; no external prime theorem or rank estimate is an input. The
existing attributed pinned-graph equivalence is reused through its
checked P1 interface, with no new Paper C port. See
[alignment](COVER_RANK_ALIGNMENT.md).


## Companion T19.6 — An internal growing-order tail proof

The proof uses the internally proved finite prime-budget Rankin bound,
actual full-vector independence after old observations, an exact
joint-event bridge and a proved distinct-tuple factorial recurrence.
The order k=ceil(128*(log N)^2) is controlled uniformly before Markov
is applied. The tail and truncated moments therefore require no
smooth-pair estimate, conditional dependency-graph bound or extrapolation
of fixed-order constants. Elementary logarithmic-power limits compare
the literal source thresholds. No new Paper C code is ported. See
[alignment](VERY_SMALL_TAIL_ALIGNMENT.md).


## Companion T19.5 — Effective support without an initial pair estimate

The proof uses the closed prime-budget Rankin theorem at sigma=1/2,
an explicit budget at a controlled growing order, and the actual factorial
recurrence initialized at zero. No bounded F_2 estimate or fixed-order
moment theorem is an input. Elementary real-power limits, the exact
finite-cylinder Markov inequality and Z<=N finish both source bounds.
No new Paper C code is ported. See
[alignment](EFFECTIVE_SUPPORT_ALIGNMENT.md).


## Article Lemma 3.5 — Finite normalized compression

Zero-sum image generators, the intersecting-union rule, dilation
invariance and private-coordinate injectivity are proved internally.
The actual normalized intersection is identified with exact units and
bounded by the proved elementary channel lattice count. Four channel
arithmetic modules are attributed Paper C ports rebuilt under the new
compiler; no rank, private-coordinate implication or asymptotic target
is supplied as a literature hypothesis. The motif count and uniqueness
of the translation parameter are explicit finite proofs. See
[alignment](GOOD_EDGE_COMPRESSION_ALIGNMENT.md).


## Companion T2.6 — Finite coefficient only

The gcd/proper-divisor inequality and the exact finite candidate-set
identification are closed internal proofs. The leading-channel values
use exhaustive bounded arithmetic proofs with strict ratio endpoints,
and the 8:9 value follows from a literal eligible fraction plus the
universal upper bound. No numerical search or actual-rank estimate is
an input. The remainder of T2.6 remains open; no external premise is
introduced for it. See [partial alignment](FIXED_CHANNEL_GAMMA_ALIGNMENT.md).


## T2.6 and T1.11 — Finite affine matching classes

One-class lower and upper counts follow from the exact integer-ceiling
formula in Mathlib. Integer Bezout coefficients supply the affine
residue, and proved gcd/lcm identities identify the intersection class.
Finite inclusion-exclusion yields the uniform two-sided error at most
3. No CRT counting estimate, asymptotic O(1) premise or actual-rank
identity is assumed. The remaining arithmetic/rank bridges are open.
See [partial alignment](FIXED_CHANNEL_MATCHES_ALIGNMENT.md).


## Actual normalized matching positions

Stable ID: `P1-ARITH-ACTUAL-TARGET-MATCHES`. Status: **proved finite core**.
Actual target positions matching the deduplicated normalized source union
inject into the two affine congruence classes. Positive actual joint mass
gives the start separation needed for physical fractions; their true-set
bound is B/b+2, and the combined strict-interior bound is B*gamma+3.
There is no height restriction, external counting premise or new Paper C
port. This closes an actual-value bridge, while residual normalized rank
and endpoint exceptions remain unresolved. See
[alignment](ACTUAL_TARGET_MATCHES_ALIGNMENT.md).


## Uniform aligned residual arithmetic

Stable ID: `P1-ARITH-ALIGNED-RESIDUAL`. Status: **proved one-unit subcase; full T1.9 in progress**.
The actual normalized full value kernel is uniformly o(B) for all
heights up to B^3, without separation, compatibility or local regularity.
The full pair deficiency is <=(u-1)+epsilon*B and, in reduced channels,
<=L/b+epsilon*B. The finite component-code proof uses actual disjoint
value sets, the proved degree-uniform Runge lemma, the existing audited
Hamming theorem, elementary prime counts and a proved polynomial-height
prime-factor budget. No new literature hypothesis or Paper C source is
introduced. The actual enlarged-cutoff value kernel at fixed height is
now bounded by the actual defective-value count, proving O(B/log B)
with its constant before the critical-band width. The full-kernel and
full-pair-deficiency rates follow. Target quotient-rank bridges for
T1.11/T2.6 have a proved finite bridge; the combined target-union
asymptotic application remains unresolved. See
[alignment](ALIGNED_RESIDUAL_RANK_ALIGNMENT.md).


## Bounded-affine dyadic matching arithmetic

Stable ID: `P1-ARITH-DYADIC-MATCHING`. Status: **proved finite/uniform core**.
Actual source labels and explicit bounded affine target data give finite
integer fraction separation, literal endpoint-source and decoded target
pools, explicit polynomial counts and one common critical-band threshold.
The actual B*gamma+3 matching bound needs deterministic separation only.
The construction of those data from geometric alignment remains unresolved.
The finite target quotient-rank bridge is now proved in the later
checkpoint below; its actual combined-union asymptotic application remains
open. No rational-separation,
curve-counting or rank estimate is assumed. No new Paper C port or external
mathematical hypothesis is introduced. See
[alignment](DYADIC_MATCHING_ALIGNMENT.md).


## Actual finite target quotient rank

Stable ID: `P1-ARITH-TARGET-QUOTIENT`. Status: **proved finite core**.
A generic division-ring theorem bounds zero-sum target selections modulo
old true values by actual intersection count plus the true union kernel.
The masked parity kernel is exactly the literal solution space after
finite prime rows are discarded. Old prime-coordinate bits contained in
that set are handled by a proved kernel inclusion. Actual normalized
window spaces and exact matching positions are identified, giving the
paper's target deficiency including internal defects. Source privacy,
local regularity, separation and compatibility are unnecessary for this
finite rank bridge. The combined target-union geometry and canonical
bounded affine target construction remain unresolved. No rank estimate
or external mathematical proposition is assumed. See
[alignment](TARGET_QUOTIENT_RANK_ALIGNMENT.md).

## Full enlarged-alignment closure of T1.9

The literal enlarged geometric alignment, including zero units and both
orientations, is now discharged by the existing proved Runge, Hamming,
prime-count and local-defect estimates. The extra work is explicit
interval geometry and finite span/rank-nullity algebra. The fixed-height
constant precedes the critical-band width. No new external mathematical
hypothesis or Paper C source is used. See the [full alignment](ALIGNED_RESIDUAL_RANK_ALIGNMENT.md)
and preserved [scope correction](FORMALIZATION_SCOPE_AUDIT.md).

## Complete aligned-target quotient rank and canonical data

The actual combined-union geometry, polynomial coefficient prime budget,
remaining-row o(L) bound and quotient-rank conclusion are now proved.
Literal compressed-source alignment constructs bounded reduced affine
data. Both source orientations, actual compatibility, old prime signs,
explicit source exceptions and target counts are included. No rational
separation estimate, curve count, rank bound or encoding existence is an
external premise. All arithmetic uses the already proved Runge, Hamming,
prime-count and finite linear-algebra results. No new Paper C source is
used. T1.11 and T2.6 are complete; source mass and Palm mean remain
separate. See the [full alignment](ALIGNED_TARGET_RANK_ALIGNMENT.md).

## Known-alignment rank from the existing residual

Article 13.7 now follows from the proved full enlarged-alignment T1.9
and actual compatible-window separation. The fixed-tau bound, uniform
half bound and exact height-one contact case require no new external
input. Short-basis, norm-polynomial and curve-counting results are not
premises of this known-alignment conclusion. Their nonaligned uses remain
separate unfinished work. See the [alignment](KNOWN_ALIGNMENT_RANK_ALIGNMENT.md).

## Finite channel selection and placement identities

The A_d cardinalities, actual within-window signed placements, weighted
moments, arbitrary-integer-shift identity and exact leading-channel sums
are proved by finite binary linear algebra, finite sums and polynomial
identities. No literature proposition or external arithmetic estimate is
assumed. These finite calculations do not supply the source-host, mass
or asymptotic error estimates of article 3.3 and companion T2.5. Both
numbered statements remain in progress. See the
[finite alignment](FINITE_CHANNEL_SUMS_ALIGNMENT.md).

## Actual source translation counts

The exact rational-ceiling interval, its bijection with actual dyadic
source pairs, disjoint orientations and the uniform 3B/6B finite errors
are proved from elementary integer arithmetic. The common threshold
before all reduced heights <=B^3 uses the proved critical polynomial
scale lemma. No external lattice-counting input is assumed and no new
Paper C source is used. Probability/mass identification and defective
normalizations remain separate. See the
[translation alignment](SOURCE_TRANSLATIONS_ALIGNMENT.md).

## Weighted canonical-pattern translation aggregation

Finite dependent sums and a proved weighted triangle inequality combine
the actual source translation counts into main terms N*w*U and N*w*S
with error <=6B*U. The signed main term retains predecessor cancellation.
The result is uniform through reduced height B^3. No external summation
or mass estimate is assumed. Identification with actual complete unit
relations/Fourier contributions and probabilities, and defective sources,
remain open. See the [weighted alignment](CHANNEL_WORD_HOSTS_ALIGNMENT.md).

## Exact unit coefficients on private normalized values

The actual private value-intersection equality, zero-sum coefficient
transport, normalized unit/value bijection and explicit even-unit/common-class
linear equivalence are proved by finite linear algebra and literal sums.
No external dimension or relation-space identification is assumed.
The zero/singleton cases are included. Affine character signs and the
probability/mass bridge remain separate. No new Paper C source is used.
See the [coefficient alignment](EXACT_UNIT_INTERSECTION_ALIGNMENT.md).

## Actual private pair Fourier contribution

`StartVertexSign`, `UnitAffineSigns`, `PairFourierIntersection`,
`PairSquareClassFourier` and `PrivateUnitCovariance` prove the actual
predecessor signs, common-class reindexing and private pair covariance.
Separate local affine solutions suffice; no joint compatibility is assumed.
These finite algebra and probability identities use already proved project
results and the pinned Mathlib only. There is no new literature premise
or Paper C port. Full selected-word enumeration and normalization estimates
for article 3.3 and companion T2.5 remain unfinished.

## Actual canonical unit-word enumeration

`BinaryEvenSelections`, `ExactUnitProgression`, `SelectedUnitExtrema`,
`ChannelGapWords`, `SelectedUnitWords`, `SelectedUnitWordBijection` and
`SelectedUnitFourierEnumeration` prove the fixed-pair actual word
bijection, exact cardinality and predecessor sign enumeration. They use
finite binary algebra, coprimality, actual window labels and finite
extrema only. There is no new literature premise or Paper C port. The
global host aggregation and exceptional-normalization estimates remain open.

## Actual dyadic rational-unit aggregate

`UnitShapePatterns`, `DyadicUnitWordHosts`, `DyadicUnitFourierAggregate`
and `DyadicUnitFourierCount` prove the actual pair-shape/global-pattern
bijection, dyadic host reindexing, exact symmetric signed unit aggregate
and its <=6B*U translation error uniformly through height B^3. These
use previously proved finite and critical-scale results only. There is
no new literature premise or Paper C port. Exceptional normalization
removal and full channel mass/profile asymptotics remain unfinished.

## Actual normalized exceptional hosts

`NormalizedPrivateDefects`, `NormalizedDefectSources`,
`NormalizedDefectSourceCount`, `UnitFourierWeight` and
`FixedChannelSourceGeometry` use the already proved elementary private-prime
lemma, actual global defect count and finite binary coefficient cardinalities.
They give actual host injections, fixed-channel square-root counts,
privacy-free rational-unit weights and source geometry. No residual-rank
or external host-count premise is introduced. The final retained mass
calculation and phase comparison remain unfinished; no literature input
or Paper C port is added.

## Actual finite private-channel mass reduction

`PrivateChannelSources`, `PrivateChannelRemoval` and
`PrivateChannelMassBound` combine the already proved actual probability,
dyadic aggregate, source count and rational-unit weight identities. Their
finite mass error uses no complete residual-nullity estimate for defective
pairs and no external input. The critical-scale and phase comparisons
remain unfinished. No Paper C port is added.

## Actual fixed-channel critical remainder

`ChannelUnsignedBound`, `CriticalChannelPowers`, `FixedChannelErrorAlgebra`
and `PrivateChannelMassRate` combine proved finite counts, actual probability
identities and elementary real powers to give the explicit O(B^2/N) actual
mass error, hence the source N^(-1+epsilon) estimate. No complete defective
pair residual-nullity estimate or external premise is used in this route.
The positive phase equivalent and cutoff-convention transport remain open.
No Paper C port is added.

## Complete actual fixed-channel mass T2.5

`SignedChannelLeadingBounds`, `ChannelMainTermAlgebra`,
`ChannelMainTermBounds`, `PrivateChannelMassPhase`,
`RealPrivateChannelSources`, `FixedChannelMassTheorem` and the extended
`CriticalChannelPowers` complete the positive phase and exact real-cutoff,
literal separated-family transport. Both source T2.5 assertions and
its stronger explicit remainder are proved with existing project results
and the pinned Mathlib only. There is no new literature premise, global
axiom or Paper C port. The complete main pair profile remains unfinished.

## Actual large selected kernels and one-small-kernel windows

Stable ID: `P1-ARITH-LARGE-SELECTED-KERNEL`. Status: **proved**, complete T1.6.

- `LargeSelectedKernelTheorem.companion_T1_6` proves both source bounds on
  actual mixed rational-square selections and actual dyadic window values.
  Both orientations, real cutoffs and a threshold before all critical
  lengths and cutoffs are included. No target counting, probability, rank,
  CRT or Euler estimate is supplied as a premise.
- The generalized canonical-triple port uses Paper C commit
  b9fa9ba490f201b408a302a86f1594ee620b228b, Apache-2.0, with exact provenance
  in PAPER_C_REUSE.md. All other bridges and finite-tail arguments are new
  P1 proofs using already pinned Mathlib finite sums and real powers.
- Finite rough prime pools and the already proved integer p-series tail
  close the Rankin/Euler estimate. The explicit bounds, r>N residue-fibre
  case and stronger selection scope are P1-MATH-0046. No new unproved
  literature input is introduced. See
  [alignment](LARGE_SELECTED_KERNEL_ALIGNMENT.md).

## Large-kernel branch for several actual windows

Stable ID: `P1-ARITH-SEVERAL-LARGE-KERNEL-RECEIVERS`. Status: **proved branch**,
companion T1.14 remains in progress.

- Actual mixed binary parity forces each selected anchor prime to a receiving
  window. Prime assignments are finite; their group moduli divide the actual
  kernel K<=3N. The exact CRT cost is at most 4^m*N^m/K, including moduli>N.
- The scaled canonical-support tail and actual marked-anchor tuple injection
  give the uniform N^(m+1/2+epsilon)*T^(-1/2+tau) count. The beta_s exponent
  identity and choice of tau after epsilon are proved, without assuming a
  target tuple bound.
- The remaining two-small-kernel estimate and full fixed-width/dilation
  assembly are not hidden hypotheses of these theorems and do not count as
  completed coverage. No new Paper C port or unproved literature input is
  introduced. See [alignment](LARGE_KERNEL_TUPLES_ALIGNMENT.md).

## Arbitrary selected fixed-width one-kernel blocks

Stable ID: `P1-ARITH-ONE-KERNEL-FIXED-WIDTH`. Status: **proved first assertion**,
companion T1.13 remains in progress.

- Actual positive selected values, arbitrary subsets varying with the centre,
  a finite offset cover and an injective value map give the finite count.
  The already proved square-root Rankin endpoint supplies the analytic bound.
- One threshold precedes all sets, critical lengths, prime thresholds and
  real T>=0. Real width/height ceilings and the exact real-cutoff floor
  dictionary are proved. No rank, independence or target count is assumed.
- The separate two-small-kernel assertion still requires T1.5. No new
  unproved literature input or Paper C port is introduced. The stronger
  one-kernel scope extends P1-MATH-0046. See
  [alignment](FIXED_WIDTH_SMALL_KERNEL_ALIGNMENT.md).

## Finite bivariate polynomial level sets

Stable ID: `P1-ALG-BIVARIATE-GRID-COUNT`. Status: **Mathlib and proved P1 wrapper**.

- Mathlib pin 9d581dfff2e41de989072ea63abf3daf69311520 provides the proved
  Schwartz-Zippel and homogeneous coefficient/degree lemmas. Explicit
  denominator clearing, nonzero constant-level transport and actual integer
  grids give the coefficient-independent d*(2H+1) bound.
- This is an independent ingredient of T1.4 Step 3; the eliminant and full
  determinant argument are not established by it. No new unproved
  literature hypothesis or Paper C port is introduced. The proof
  simplification is P1-MATH-0048. See
  [alignment](BIVARIATE_GRID_ALIGNMENT.md).

## Primitive eliminant denominator arithmetic

Stable ID: `P1-ALG-PRIMITIVE-DENOMINATORS`. Status: **proved arithmetic ingredient**.

- Exact gcd and natural-absolute-value identities prove q divides R*Rprime
  from the two primitive-coordinate divisibilities, uniformly in exponents.
  An explicit signed divisor set gives the finite 2*tau bound.
- The already audited elementary divisor-subpolynomial proof gives the
  polynomial-height count with one threshold before all coordinates,
  exponents and finite denominator families.
- Actual chart-resultant identities are now constructed in the later
  resultant checkpoint; source nondegeneracy/height and full T1.4 remain
  in progress. No new Paper C port or unproved
  literature input is introduced. This extends P1-MATH-0048.

## Actual homogeneous chart-resultant identities

Stable ID: `P1-ALG-ACTUAL-RESULTANT-DIVISIBILITIES`. Status: **proved ingredient**.

- Mathlib pin 9d581dfff2e41de989072ea63abf3daf69311520 provides actual
  Sylvester Bezout, homogenization and coefficient-reflection proofs.
  The P1 proof derives both chart divisibilities and primitive cancellation
  from actual form evaluations.
- Nonzero padded resultants use explicit univariate coprimality and
  full-degree conditions; integer polynomials are transported injectively
  to Q. Actual finite signed denominator sets may vary their primitive
  coordinate witnesses. The common polynomial-height count is proved.
- Source chart extraction, nondegeneracy/height and the full determinant
  argument remain open. No unproved literature input or new Paper C port
  is introduced. See [alignment](RESULTANT_DENOMINATORS_ALIGNMENT.md).

## Actual bidegree-one auxiliary primitive-point count

Stable ID: `P1-ALG-BIDEGREE-ONE-CURVE-COUNT`. Status: **proved local case**,
full T1.4 remains in progress.

- Actual Sylvester entries and the proved determinant absolute-value bound
  give explicit resultant heights from auxiliary coefficient bounds.
  Canonical integer primitive Bezout coefficients construct the scale.
  Its nonzero signed divisor budget, actual homogeneous eliminant and
  fixed-scale injection prove the finite count on actual integer solutions.
- Real coefficient exponents and exact real box membership are proved.
  A common N^epsilon*H threshold precedes all auxiliary coefficients of
  the prescribed height, all original homogeneous coefficient forms, every
  nonzero integer shift and all real boxes. Original coefficients, shifts
  and boxes need no height bound in this local case.
- Nonzero chart resultants and the literal equations are explicit algebraic
  conditions. Source auxiliary extraction/nondegeneracy and coefficient
  height from determinant/lattice steps remain to be established. No
  target counting estimate or unproved literature input is assumed; no
  Paper C port is added. See [alignment](BIDEGREE_ONE_CURVE_ALIGNMENT.md).

Scope precision for P1-MATH-0049: the proved elementary elimination
estimate is in the remaining pair height. The complementary Heath-Brown
bound in the eliminated pair height remains open, including for the
relevant bidegree-one auxiliary factors. No min-of-both-heights estimate
is claimed by this checkpoint.
