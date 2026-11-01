# Mathematical corrections and improvements

Baseline: original P1 V1.6 article and companion, 31 October 2026, preserved in
`manuscripts/paper-p1/v1.6/`. This log is separate from the original package's
historical reviews and editorial revisions.

**30 mathematical improvements are confirmed; no error in a manuscript conclusion
has been confirmed.** The paper has not yet undergone a complete formal audit.
Absence of an entry does not mean the argument has been verified.

## P1-MATH-0001 — Weaker algebra assumptions for Lemma 5.1

- Location: main article, Lemma 5.1, page 19, label `p1:stop:polynomial`,
  `main_sections/stopped.tex:40` in V1.6.
- Original setting: a commutative unital algebra.
- Improvement: a commutative semiring suffices. The identity requires only
  finite sums and products, distributivity, zero and one. Additive inverses and
  a scalar algebra structure are unnecessary.
- Evidence: `PaperP1.Algebra.stopped_expansion`, proved in Lean v4.36.0-rc2
  with the exact scalar parameter, ordered boundary and suffix. The supporting
  lemmas identify the proper prefix with deletion of the maximum.
- Suggested revision: state the identity for elements `t, u_x` of any
  commutative semiring. The signed-measure application, all estimates and all
  asymptotic exponents are unchanged.
- Status: confirmed by compilation and the kernel-axiom audit; not yet
  integrated into a new manuscript version.

## P1-MATH-0002 — Entirely algebraic proof of companion T1.1

- Location: technical companion, Lemma T1.1, page 5, label `p1:arith:runge`,
  `companion_sections/arithmetic_appendix.tex:19` in V1.6.
- Original proof: analytic square-root branches, a Cauchy coefficient bound,
  a tail estimate and a separate auxiliary-polynomial equality case.
- Improvement: finite formal-series coefficients and integer-square separation
  prove the same degree-uniform conclusion `U ≤ (64R)^d`. The proof needs no
  analytic branch choice, convergence argument or tail estimate.
- Evidence: `PaperP1.SplitProductBound.uniform_split_product_real_radius`,
  `PaperP1.RungeUniform.rungeQ_height_le`, and the intermediate nonzero-value
  height bound. Real radii, integer bases and every even degree are retained.
- Suggested revision: replace the proof by the algebraic argument detailed in
  [SPLIT_PRODUCT_ALIGNMENT.md](SPLIT_PRODUCT_ALIGNMENT.md). Its auxiliary
  height bound is `H(Q) ≤ (k+1)2^(5d)R^d ≤ (64R)^d`; both branches give
  `U ≤ H(Q)` directly.
- Impact: no change to T1.1's hypotheses, conclusion, constant or downstream
  exponents. This is a proof simplification; no error in the original proof
  is claimed, and its analytic inequalities have not been separately checked.
- Status: confirmed by compilation and the kernel-axiom audit; not yet
  integrated into a new manuscript version.

## P1-MATH-0003 — Weaker cutoff hypotheses for T1.3

- Location: companion Lemma T1.3, page 6, label `p1:arith:defects`,
  `companion_sections/arithmetic_appendix.tex:90`, all three conclusions.
- Original setting: B is comparable to log N and H is comparable to B, with
  fixed comparison constants shared by the combined lemma.
- Improvement: the local estimate needs only H=O(B), with B comparable to log N.
  The global count needs only H ≤ D log N and a linear counting
  height. The two-defect-window count needs only H ≤ D log N and L ≤ E log N.
  Fixed D,E ≥ 0 suffice; a lower bound on H and the intermediate B are
  unnecessary for the last two conclusions. The lower comparison H ≳ B is
  unnecessary for the local estimate as well. The paper's domain H ≥ 2
  remains covered, including fixed bounded cutoffs.
- Evidence: `GlobalDefectCount.global_defect_count_le_rpow_eventually`,
  `TwoDefectCount.two_defect_count_le_rpow_eventually`, and
  `TwoDefectWindows.dyadic_two_defect_windows_le_rpow_eventually`, and the
  complete `UniformDefectCounts.companion_T1_3_run_length` and
  `companion_T1_3_run_length_fixed_affine` statements.
  Actual finite sets and a threshold before all cutoffs and lengths are used.
- Suggested revision: replace H ≍ B by H=O(B) in the local estimate, and state
  the global and two-defect estimates separately under their upper logarithmic
  bounds. The B ≍ log N comparison remains in the local estimate. See
  [exact alignment](TWO_DEFECT_ALIGNMENT.md).
- Impact: strengthens parameter scope, including bounded or smaller cutoffs;
  the exponents 1/2 and 0 are unchanged. T1.3 is now complete, including the
  local estimate and fixed real affine interval versions.
- Status: confirmed by full compilation and the 862-declaration kernel-axiom
  audit; not yet integrated into a new manuscript version. The JSON record
  preserves the earlier 830-declaration validation of the first two components.

## P1-MATH-0004 — A lower base bound suffices for local rigidity

- Location: article Lemma 2.1, page 11, label `p1:limits:local-rigidity`,
  `main_sections/exact_setup.tex:27` in V1.6. The source block is unchanged.
- Original setting: U ≍ N and B=O(log N), followed by the sharp fixed-order
  logarithmic rank thresholds and subcritical relative-sign independence.
- Improvement: fix a>0 and require only U≥aN. The upper bound U=O(N) is
  unnecessary for every local-rigidity conclusion. The rank bound is also
  uniform for all positive B≤c log N whenever c<2-2^(1-t), rather than only
  a chosen sequence B~c log N. A single threshold precedes all U and B.
- Evidence: `UniformLocalRigidity.finite_griesmer_eventually`,
  `uniform_relation_rank_lt`,
  `LocalRigidityRegimes.relation_rank_lt_of_length_asymptotic`,
  `critical_relation_rank_le_one_of_error`,
  `RelativeSignIndependence.subcritical_window_relative_signs_independent`,
  and `LocalRigidityConsequences.critical_band_marginals`.
  The rounded common cap, sharp PNT budget and actual relation-code extension
  are proved; independence uses the full product law under the infinite model.
- Suggested revision: state local rigidity uniformly for U≥aN, with a fixed
  positive a. State the general rank consequence uniformly for every
  B≤c log N below the same threshold. Keep t fixed before the asymptotic
  threshold. In the finite Griesmer inequality alone, t can vary after N;
  that finite threshold is independent of t.
- Impact: enlarges the arithmetic domain, including bases that grow faster
  than N. The constant 64, critical coefficient 1/log 2, sharp rank
  thresholds and all error exponents are unchanged. In the original dyadic
  application, the exact heterogeneous marginals remain p or 2p, with the
  proved pointwise bound `(2 * 2^C)/N` in a fixed critical band.
- Status: confirmed by full Lean 4.36.0-rc2 compilation and the actual
  1,223-declaration kernel-axiom audit; not yet integrated into a new paper
  version. See [local rigidity alignment](LOCAL_RIGIDITY_ALIGNMENT.md).
  Exact proof commit:
  [deaa74d96763db33f7d8932053eb4bc308d3db4c](https://github.com/Vulkin-prog/paper-p1-lean/commit/deaa74d96763db33f7d8932053eb4bc308d3db4c).

## P1-MATH-0005 — A stronger finite local-square threshold

- Location: companion T9.1, page 39, `p13:rig:local-square`,
  `companion_sections/pair_rigidity.tex:17`.
- Original condition: x>(B+1)^(12m), B≥2, where m is the positive even
  cardinality of the actual offset set I⊆[-B,B].
- Improvement: x>(64B)^m suffices. Since 64B≤(B+1)^5 for every B≥2,
  the simpler condition x>(B+1)^(5m) suffices as well.
- Evidence: `LocalSquareThreshold.local_square_threshold_sharp`,
  `local_square_threshold_power_five` and `companion_T9_1`. These are proved
  from the internal degree-uniform T1.1 theorem after an exact reindexing of
  the finite integer set. The threshold supplies the required base condition.
- Suggested revision: use the sharper (64B)^m threshold or replace 12m by
  5m, and replace the analytic truncation argument with this short consequence
  of T1.1. No optimality of the new threshold is claimed.
- Impact: strengthens finite local square exclusion without changing the
  original conclusion, offset domain, evenness or later asymptotic exponents.
- Status: confirmed by Lean compilation and actual kernel audit; not integrated
  into a new manuscript. See [alignment](LOCAL_SQUARE_THRESHOLD_ALIGNMENT.md).

## P1-MATH-0006 — Absolute constants for critical defects and free components

- Location: companion T9.2, page 39, `p13:rig:defective`,
  `companion_sections/pair_rigidity.tex:62`.
- Original bound: O_C(B/log B) for the actual 10B-defective positions.
- Improvement: there is one absolute K>0 before the band width C. For each
  fixed C, only N0(C) changes. The same K bounds every start and every length
  in that critical band by K B/log B, with B=L+1.
- Evidence: `CriticalDefectPositions.uniform_critical_defect_constant`,
  `companion_T9_2` and the exact kernel/interval dictionary. The already proved
  T1.3 local count uses fixed dyadic-base and logarithmic-scale comparisons;
  their constants are independent of C once N exceeds a C-dependent threshold.
- Propagation to companion T9.3, page 40, `p13:rig:components`: the complete
  free-component comparison also has an absolute constant before C, with only
  N0(C) depending on C. Evidence: `FreeComponentRank.companion_T9_3`, the
  proved complete-relation dimension and the exact π(10B)+2 constraint cost.
  Its constant can differ from the defect-count constant. Both overlapping
  windows and all actual local kernels are retained.
- Suggested revision: state the quantifier order ∃K>0, ∀C, ∃N0(C), followed
  by all N, L and x. Preserve the eventual character of the result.
- Impact: strengthens constant uniformity. The cutoff 10B, rate B/log B and
  original conclusions are unchanged. No regularity or admissibility premise
  is introduced, and no uniform threshold over unbounded C is asserted.
- Status: confirmed by Lean compilation and actual kernel audit; not integrated
  into a new manuscript. See [alignment](LOCAL_SQUARE_THRESHOLD_ALIGNMENT.md).

The initial validated implementation commit for P1-MATH-0005 and the original
T9.2 scope of P1-MATH-0006 is
[548a0d2d02f1871aa3e4b26d7526082183f7bf03](https://github.com/Vulkin-prog/paper-p1-lean/commit/548a0d2d02f1871aa3e4b26d7526082183f7bf03).
The full build and actual 1,301-declaration kernel audit passed.

## P1-MATH-0007 — Missing-block estimates with heterogeneous marginals

- Location: companion T22.2, page 90, `p1:uniform:missing-block`,
  `companion_sections/uniform_appendix.tex:69`.
- Original setting: regular windows with their common marginal p and the
  tuple bound RNp·E(Z_G)_(R-1).
- Improvement: for arbitrary windows, the exact inequality is
  q(I)≤sum_x p_x q(I\{x}), with each actual marginal p_x. If pmax≥0 bounds
  them on G, the ordered-tuple sum is at most R|G|pmax·E(Z_G)_(R-1).
  The regular-set assertion follows by pmax=p and |G|≤N.
- Evidence: `MissingBlockProbabilities.infinite_joint_missing_block_bound`,
  `joint_missing_block_bound_of_marginal_le`, and
  `MissingBlockTupleSum.sum_missing_block_tuples_heterogeneous`. The source's
  full pointwise and summed conclusions are proved separately. The exact
  factorial-moment identity and injective tuple deletion are proved.
- Suggested revision: state the heterogeneous version first and give the
  regular specialization as a corollary. Keep the absence of a full-support
  relation as an explicit structural premise.
- Impact: removes regularity as a requirement of the general estimate and
  retains affine incompatibility, zero marginals and actual probabilities.
  It introduces no separation, independence, moment bound or order cutoff.
  The source's RNp constant and all asymptotic exponents remain valid.
- Status: confirmed by Lean compilation and actual kernel audit; not integrated
  into a new manuscript. See [alignment](MISSING_BLOCK_ALIGNMENT.md).

The exact validated implementation commit for P1-MATH-0007 is
[ec54490500649dfe3fb3ff73c1abfbd29ad555e4](https://github.com/Vulkin-prog/paper-p1-lean/commit/ec54490500649dfe3fb3ff73c1abfbd29ad555e4).
The full build and actual 1,334-declaration kernel audit passed.

The complete T9.3 consequence of P1-MATH-0006 is validated at
[a96edd26685699c9dfc651d9de2e7f7945773342](https://github.com/Vulkin-prog/paper-p1-lean/commit/a96edd26685699c9dfc651d9de2e7f7945773342),
with a full build and actual 1,435-declaration kernel audit. All 112 distinct
coverage/finding reference names were also checked by Lean. The original
T9.2 validation remains in the machine-readable history.

## P1-MATH-0008 — Integer bivariate factors need not be primitive

- Location: companion T9.4, page 41, `p13:rig:factor-height`,
  `companion_sections/pair_rigidity.tex:251`.
- Original hypothesis: Q is a primitive integer factor of nonzero P;
  the integer quotient is also bounded.
- Improvement: every integer factorization P=Q R suffices. Both factors
  obey the exact bound by 2^(dX+dY) ||P||₂, followed by the original
  sqrt((dX+1)(dY+1)) H(P) norm bound. No content correction is needed.
- Evidence: `BivariateFactorHeight.companion_T9_4_factor_and_quotient`,
  `companion_T9_4`, and `quotient_height_le_l2`. The proof gives a coefficient
  bound using the selected factor's own partial degrees before enlarging
  them to those of the product. It uses proved univariate Mahler bounds,
  specialization and Parseval, including degree-lowering specializations.
- Suggested revision: remove the primitive-factor hypothesis and state the
  conclusion for an arbitrary integer factorization of nonzero P.
- Impact: no change to the original constants, exponents or downstream
  conclusions. No error in the original conclusion or proof is claimed.
- Status: confirmed by the full Lean v4.36.0-rc2 build (8,651 jobs) and actual
  1,484-declaration kernel audit; not integrated into a new manuscript.
  See [complete alignment](BIVARIATE_FACTOR_HEIGHT_ALIGNMENT.md).

The exact validated implementation commit for P1-MATH-0008 is
[7b6f23e04ffe90d29d093d7009c00e5f52426209](https://github.com/Vulkin-prog/paper-p1-lean/commit/7b6f23e04ffe90d29d093d7009c00e5f52426209).
The full build, actual 1,484-declaration axiom audit and all 120 distinct
coverage/finding declaration checks passed.

## P1-MATH-0009 — Larger parameter interval for the moment perturbation

- Location: companion T23.1, page 93, `p1:obstruction:fixed`,
  `companion_sections/moment_obstruction.tex:8`.
- Original setting: 0≤a≤1 in the exact positive perturbation of Q_a.
- Improvement: the same construction works on 0≤a≤2, with the same
  pointwise factors 1/2 and 3/2, the same exact distance constant and the
  same factorial-moment difference. The perturbation is nonzero for a<2;
  at a=2 epsilon is zero, so P=Q and every moment agrees.
- Evidence: `MomentObstruction.companion_T23_1_extended`,
  `totalVariation_exact`, `exponential_moment_le`, and
  `MomentObstructionMoments.factorial_moment_eq_iff`.
- Suggested revision: use 0≤a<2 for the nontrivial example, optionally add
  the zero endpoint. For a uniform bound on [0,A], A≤2, replace the final
  exponential factor by 1+(A/2)(exp(t)-1)^2. A=1 retains the original bound.
- Impact: no change to epsilon or the original total variation constant.
  The uniform exponential constant on the larger interval is enlarged
  explicitly; it is not claimed to retain the original 1/2 coefficient.
  No error in the original statement is asserted. The following unnumbered
  m_N/Stirling asymptotics are not discharged by this proposition alone.
- Status: confirmed by the full Lean v4.36.0-rc2 build (8,727 jobs) and
  actual 1,647-declaration kernel audit; not integrated into a new manuscript.
  See [complete alignment](MOMENT_OBSTRUCTION_ALIGNMENT.md).

The exact validated implementation commit for P1-MATH-0009 is
[a8d53556b218c66ac655e855ac9096594217072b](https://github.com/Vulkin-prog/paper-p1-lean/commit/a8d53556b218c66ac655e855ac9096594217072b).
The full build, actual 1,647-declaration axiom audit and all 159 distinct
coverage/finding declaration checks passed.

Every finding receives a stable identifier `P1-MATH-0001`, etc., and an entry in
[mathematical-changes.json](mathematical-changes.json). Keep the following fields:

| Field | Required content |
|---|---|
| Location | Document, version, label, number, page, source file and lines |
| Original statement | Exact claim and hypotheses, with source identity |
| Finding | Concrete gap, counterexample, missing hypothesis or improvement |
| Classification | Confirmed correction, improvement, clarification, or open question |
| Evidence | Lean declaration/proof, exact computation, or mathematical derivation |
| Proposed revision | Precise replacement text or corrected quantifier/hypothesis |
| Impact | Other results, constants, exponents and proof dependencies affected |
| Validation | Pending / confirmed / rejected, with reason and exact commit |
| Manuscript integration | Target future version and integrated / not integrated |

Do not silently strengthen assumptions or weaken a conclusion to make a proof
compile. Record the discrepancy before changing the formal target. Distinguish
a missing Lean-library lemma from an actual mathematical gap. An unproved
arithmetic estimate is an open formalization obligation, not automatically a
counterexample to the paper. Preserve rejected findings with their resolution.

## Initial proof obligations to inspect

These are priorities, **not established errors**:

- Uniformity in coefficients and degree in the companion's arithmetic inputs.
- Effective spaces and affine incompatibility when a window has a local relation.
- Conditional propagation and the distinction between fixed and growing order.
- Exact heterogeneous marginals and repeated-index factorial-cumulant terms.
- The three reconstruction errors, positivity, and the fourth-order lower bound.
- The distinction between primitive supports and canonical direct components.

## Regular-set transfer verification — no new mathematical finding

The complete conclusion of article Proposition 3.1 has been checked, including
arbitrary affine targets, incompatible exceptional windows, actual infinite
count laws, both means, and the conditional fixed-moment and second factorial-
cumulant transfers. The latter retain the bounded-fixed-moments premise and
the diagonal term -E Z. A prescribed length sequence requires moment bounds
only along that sequence. The proof gives the explicit combined constant
4·2^C without changing the manuscript's exponent. This regular-set checkpoint added no correction or improvement entry.
The later local-square and defect-constant improvements are recorded above
as P1-MATH-0005 and P1-MATH-0006. See
[statement alignment](REGULAR_SET_ALIGNMENT.md).

## Exact support and factorial lattice verification — no new finding

Companion T19.1 is proved with its original ceil(N/L) support bound and
j! p^j nonnegative integer lattice. The proof includes all irregular and
incompatible windows and has no asymptotic or regular-set hypothesis.
It uses exact affine rank, deterministic separation and the full
unordered-subset factorial identity. No correction to this proposition is
identified; the seven confirmed improvement entries remain separate.
See [statement alignment](SUPPORT_LATTICE_ALIGNMENT.md).

## Free-component graph checkpoint — no new finding

The checked Paper C graph resolution is adapted to the literal P1 cutoff
10(L+1) and linked to actual defective positions. The D+c dimension and
component selection statements are proved, with exact source provenance.
At that initial graph checkpoint, the d_xy comparison remained open and no
completed numbered result or correction was added. The completed comparison
is recorded below; see [complete alignment](FREE_COMPONENT_ALIGNMENT.md).

## Complete free-component verification

The earlier partial graph checkpoint is now completed by an explicit
complete-relation equivalence, exact small-prime/parity constraint kernel and
closed prime budget. This proves all of companion T9.3. The stronger constant
quantifier is recorded as a consequence of P1-MATH-0006, whose original T9.2
validation remains preserved. No further finding identifier or paper error is
introduced. See [complete alignment](FREE_COMPONENT_ALIGNMENT.md).

## Exact quadratic Poisson positivity — no new finding

Article Lemma 8.1 is proved for an actual signed measure, including its
exact masses, total mass one, both directions of the parameter criterion,
the integer minimum and a large-index obstruction for every negative α.
The endpoints and integral means are included. All eight existing
improvement entries remain separate; no error or improvement is identified
in this lemma. The full build, actual 1,519-declaration axiom audit and all
130 distinct coverage/finding declaration checks passed. See
[complete alignment](QUADRATIC_POISSON_ALIGNMENT.md).

## Complete signed Palm verification — no new finding

Companion T19.12 is proved with the exact heterogeneous conditional laws,
omission of zero-marginal sources, diagonal error 2 sum p_x^2, raw recurrence
coefficients, and both generating-polynomial coefficient formulas. All
indicator families are transported from their original probability space;
independence is not assumed. The sums retain their signs before the norm.
The full build and actual 1,592-declaration axiom audit passed. No new
mathematical change is identified; the eight confirmed improvement entries
remain separate. See [complete alignment](SIGNED_PALM_ALIGNMENT.md).

## Complete moment-obstruction continuation — no new finding

The unnumbered continuation after T23.1 is now proved for the exact
m_N=floor(sqrt(log N)) and a_N=(log N)N^(-2/3). Parameter validity, actual
probability families, eventual fixed factorial moments, the full displayed
logarithmic error, and strict failure of every polynomial approximation
rate are checked. The distance comparison is uniform over all a in [0,1].
This completes that continuation separately from the original validated
parameter extension P1-MATH-0009, whose original commit is retained.
The full build and actual 1,680-declaration audit passed. No additional
finding identifier is introduced. See
[complete alignment](MOMENT_OBSTRUCTION_ASYMPTOTICS.md).

## P1-MATH-0010 — Weaker parameters for the weighted recurrence criterion

- Location: companion T19.13, page 77, `p1:limits:weighted-residual`,
  `companion_sections/limits_appendix.tex:1013`.
- Original hypotheses: mu>0 for the comparison and 0<mu,nu<=M for stability.
- Improvement: the same two-sided comparison includes mu=0. For all real
  mu and nu, stability holds with coefficient 2(1+abs(mu)) and parameter
  cost abs(mu-nu). Thus the source coefficient 2(1+M) requires only
  0<=mu<=M, with no restriction on nu.
- Evidence: `WeightedPoissonNorm.poisson_comparison_nonnegative`,
  `weightedNorm_stability` and `weightedNorm_stability_bounded`.
  The exact factorial solution and absolutely convergent resolvent give
  the lower comparison constant; no moment or comparison estimate is assumed.
- Suggested revision: include the zero-parameter Poisson law and state the
  all-real stability estimate before its bounded-parameter specialization.
  Negative parameters apply to the recurrence norm, not to a Poisson law.
- Impact: unchanged constants on the original domain. Arbitrary probability
  laws without a first moment were already allowed by the source and remain
  included. No original conclusion is corrected.
- Status: confirmed by the full Lean v4.36.0-rc2 build (8,745 jobs) and actual
  kernel audit of all 1,728 theorem/lemma declarations; not integrated into
  a new manuscript. See [complete alignment](WEIGHTED_POISSON_NORM_ALIGNMENT.md).

Exact validated implementation commit for P1-MATH-0010:
[281431eefffbf25daa2564d62280b3bd188a6496](https://github.com/Vulkin-prog/paper-p1-lean/commit/281431eefffbf25daa2564d62280b3bd188a6496).
All 178 distinct coverage/finding declaration names were also checked by Lean.

## Small-prime budget verification — no new finding

Both parts of companion T2.1 are proved for every translated positive
interval, with the exact sf/K small odd-prime product. The elementary
primorial inequality makes its original absolute O(B) remainder explicit
as (log 4)B, and gives the exact corresponding exceptional-value constant.
This checks the source's stated dependence, without changing its conclusion
or adding a critical-band premise. The full build and actual 1,746-declaration
kernel audit passed. The ten confirmed improvements remain separate; see
[complete alignment](SMALL_PRIME_BUDGET_ALIGNMENT.md).

## Integer product-tail verification — no new finding

Companion T20.2 is proved with the source exponent and logarithmic factor,
for each fixed s>1 and all real T>=1. Absolute convergence, exact floors,
strict product cutoffs and the order of constant quantifiers are checked.
The explicit constant supplies the source's stated dependence and is not
claimed optimal. The full build and actual 1,775-declaration kernel audit
passed. No additional mathematical finding is introduced; see
[complete alignment](INTEGER_PRODUCT_TAIL_ALIGNMENT.md).

## P1-MATH-0011 — An active coordinate budget and zero boundary parameters

- Location: companion T2.2, page 20, `p1:arith:coordinate-regularisation`,
  `companion_sections/supplemental_arithmetic.tex:51`.
- Original setting: K,d>=1 and codimension at most n/(K+1)+(s-r)/(d+1).
- Improvement: n can be replaced by n_plus, the number of initially nonzero
  coordinate forms counted with multiplicity. Both properties and the same
  budget hold for K,d>=0. At K=0 the final space is zero; at d=0 no present
  nonzero form has a decomposition into two distinct present nonzero forms.
- Evidence: `CoordinateForms.companion_T2_2_active_budget`, the proved
  potential inequality and exact nonzero-kernel dimension drop. Initial zero
  forms never contribute to the potential's active-coordinate term.
- Suggested revision: use n_plus and allow zero parameters, then give the
  original n and positive-parameter domain as a corollary. Keep the exact
  codimension card(D), unordered-label convention and simultaneous properties.
- Impact: a smaller finite bound when initial zero forms occur; no changed
  denominator or original conclusion. Arbitrary later restrictions are still
  allowed to destroy these properties. No manuscript error is asserted.
- Status: confirmed by the full Lean v4.36.0-rc2 build (8,765 jobs) and actual
  audit of all 1,814 theorem/lemma declarations; not integrated into a new
  manuscript. See [complete alignment](COORDINATE_REGULARISATION_ALIGNMENT.md).

Validated implementation for P1-MATH-0011:
[273ececdfd9ea82cd8271e9dac031f44c4e9c44a](https://github.com/Vulkin-prog/paper-p1-lean/commit/273ececdfd9ea82cd8271e9dac031f44c4e9c44a).
All 209 distinct coverage/finding declaration names were checked by Lean.

## P1-MATH-0012 — Ternary incidence dK^2 and arbitrary supports of size three

- Location: companion T2.3, page 21, `p1:arith:ternary-degree`,
  `companion_sections/supplemental_arithmetic.tex:107`.
- Original conclusion: incidence at most 2dK^2, for rows with at most one
  occurrence in each part of a three-block partition.
- Improvement: the incidence is at most dK^2. For each unordered pair of
  labels, the two full coordinate classes have at most K^2 choices in total.
  These choices already include both possible assignments to the other
  blocks. Supports, rather than repeated ordered row descriptions, are counted.
- The general statement needs only support size at most three, zero row sums,
  nonzero remaining labels and the two regularity bounds. A three-block
  coloring is sufficient to prove the support bound but is not otherwise used.
- Evidence: `ReducedBinaryRows.ternary_degree_bound`, its exact unordered
  support cover and `TernaryConstraints.after_regularisation_sharp`. The
  actual T2.2 subspace and all row transformations are retained.
- Suggested revision: use dK^2 and give the three-block case as a specialization
  of the support-size statement. Binary component size K is unchanged.
- Impact: a better finite constant and weaker structural assumptions. No
  original conclusion is corrected and no optimality of dK^2 is asserted.
- Status: confirmed by the full Lean v4.36.0-rc2 build (8,771 jobs) and actual
  audit of all 1,834 theorem/lemma declarations; not integrated into a new
  manuscript. See [complete alignment](TERNARY_CONSTRAINTS_ALIGNMENT.md).

Validated implementation for P1-MATH-0012:
[0f8350f2eecede15560958e20acac059f016bc05](https://github.com/Vulkin-prog/paper-p1-lean/commit/0f8350f2eecede15560958e20acac059f016bc05).
All 221 distinct coverage/finding declaration names were checked by Lean.

## P1-MATH-0013 — Disjoint recovery over arbitrary fields

- Location: article Lemma 6.1, page 21, `p1:fixed:recovery`,
  `main_sections/fixed_moments.tex:30`.
- Original setting: a binary coordinate subspace R in F_2^V.
- Improvement: the complete lemma holds over any field for any finite family
  of linear forms on a finite-dimensional U. The family need not separate
  points. This includes the stopping subspace, exclusion of every t-disjoint
  recovery system, multiplicity and independent-label representation count.
  The cost remains 2*card(V)*t^(-1/d), with d>=1 and t>=2.
- Evidence: `DisjointRecoveryTheorem.disjoint_recovery`,
  `disjoint_recovery_sharp`, `DisjointRecoverySubspace.exists_small_recovery_subspace`,
  `coordinate_multiplicity_le` and
  `IndependentRepresentations.independentRepresentations_source_bound`.
- Suggested revision: generalize the full lemma and retain its original
  binary coordinate specialization for the arithmetic applications.
- Status: confirmed by the full Lean v4.36.0-rc2 build (8,797 jobs) and actual
  audit of all 1,891 theorem/lemma declarations. No original conclusion is
  corrected. Not integrated into a manuscript. See
  [alignment](DISJOINT_RECOVERY_ALIGNMENT.md).

The earlier partial checkpoint proved the subspace, recovery exclusion and
multiplicity clauses only, with 1,874 audited declarations:
[749cc57a47466ee65501e37ed5f5dfcfca6a24ea](https://github.com/Vulkin-prog/paper-p1-lean/commit/749cc57a47466ee65501e37ed5f5dfcfca6a24ea).
Its limited scope is preserved in the machine-readable validation history.

## P1-MATH-0014 — Sharper count for zero-sum-free label supports

- Location: the final clause of the same article Lemma 6.1.
- Original conclusion: at most j!*t^(j-1) representations by j distinct
  linearly independent labels, for 1<=j<=d.
- Improvement: j!*(t-1)^(j-1) suffices. The same bound even counts all
  supports of size j with no nonempty zero-sum subset and a fixed nonzero sum.
  The counting lemma works in every abelian group under the explicit absence
  of t disjoint nonempty sum representations of sizes at most d.
- Proof: a maximal disjoint family has at most t-1 members; its union is a
  transversal of size at most j*(t-1). Mark a label in that transversal and
  erase it. Zero-sum-freeness makes the residual sum nonzero. The smaller
  representations satisfy the induction hypothesis, giving the full factorial
  recurrence. Every step, including the transversal construction, is proved.
- Evidence: `ZeroSumFreeRepresentations.representations_card_le`,
  `UniformTransversal.exists_transversal`,
  `IndependentRepresentations.independent_zeroSumFree`,
  `independentRepresentations_card_le`,
  `RecoveryLabelSupports.noDisjointSums_of_recovery_exclusion` and
  `DisjointRecoveryTheorem.disjoint_recovery_sharp`.
- Suggested revision: use the stronger constant and state explicitly that
  representations are unordered supports of distinct labels, as in the source
  proof. Ordered tuples would multiply the support count by j!. The
  zero-sum-free version may be stated with independence as a corollary.
- Status: confirmed by the same full build and actual axiom audit. No error
  or optimality claim is made. Not integrated into a manuscript.

All 239 distinct coverage/finding declaration names were checked directly by Lean.

Validated implementation of complete Lemma 6.1 and P1-MATH-0013/0014:
[9dcb13772d8b7dbef31571adca039223a50ec120](https://github.com/Vulkin-prog/paper-p1-lean/commit/9dcb13772d8b7dbef31571adca039223a50ec120).

## P1-MATH-0015 — The square-root endpoint in the small-kernel count

- Location: article Lemma 7.1, page 23, `p1:core:rankin`,
  `main_sections/cores.tex:24`; its proof is in companion
  `p14:comp:certificate-rankin`.
- Original assumptions: 1/2<sigma<1, T>=1, in the surrounding regime Y>=B.
- Improvement: the bound also holds at sigma=1/2. In fact every real
  X,Y,T>=0 satisfies the actual positive-integer count bound
  `2*sqrt(X)*sqrt(T)*exp(2*sqrt(Y))`.
- For 1/2<=sigma<1 the explicit bound is
  `X^sigma*T^(1-sigma)/(1-sigma)*exp(Y^(1-sigma)/(1-sigma))`.
  The exponential constant is 1/(1-sigma), depending only on sigma.
  At X=C1*N the prefactor is C1^sigma/(1-sigma).
- Proof improvement: retain the finite square-part fibre and bound its
  cardinality by floor(sqrt(X/(k*s))). Its Rankin comparison is valid at the
  endpoint. The source's enlarged infinite square-part series zeta(2*sigma)
  is unnecessary and would diverge there. The remaining finite k sum and
  finite Euler product have explicit integral bounds.
- Evidence: `RankinSmallKernel.rankin_half`, `rankin_bound`,
  `main_7_1_explicit`, `SmallKernelCount.card_smallKernelValues_le_power`,
  `RankinComparison.cast_sqrt_div_le_rankin` and
  `PartialPowerSum.powerSum_le`.
- Suggested revision: include the endpoint and explicit constants, replacing
  the infinite square-part sum by the finite fibre bound. Later applications
  may retain Y>=B and T>=1. No error or optimality claim is made.
- Status: confirmed by the full Lean v4.36.0-rc2 build (8,805 jobs) and actual
  audit of all 1,914 theorem/lemma declarations, with only `propext`,
  `Classical.choice` and `Quot.sound`. Not integrated into a manuscript. See
  [alignment](RANKIN_SMALL_KERNEL_ALIGNMENT.md).

All 251 distinct coverage/finding declaration names were checked directly by Lean.

Validated implementation of article Lemma 7.1 and P1-MATH-0015:
[77ac64fd3085c4f58ebb6a071f5c3fa30779a85b](https://github.com/Vulkin-prog/paper-p1-lean/commit/77ac64fd3085c4f58ebb6a071f5c3fa30779a85b).

## P1-MATH-0016 — Stronger Rankin bounds under a logarithmic prime budget

- Location: companion T22.3, page 90, `p1:uniform:prime-budget`,
  `companion_sections/uniform_appendix.tex:116`.
- Original conclusions: the finite count has a factor zeta(2*sigma) for
  1/2<sigma<1; the logarithmic bound is uniform on [3/5,3/4], Y>=3,
  with an O(1+Y^(1-sigma)/logY) remainder.
- Improvement: remove the zeta factor. The Euler-product count holds for
  every sigma>=1/2. The logarithmic estimate extends uniformly to
  [1/2,3/4] and Y>1, with the explicit remainder
  `(65+4*log(4))*Y^(1-sigma)/logY`, without the additive one.
- Proof: finite square-root fibres give the stronger count. The elementary
  primorial bound controls initial logarithmic prime sums. Finite Abel
  comparison transfers this to real-power weights. A fixed 1/8 power bound
  controls log(Y/p), and the prime set above Y is charged to its actual
  logarithmic budget. Every constant is independent of the finite set,
  exponent and cutoffs in the stated range.
- Evidence: `SmoothSquarefreeCount.card_values_le_euler`,
  `PrimeBudgetRankin.log_values_le`,
  `WeightedPrimeSum.primeSum_mul_log_le_uniform`,
  `LogarithmicPrimeBudget.primeBudgetSum_le` and
  `PrimeBudgetRankin.companion_T22_3`.
- Suggested revision: use the finite fibre proof, wider interval and explicit
  constant. No PNT or zeta upper bound is needed. No error in an original
  conclusion or optimality claim is made.
- Status: confirmed by the full Lean v4.36.0-rc2 build (8,817 jobs) and actual
  audit of all 1,941 theorem/lemma declarations, with only `propext`,
  `Classical.choice` and `Quot.sound`. Not integrated into a manuscript. See
  [alignment](LOGARITHMIC_PRIME_BUDGET_ALIGNMENT.md).

All 263 distinct coverage/finding declaration names were checked directly by Lean.

Validated implementation of companion T22.3 and P1-MATH-0016:
[88a8ae4c5fe51e5b8ed6fdfdf86ee641531af02a](https://github.com/Vulkin-prog/paper-p1-lean/commit/88a8ae4c5fe51e5b8ed6fdfdf86ee641531af02a).

## P1-MATH-0017 — Wider offset-pattern parameters

- Location: companion T21.3, page 88, `p1:consequences:rankin-patterns`,
  `companion_sections/arithmetic_consequences.tex:208`.
- Original restrictions: d is 2 or 3; the integer-factor tilt has 0<zeta<1.
- Improvement: both estimates hold for every fixed integer d>=2, with
  constants allowed to depend on d. The integer-factor estimate holds for
  every zeta>=0, including zero and zeta>=1. The displayed exponents
  `s=1+(d-1)/c` and `s_zeta=1+(d-1+zeta)/c` are unchanged.
- Explicit constants use the proved prime and integer power-tail constants.
  For the original finite set d=2 or d=3, taking the maximum of the two
  prime constants gives one constant depending only on c and D0, as in
  the source. No constant uniform over unbounded d is claimed.
- Evidence: `OffsetPatternRankin.prime_patterns_explicit`,
  `integer_patterns_explicit`, `prime_patterns_uniform`,
  `coefficient_power`, `primeConstant_pos` and `integerConstant_pos`.
- Suggested revision: state the broader fixed-d forms when needed, and
  retain the d=2 or d=3 uniform corollary. The proof only needs a Rankin
  exponent above one; the entire stated larger range satisfies it.
- Status: confirmed by the full Lean v4.36.0-rc2 build (8,827 jobs) and actual
  audit of all 1,978 theorem/lemma declarations, with only `propext`,
  `Classical.choice` and `Quot.sound`. No error in a source conclusion or
  optimality claim is made. Not integrated into a manuscript. See
  [alignment](OFFSET_PATTERN_RANKIN_ALIGNMENT.md).

All 283 distinct coverage/finding declaration names were checked directly by Lean.

Validated implementation of companion T21.3 and P1-MATH-0017:
[6848867fb06d1790bc0ff5a0a298671889c1b638](https://github.com/Vulkin-prog/paper-p1-lean/commit/6848867fb06d1790bc0ff5a0a298671889c1b638).

## P1-MATH-0018 — A non-strict product threshold for fixed-source certificates

- Location: companion T4.2, page 27, `p1:fixed:CRT`,
  `companion_sections/fixed_moments.tex:68`.
- Original assumptions: product(G_i)>N and lengths in the critical band.
- Improvement: product(G_i)>=N suffices for the same uniform N^epsilon
  bound. Equality still permits at most one centre, because two distinct
  integers in the half-open interval [N,2N) differ by less than N.
- The complete count also only needs the upper logarithmic ceiling
  B<=D*logN. No lower critical-band length assumption is needed. The
  threshold precedes every source tuple and every allowed length.
- Finite proof: the source divisors and target offsets give at most
  `(B*sum_a tau(v_a))^k` codes. A valid code determines at most one centre.
  This counts each module directly as a divisor of an actual source value;
  an ordered-factorization estimate for their product is unnecessary.
- Evidence: `ShortIntervalCongruences.eq_of_common_divisors`,
  `card_fibre_le_one`, `ProductCertificate.card_targets_le`,
  `FixedSourceCertificate.mem_certificateTargets`,
  `UniformFixedSourceCertificates.certificateTargets_le_power_eventually`
  and `critical_band_certificateTargets`.
- Suggested revision: use the non-strict threshold and, if useful, state
  the upper-width version before its original critical-band corollary.
  The original signed-offset population and strict-product conclusion
  remain proved. No error or optimality claim is made.
- Status: confirmed by the full Lean v4.36.0-rc2 build (8,835 jobs) and actual
  audit of all 2,008 theorem/lemma declarations, with only `propext`,
  `Classical.choice` and `Quot.sound`. Not integrated into a manuscript. See
  [alignment](FIXED_SOURCE_PRODUCT_CERTIFICATE_ALIGNMENT.md).

All 297 distinct coverage/finding declaration names were checked directly by Lean.

Validated implementation of companion T4.2 and P1-MATH-0018:
[ed4ed43ecc05c2f7823ba9b0acca98bc1f62fc5d](https://github.com/Vulkin-prog/paper-p1-lean/commit/ed4ed43ecc05c2f7823ba9b0acca98bc1f62fc5d).

## P1-MATH-0019 — Only the first window needs to be regular for root separation

- Location: companion T20.5, page 83, `p1:offset:root-separation`,
  `companion_sections/offset_geometry.tex:192`.
- Original setting: a positive pair of regular windows with direct relative
  square-class spaces, on the nonzero-slope rational line y=alpha*x+beta.
- Improvement: only the first window needs to be regular. The second may
  have local even square relations. Both conclusions are retained: at most
  one common root, and deletion of at most two equations to obtain
  squarefree polynomials with pairwise disjoint root sets.
- Proof: two common roots give two proportional pairs of actual positive
  values. Their even square classes coincide. Injectivity of the first
  even-selection map makes that class nonzero; membership in both actual
  spaces contradicts directness. Second-window injectivity is unnecessary.
  The remaining support and polynomial steps are proved in full.
- Evidence: `OffsetRootPolynomials.root_separation`,
  `OffsetRootSeparation.match_left_unique`, `commonRoots_card_le_one`,
  `TwoPointSquareClasses.no_proportional_pairs`, `injective_evenMap_of_rank`
  and `OffsetRootExceptionalSet.exists_exceptional_coordinates`.
- Suggested revision: require first-window regularity only, retaining the
  original two-regular-window specialization for later applications.
  Positivity, the nonzero slope and directness remain explicit.
- Status: confirmed by the full Lean v4.36.0-rc2 build (8,847 jobs) and actual
  audit of all 2,038 theorem/lemma declarations, with only `propext`,
  `Classical.choice` and `Quot.sound`. No error or optimality claim is made.
  Not integrated into a manuscript. See
  [alignment](OFFSET_ROOT_SEPARATION_ALIGNMENT.md).

All 313 distinct coverage/finding declaration names were checked directly by Lean.

Validated implementation of companion T20.5 and P1-MATH-0019:
[9fac0fbf1971b9145acd77ce72f3e6e42cbfedfc](https://github.com/Vulkin-prog/paper-p1-lean/commit/9fac0fbf1971b9145acd77ce72f3e6e42cbfedfc).

## P1-MATH-0020 — Wider parameters for the weighted moderate-certificate estimate

- Location: article Lemma 7.2, page 23, `p1:core:moderate`,
  `main_sections/cores.tex:65` in V1.6.
- Original setting: A>1, 0<beta<1 and every fixed u>0.
- Improvement: the same weighted bound with exponent -2*beta+4/A+o(1)
  holds for every fixed beta>=0 and u>=0. More generally, a nonnegative
  weight a with a*N<=M for fixed M suffices, together with the explicit
  finite width constraints and B<=D*logN. The stronger theorem needs
  only an upper logarithmic width bound.
- Evidence: `ModerateCertificateAsymptotic.weightedTotal_le_power_eventually`,
  `weighted_criticalBand`, `ModerateWeightedSeries.weightedTotal_le`,
  `ModerateFactorialBudget.product_le_power_eventually` and
  `ModerateOrder.scaledOrder_tendsto`.
- The exact finite population is summed over every order; it vanishes
  above N. Its proved majorant is
  `18*B^(m+4)*T^(-2)*(m+1)!*exp(exp(1)*2*a*N)`.
  The actual ceiling, rather than an assumed asymptotic order, gives the
  factorial budget with exponent 4/A. The power estimate means that for
  every epsilon>0 one threshold precedes every allowed window length.
- Suggested revision: record this broader certificate estimate separately;
  retain beta<1 in any other core argument which requires it. No global
  extension of the paper's parameter ranges is claimed.
- Status: confirmed by the full Lean v4.36.0-rc2 build (8,875 jobs) and the
  actual audit of 2,123 theorem/lemma declarations. Only `propext`,
  `Classical.choice` and `Quot.sound` occur. No manuscript conclusion is
  corrected. Not integrated into a new manuscript version.

All 349 distinct coverage/finding declaration names were checked directly by Lean.

Validated implementation of both conclusions of article Lemma 7.2 and P1-MATH-0020:
[62861d120c500f4fcb910532aaa8eea5a6d6930b](https://github.com/Vulkin-prog/paper-p1-lean/commit/62861d120c500f4fcb910532aaa8eea5a6d6930b).

## P1-MATH-0021 — Lower divisor threshold for saturation degree bounds

- Location: article Lemma 7.3, page 24, `p1:core:degrees`,
  `main_sections/cores.tex:92` in V1.6.
- Original setting: a saturation witness has D>6*N*B.
- Improvement: for the degree estimates, the same exponent 2/A holds for
  the larger relation whose witness only needs D>=N. The non-strict
  endpoint is included. The actual enlarged incoming and outgoing
  neighborhoods, and their union, are all uniformly at most
  N^(2/A+epsilon) for every epsilon>0.
- The explicit finite bounds are B^2*(B+1)^m and
  B^2*(2*exp(1)*B)^m, with their sum bounding the union. They hold for
  N>=10, 2<=B<=N+1 and Y>=B, with the literal source ceiling m.
  The incoming powerset estimate is valid at every finite m and does
  not require the source intermediate condition m<=R/2.
- Evidence: `RelaxedSaturationDegrees.relaxed_neighborhood_bounds`,
  `RelaxedSaturation.outgoing_bound`, `incoming_bound`, `neighbors_bound`,
  `source_edge_subset`, `SaturationPrimes.divisor_data_of_le` and
  `BoundedSubsetWeights.weightSum_le_of_card_le`.
- Suggested revision: note the broader degree estimate separately. Keep
  the original 6*N*B threshold in any moderate/nonmoderate decomposition
  whose cost uses it. No replacement in the entire core argument is
  claimed, and no manuscript conclusion is corrected.
- Status: confirmed by the full Lean v4.36.0-rc2 build (8,893 jobs),
  followed by the actual audit of all 2,170 theorem/lemma declarations.
  Only `propext`, `Classical.choice` and `Quot.sound` occur. Not integrated
  into a new manuscript version.

All 374 distinct coverage/finding declaration names were checked directly by Lean.

Validated implementation of article Lemma 7.3 and P1-MATH-0021:
[41cefe7cf8bb7d036a201ea5ae764b66795f2023](https://github.com/Vulkin-prog/paper-p1-lean/commit/41cefe7cf8bb7d036a201ea5ae764b66795f2023).

## P1-MATH-0022 — Stronger graph generating bounds from disjoint stars

- Location: article Lemma 7.4, page 24, `p1:core:generator`,
  `main_sections/cores.tex:111` in V1.6.
- Original conclusion: exp(M*z+4*n*Delta*z^2/(1-4*Delta*z)), for z>=0
  and 4*Delta*z<1.
- Improvement: the same actual admissible family has the stronger bounds
  exp(M*z+n*z*((1+z)^Delta-1)) and
  exp(M*z+n*z*(exp(Delta*z)-1)) for every z>=0. The rational corollary
  exp(M*z+2*n*Delta*z^2/(2-Delta*z)) holds under the wider Delta*z<2
  condition. The actual degree profile can replace the maximum degree.
- The heterogeneous form permits any nonnegative vertex weights and gives
  exp(sum_marked w_v + sum_v w_v*(prod_{u adjacent v}(1+w_u)-1)).
  The left side is the actual sum of products over admissible vertex sets.
- Evidence: `MarkedGraphGenerator.polynomial_star_bound`,
  `exponential_star_bound`, `rational_star_bound`, `degree_profile_bound`,
  `GraphStarWeights.heterogeneous_generating_bound`,
  `GraphStarPartition.exists_partition`, `MinimalFiniteCover.exists_private_cover`
  and `FinitePolymerBound.generating_le_exp`.
- Proof: a minimal finite cover by graph edges and marked singletons has
  a private vertex in every member. Orienting these as leaves and grouping
  the other endpoints gives disjoint stars. Counting all star collections
  by a finite product bounds the original sum. All coverings, partitions
  and weight identities are constructed and proved internally.
- Suggested revision: add the star bound and its heterogeneous version;
  retain the original rational formula as a corollary where convenient.
  No optimality or manuscript-error claim is made.
- Status: confirmed by the full Lean v4.36.0-rc2 build (8,905 jobs),
  followed by the actual audit of all 2,207 theorem/lemma declarations.
  Only `propext`, `Classical.choice` and `Quot.sound` occur. Not integrated
  into a new manuscript version.

All 393 distinct coverage/finding declaration names were checked directly by Lean.

Validated implementation of article Lemma 7.4 and P1-MATH-0022:
[91f0b85e7a22f8527792bfbaf209f8d6f11a4bc4](https://github.com/Vulkin-prog/paper-p1-lean/commit/91f0b85e7a22f8527792bfbaf209f8d6f11a4bc4).

## P1-MATH-0023 — Double the lower Poisson--Charlier coefficient bound

- Location: article V1.6, unnumbered equation `p1:close:constant-bounds`,
  `main_sections/closure.tex:99`; related to Proposition 19.2.
- Original bound: exp(-lambda)/4 <= C(lambda) <= 1, where
  C(lambda)=norm(Poisson(lambda)*Delta^2)/4 and lambda>0.
- Improvement: exp(-lambda)/2 <= C(lambda). The original normalization,
  upper bound and asymptotic exponents are unchanged.
- Proof: a summable real sequence of total mass zero has l1 norm at
  least twice any coefficient. The second Poisson difference has total
  mass zero and coefficient exp(-lambda) at zero. Thus its norm is at
  least 2*exp(-lambda), rather than the single-coefficient bound used
  in the original displayed estimate.
- Evidence: `FiniteNegativeMass.l1_ge_twice_point`,
  `PoissonSecondDifferenceNorm.norm_second_lower_bound` and
  `PoissonSecondDifferenceNorm.coefficient_lower_bound`.
  The last theorem also includes lambda=0 for the signed definition.
- Suggested revision: double the lower constant in the displayed
  unnumbered inequality and mention the zero-mass argument. The original
  weaker estimate remains true; no manuscript error is asserted.
- Status: confirmed by the full Lean v4.36.0-rc2 build (8,919 jobs),
  followed by the actual audit of all 2,257 theorem/lemma declarations.
  Only `propext`, `Classical.choice` and `Quot.sound` occur. Not integrated
  into a new manuscript version. This unnumbered improvement adds no
  extra numbered coverage item.

All 415 distinct coverage/finding declaration names were checked directly by Lean.

Validated implementation of article Proposition 19.2 and P1-MATH-0023:
[c3ae67f0b8622f142f16dce9eb4bb22fd541a2c5](https://github.com/Vulkin-prog/paper-p1-lean/commit/c3ae67f0b8622f142f16dce9eb4bb22fd541a2c5).

## P1-MATH-0024 — Weaker hypotheses for the whole offset-line estimate

- Location: companion T20.1, page 82, `p1:offset:line-product`,
  `companion_sections/offset_geometry.tex:25` in V1.6.
- Original setting: three distinct regular windows, pairwise direct
  relative spaces, and H=C0*B with C0>1.
- Improvement: first-window regularity and directness of the first two
  spaces suffice for the entire lemma. The other windows need no
  regularity, and the third space needs no directness condition. The
  stronger theorem even permits the third center to coincide with another
  center. All source positivity and size bounds remain in force.
  Canonical offsets need only H>=B, including C0=1.
- Evidence: `OffsetLineTheorem.uniform_stronger`, `finite_bounds`,
  `OffsetLineData.exists_nonzero_cross`, `OffsetLinePopulation.odd_offsets_unique`
  and `IntegralLine.parametrize_line_of_primitive`.
- Reason: a zero common minor vector would force two proportional value
  vectors. Only one regular/direct pair is needed to exclude them. The
  remaining prime-product and logarithmic arguments use no other local
  rank assumption. The primitive direction and all lattice parameters
  are constructed with integer Bezout identities.
- Suggested revision: weaken the line lemma separately; keep all stronger
  assumptions required by later plane and residual-space results.
  No manuscript error or optimality claim is made.
- Status: confirmed by the full Lean v4.36.0-rc2 build (8,935 jobs) and
  actual audit of all 2,305 theorem/lemma declarations, with only `propext`,
  `Classical.choice` and `Quot.sound`. Not integrated into a new version.

## P1-MATH-0025 — Sharper offset count and an absolute logarithmic constant

- Location: the distinct-offset conclusion of companion T20.1, same
  source and exact original statement hash as P1-MATH-0024.
- Original bound: 1+log(6*N*B)/logY, with O_{C0,C}(B/logB) dependence.
- Improvement: the actual distinct-offset count is at most
  log(6*N*B)/logY. The additive one can be omitted. The original majorant
  itself is eventually at most (1+6*log(2))*B/logB, with this absolute
  multiplicative constant chosen before C, C0, the centers, line and Y.
  The threshold dependence remains explicit.
- Evidence: `OffsetLineCount.distinct_offsets_le`,
  `OffsetLinePopulation.pool_product_le`,
  `OffsetLineMajorant.majorant_bound_eventually`, `majorantConstant_eq`,
  `majorant_little_o_uniform` and `OffsetLineTheorem.companion_T20_1`.
- Reason: both the single-point and multiple-point cases obey the same
  whole-product bound 6*N*B, so logarithms bound the number of primes and
  hence offsets without a separate additive term. The critical-band
  lower scale yields the absolute constant. The empty pool is included.
- Suggested revision: remove the additive one and record absolute
  multiplicative uniformity, while retaining the explicit eventual
  threshold and epsilon quantifiers for o(B). No error or optimality
  claim is made.
- Status: confirmed by the same full 8,935-job build and actual 2,305-
  declaration audit. Not integrated into a new manuscript version.

All 438 distinct coverage/finding declaration names were checked directly by Lean.

Validated implementation of companion T20.1, P1-MATH-0024 and P1-MATH-0025:
[cbf22970cceae54d3971a64f5a7def265088dc85](https://github.com/Vulkin-prog/paper-p1-lean/commit/cbf22970cceae54d3971a64f5a7def265088dc85).

## P1-MATH-0026 — Weaker regularity for forced planes and a larger mass population

- Location: companion Proposition T20.3, page 82,
  `p1:offset:forced-plane`, `companion_sections/offset_geometry.tex:96`.
- Original setting: three distinct regular windows, pairwise direct
  square-class spaces, H=C0*B with C0>1, and primitive triples for the
  two-plane mass conclusion.
- Improvement: the first two windows alone need full effective rank
  for the entire geometric conclusion. All pairwise directness remains
  in that proof. The two-plane mass estimate holds for the larger
  population with only the first two starts distinct, regular and direct;
  the third may be irregular, dependent or repeated. The actual joint
  probability is still at most p^2. Canonical odd offsets require H>=B.
  The subsequent-offset equation holds for any common integer divisor
  above 12*B^3, including composite divisors; the initial product proof
  still requires three distinct primes.
- Evidence: `OffsetPlaneTheorem.uniform_stronger`, `finite_stronger`,
  `OffsetPlaneMassAsymptotic.pairMass_le_power_eventually`,
  `TripleProbabilityBound.triple_joint_le`,
  `SharedPrimeOffsets.shared_unique_offset` and
  `OffsetPlaneGeometry.further_divisor_offset`.
- Reason: excluding proportional pair projections needs regularity of
  one of those two coordinates, and either coordinate zero leaves such
  a regular coordinate among the other two. The mass uses monotonicity
  of actual joint activation and the exact first-pair probability.
- Suggested revision: state these separately delimited hypotheses and
  the larger mass population. No later normal-budget or residual-space
  estimate is extended by this finding. No error or optimality claim.
- Status: confirmed by the full Lean v4.36.0-rc2 build (8,965 jobs) and
  actual axiom audit of all 2,402 theorem/lemma declarations, with only
  `propext`, `Classical.choice` and `Quot.sound`. Not integrated into a
  new manuscript version.

All 480 distinct coverage/finding declaration names were checked directly by Lean.

Validated implementation of companion T20.3 and P1-MATH-0026:
[1bbce661a7f9c0bdaaccc69e5ab171848a9e5db1](https://github.com/Vulkin-prog/paper-p1-lean/commit/1bbce661a7f9c0bdaaccc69e5ab171848a9e5db1).

## P1-MATH-0027 — A sharper local-block endpoint correction

- Location: the last sentence of companion Proposition T19.2, page 67,
  `p1:limits:local-blocks`, `companion_sections/limits_appendix.tex:63`.
- Original bound: the total endpoint correction has absolute value at
  most 2*L*p, with at most two truncated blocks.
- Improvement: each nonempty clipped block contributes a correction of
  absolute value at most p*(card(fullBlock)-1). Sum this quantity only
  over the actually truncated blocks to obtain a length-dependent bound;
  the simpler uniform bound is 2*(L-1)*p. Both hold in the finite rank-one
  formulation and uniformly in every fixed critical band.
- Evidence: `LocalBlockBoundarySharp.clipped_weight_error`,
  `boundaryError_bound_by_length`, `sum_boundaryError_bound_by_lengths`,
  `mean_full_block_error_sharp` and
  `LocalBlocksTheorem.boundary_improvement_uniform`.
- Reason: clipping retains at least one full-block start. If the endpoint
  causing the incompatible marginal is removed, at least one start is
  removed as well. Both cases give card(fullBlock)-1 rather than L.
- Suggested revision: sharpen the displayed finite boundary constant or
  state the finer bound using the actual full lengths. The asymptotic
  order, exact block laws and mean identities are unchanged. No sign of
  the whole mean bias, error in the original bound or optimality is claimed.
- Status: confirmed by the full Lean v4.36.0-rc2 build (8,989 jobs) and
  actual axiom audit of all 2,487 theorem/lemma declarations, with only
  `propext`, `Classical.choice` and `Quot.sound`. Not integrated into a
  new manuscript version.

All 523 distinct coverage/finding declaration names were checked directly by Lean.

Validated implementation of companion T19.2 and P1-MATH-0027:
[14bbf2d16f3c69615a182b774c6952d4fc323373](https://github.com/Vulkin-prog/paper-p1-lean/commit/14bbf2d16f3c69615a182b774c6952d4fc323373).

## P1-MATH-0028 — A factor-two improvement of the positive-core loss

- Location: companion Lemma T19.8, page 71, `p1:limits:peeling`,
  `companion_sections/limits_appendix.tex:427`.
- Original bound: a zero coordinate in the uniform relation kernel
  costs at most p*2^t, yielding c(C)>=(1-card(C)*p*2^t)*q(C).
- Improvement: the exact cost is 2^r_i/2^dim(S_i), with actual private
  rank r_i. The compatible lower bound keeps one minus the sum of these
  heterogeneous costs. Since integer r_i<t gives r_i<=t-1, the source
  homogeneous loss improves to p*2^(t-1). Every canonical component of
  the constructed terminal family inherits it. The implementation also
  retains the exact deletion charge t*(m-card(B))+rank(B)<=R.
- Evidence: `Affine.missed_card_ratio`, `private_profile_centered_lower`,
  `privateRank_centered_lower_sharp`, `PrivateCoreMoments.component_mass_bounds`,
  `PrivateRankPeeling.trace_rank_budget` and
  `PrivateRankPeelingTheorem.companion_T19_8`.
- Reason: deleting one coordinate identifies its zero fiber with the
  erased relation kernel. Exact cardinalities give its fraction; the
  strict integer private-rank bound supplies the missing factor two.
- Suggested revision: use 2^(t-1) in the positive-core inequality and
  optionally state the heterogeneous profile and exact rank charge.
  The displayed lower factor need not always be positive. No later
  arithmetic construction, original error or optimality is asserted.
- Status: confirmed by the full Lean v4.36.0-rc2 build (9,013 jobs) and
  actual axiom audit of all 2,542 theorem/lemma declarations, with only
  `propext`, `Classical.choice` and `Quot.sound`. Not integrated into a
  new manuscript version.

All 557 distinct coverage/finding declaration names were checked directly by Lean.

Validated implementation of companion T19.8 and P1-MATH-0028:
[6a2be0375db8f8051a562cf179b571d344aac9dc](https://github.com/Vulkin-prog/paper-p1-lean/commit/6a2be0375db8f8051a562cf179b571d344aac9dc).

## Companion T19.7 — Complete arithmetic-cylinder validation

The original positive and total exponential-moment liminf is now proved
along the nontrivial odd-prime filter, with N_q=2^(q-1), L_q=q-1 and
every fixed t>2. The exact cylinder mass, finite start-count lower bound,
actual infinite-measure expectations and PNT limit are all proved.
Both moments eventually exceed every real level. The one-unit smaller
sufficient cutoff has the same proved asymptotic cost. This is a closure
of the original result, with no new mathematical correction or threshold
optimality claim. See [alignment](PRIME_CYLINDER_ALIGNMENT.md).

The full build passed (9,029 jobs); all 2,602 theorem/lemma declarations
passed the actual axiom audit with only `propext`, `Classical.choice`
and `Quot.sound`. All 572 coverage/finding declaration names were
checked directly by Lean. Source bytes and all original statement hashes
are preserved. Coverage is 40 / 167, with 28 confirmed mathematical
improvements. No Palomar registration is made.

Validated implementation of companion T19.7:
[af00f6613fc890bee31ac2b83d609dc9a9030635](https://github.com/Vulkin-prog/paper-p1-lean/commit/af00f6613fc890bee31ac2b83d609dc9a9030635).

## P1-MATH-0029 — The exact incidence slope in a conditional mean budget

- Location: the conditional-mean pool term of companion Lemma T21.2,
  page 87, `p1:consequences:conditional-rank`,
  `companion_sections/arithmetic_consequences.tex:139`.
- Original coefficient: p*2^(T-1), for 1<=T<=L.
- Improvement: use p*(2^(T-1)-1)/T. This reduces the original coefficient
  by the factor (1-2^(1-T))/T and makes it zero at T=1. The finite refined
  theorem also admits T=0, with zero slope and the large-t population
  still explicitly retained.
- Evidence: `ExponentialSupportSlope.cross_bound`, `loss_le_slope`,
  `ConditionalRunProbability.conditionalStartProbability_nominal`,
  `ConditionalRunBudget.conditionalStartProbability_le_incidence`,
  `WindowPoolCount.sum_supportedIndices_dyadic` and
  `ConditionalRunBudget.conditional_count_bound_sharp`.
- Reason: t<=1 gives exact conditional probability p. For 2<=t<=T only
  the excess p*(2^(t-1)-1) needs charging. Its ratio to t is nondecreasing,
  and the actual incidence sum is at most B*card(poolValues).
- Suggested revision: replace the finite coefficient and include this
  excess-mass charging argument. Preserve the actual contact and large-t
  terms. No bound for the large-t population, original error or optimality
  is asserted. The last fixed-j asymptotic pool estimate in T21.2 remains
  open at this finite checkpoint, so no numbered coverage is added.
- Status: confirmed by the full build (9,049 jobs) and actual axiom audit
  of all 2,655 theorem/lemma declarations, with only `propext`,
  `Classical.choice` and `Quot.sound`. All 589 distinct coverage/finding
  declaration names were checked directly by Lean. Not integrated into
  a new manuscript version. See [alignment](CONDITIONAL_RANK_ALIGNMENT.md).

Validated finite conditional-rank implementation and P1-MATH-0029:
[dd3755df492b2fab0b50515d6b3b1dfc75014e3d](https://github.com/Vulkin-prog/paper-p1-lean/commit/dd3755df492b2fab0b50515d6b3b1dfc75014e3d).

## Companion T21.2 — Closure of its actual prime-pool asymptotic

The remaining fixed-j estimate is now proved. Actual old windows give
the uniform logarithmic prime-pool budget, and the proved Euler bound
gives its N^(1/2+epsilon) value count. Positive squares give the lower
scale. Exact binary factors and integer-floor errors place the source
pool term between N^(1/2-delta-epsilon) and
N^(1/2-delta+epsilon). One threshold precedes every critical length,
old-window choice and realizable old raw vector. The exact finite laws
and the P1-MATH-0029 improvement are retained. See
[complete alignment](CONDITIONAL_RANK_ALIGNMENT.md).

The full build passed (9,061 jobs), and all 2,687 theorem/lemma declarations
passed the actual axiom audit with only `propext`, `Classical.choice`
and `Quot.sound`. All 602 distinct coverage/finding declaration names
were checked directly by Lean. Coverage is 41 / 167, with 29 confirmed
improvements. Original sources are preserved; no Palomar registration
is made. The earlier finite validation remains recorded above.

Validated complete implementation of companion T21.2:
[64d651e45f660ed5151a11586ffd918c0878325d](https://github.com/Vulkin-prog/paper-p1-lean/commit/64d651e45f660ed5151a11586ffd918c0878325d).

## P1-MATH-0030 — A smaller deterministic branching exception set

- Location: the original-window exceptional estimate in companion
  Proposition T1.15, page 17, `p1:arith:fixed-branching`,
  `companion_sections/arithmetic_appendix.tex:1075`.
- Original bound: j*(2L+1)+B*sqrt(3N)*exp(2sqrt(m_{j,N})).
- Improvement: the constructed exceptional set need contain only
  windows with at least two old-pool-supported values. It has cardinality
  at most (B/2)*sqrt(3N)*exp(2sqrt(m_{j,N})). This removes the separate
  contact term and halves the pool coefficient in the proved original
  consecutive-window scope.
- Evidence: `BranchingExceptional.twice_badStarts_card_le`,
  `badStarts_card_explicit`, `ConditionalRelativeBits.map_joint_eq_fair_prod_old`,
  `independent_of_old`, `FixedWindowBranching.finite_stronger` and
  `original_windows_critical`.
- Reason: at most one supported value makes the relative conditional
  kernel zero even in a contact. The whole new relative vector is fair
  and independent of every old raw value under the original infinite
  measure. Every exceptional window charges at least two incidences to
  the budget B*card(poolValues).
- Suggested revision: use this deterministic criterion and its finite
  bound, with the full-vector conditional-law argument. No optimality
  or estimate for all arithmetic dependencies is asserted. Fixed dilation,
  subset and enlarged-window variants remain open at this checkpoint;
  T1.15 is therefore not yet counted as complete.
- Status: confirmed by the full build (9,071 jobs) and actual audit of
  all 2,713 theorem/lemma declarations, with only `propext`,
  `Classical.choice` and `Quot.sound`. All 618 distinct coverage/finding
  names were checked directly by Lean. Not integrated into a new
  manuscript version. See [alignment](FIXED_BRANCHING_ALIGNMENT.md).

Validated original-window branching implementation and P1-MATH-0030:
[8b5542412a96f221e87921abc9892ddabdac0505](https://github.com/Vulkin-prog/paper-p1-lean/commit/8b5542412a96f221e87921abc9892ddabdac0505).

## Companion T1.15 — Complete generalized-window branching

The remaining extension is now proved. Injective complete even-boundary
embeddings and transposes give the exact fair laws for actual selected
relative bits. They preserve independence from every old raw observation.
Fixed positive dilations have explicit coordinate embeddings and literal
integer-label formulas. Arbitrary bounded old observations, fixed enlarged
logarithmic widths, positive height multiples and injective center changes
share the uniform N^(1/2+epsilon) exception bound. The actual old-value
image has its j*B cardinality bound proved from its index set. One
threshold precedes all source and pattern choices.

`GeneralBranchingTheorem.companion_T1_15` combines this clause with the
literal original-window rounded bound, full vector law and every conditional
word probability. The earlier P1-MATH-0030 finite improvement is retained.
See [complete alignment](FIXED_BRANCHING_ALIGNMENT.md).

The full build passed (9,089 jobs), and all 2,759 theorem/lemma declarations
passed the actual axiom audit with only `propext`, `Classical.choice`
and `Quot.sound`. All 635 distinct coverage/finding declaration names
were checked directly by Lean. Coverage is 42 / 167, with 30 confirmed
improvements. Original sources are preserved; no Palomar registration
is made. The earlier original-window validation remains recorded above.

Validated complete implementation of companion T1.15:
[aa40b4a69208172c6fca0cdd9def2e336e92f278](https://github.com/Vulkin-prog/paper-p1-lean/commit/aa40b4a69208172c6fca0cdd9def2e336e92f278).

## Companion T22.4 — Uniform branching at growing critical orders

The original logarithmic bound is proved for every j<=K*log(N)/log(log(N)),
with one explicit positive constant and envelope preceding all source
and critical-band choices. The finite variable-tilt identity and a
negative square remainder prove the literal coefficient -1/9. The
same smaller two-supported-value exception criterion of P1-MATH-0030
provides the exact full-vector law and independence of all old raw
values. Its earlier improvement validation is retained; no separate
finding is counted for this application. See
[alignment](CRITICAL_ORDER_BRANCHING_ALIGNMENT.md).

The full Lean v4.36.0-rc2 build passed (9,095 jobs). All 2,777
theorem/lemma declarations passed the actual axiom audit with only
`propext`, `Classical.choice` and `Quot.sound`; all 647 distinct
coverage/finding names were checked directly by Lean. Coverage is
43 / 167, with 30 confirmed improvements. No new manuscript version
or Palomar registration is made. Growing-order moment estimates
and principal Poisson theorems remain open.

Validated implementation of companion T22.4:
[c5334aa55a0c179a93747cf2d3d6820d575b78dc](https://github.com/Vulkin-prog/paper-p1-lean/commit/c5334aa55a0c179a93747cf2d3d6820d575b78dc).

## P1-MATH-0031 — Closed scalar comparison and its boundary

- Location: companion Lemma T19.11, page 76, `p1:limits:stein`,
  `companion_sections/limits_appendix.tex:847`; original statement hash
  `7e070bb71a29687765ca75f1869a42e82d2ab9acc98731d44928fbff56191eab`.
- Original range: 0<=theta<min(mu,1/2).
- Improvement: for mu>0 permit 0<=theta<=mu and theta<1/2, including
  the pure-double-jump endpoint theta=mu. The same exact denominator
  1-2*theta and total variation convention hold. The size-bias norm
  identity holds for every theta in [0,m], requiring only a positive
  finite mean; a variance or second moment is unnecessary in this form.
- Evidence: `HermiteRecurrence.law_eq_product_sum`, `reference_stationary`,
  `scalar_recurrence_criterion_closed`,
  `PoissonSteinSolution.unit_stein_factors`,
  `SizeBiasedRecurrence.shiftMixture_eq_weighted_successors` and
  `size_bias_totalVariation_identity`.
- Suggested revision: state the closed boundary range for the scalar
  criterion, then the general size-bias identity before specializing
  its parameter to the second factorial cumulant. No optimality claim
  or small-residual estimate is added.

Both numbered conclusions of T19.11 and the following parameter stability
inequality are proved. The Stein solution, its two unit bounds and
reference stationarity are closed internal proofs. The actual reference
is the product-Poisson pushforward; the canonical biased and successor
laws retain their measure-theoretic meanings. The Paper C Stein modules
remain unported. See [alignment](SCALAR_RECURRENCE_ALIGNMENT.md).

The full Lean v4.36.0-rc2 build passed (9,113 jobs), and all 2,875
theorem/lemma declarations passed the actual axiom audit with only
`propext`, `Classical.choice` and `Quot.sound`. All 672 distinct
coverage/finding names were checked directly by Lean. Coverage is
44 / 167, with 31 confirmed improvements. Original source bytes
are preserved; no manuscript revision or Palomar registration is made.

Validated implementation of companion T19.11 and P1-MATH-0031:
[9ca5f8aecbbc79ecd99b0658bf2cb37fa414f842](https://github.com/Vulkin-prog/paper-p1-lean/commit/9ca5f8aecbbc79ecd99b0658bf2cb37fa414f842).

## P1-MATH-0032 — A finite cover bound including singleton components

- Location: companion Lemma T20.7, page 84, `p1:offset:cover-rank`,
  `companion_sections/offset_geometry.tex:271`; original statement hash
  `3ee81e33259f97340c3f952b3d45dabdc65d472d4c67f1c0bedd44538fa460f1`.
- Original proof: isolated free components require a defective-vertex
  estimate; exactly two-block components are bounded separately. The
  section assumes separated windows and C0>1.
- Improvement: all free components missing one specified block number
  at most pi(H)+2, including singletons. Their independent coefficients
  inject into the actual small-prime coordinates and two block parities.
  Thus dim(R_D)<=c3(D)+3*pi(H)+6 holds finitely, with no separate
  defective-count term. H>=B suffices; C0=1 and overlapping windows
  are allowed under local injectivity and pairwise directness.
- Evidence: `ColoredPrimeConstraints.selection_kernel_trivial`,
  `missing_components_card_bound`, `ThreeBlockRigidity.pairwise_rigid`,
  `TripleCoverRank.finite_rank_bound`, `companion_T20_7` and
  `CoverRankPrimeBudget.finite_budget`.
- Suggested revision: group every component avoiding one block under
  the same small-prime/two-parity argument; state the finite bound and
  retain injectivity and pairwise directness when weakening separation
  and the strict cutoff condition. No optimality or primitive-host
  estimate is asserted.

All source conclusions of T20.7 are proved. The cover is the actual
shared-prime hyperedge cover, the graph space equality and coordinate
cost are explicit, and every free component's positive product is a
small-prime product times a square. One explicit constant and one
critical-band threshold precede all triple and cover choices. See
[alignment](COVER_RANK_ALIGNMENT.md).

The full Lean v4.36.0-rc2 build passed (9,135 jobs), and all 2,927
theorem/lemma declarations passed the actual axiom audit with only
`propext`, `Classical.choice` and `Quot.sound`. All 700 distinct
coverage/finding names were checked directly by Lean. Coverage is
45 / 167, with 32 confirmed improvements. Original source bytes are
preserved; no revised manuscript or Palomar registration is made.

Validated implementation of companion T20.7 and P1-MATH-0032:
[2ecbeb2a1c57c75e700e1efc63225a9107335400](https://github.com/Vulkin-prog/paper-p1-lean/commit/2ecbeb2a1c57c75e700e1efc63225a9107335400).


## P1-MATH-0033 — A power threshold for the very small tail

- Location: companion Proposition T19.6, page 70, `p1:limits:colored-tail`,
  `companion_sections/limits_appendix.tex:296`; original statement hash
  `377d9659754253d1c87b71aea548e2b6f20b12f7ff691912355db547ce493e9b`.
- Original restriction: c<sqrt(13)/4 with Pascadi's smooth-pair input,
  or c<2/sqrt(5) with the de la Breteche--Drappeau estimate, at the
  rounded near-linear threshold.
- Improvement: every real threshold b>=N^(9/10) has probability
  <=exp(-2*(log N)^3). Its truncated r-th moments are
  <=exp(-(log N)^3/2), uniformly for integer 0<=r<=log N.
  Consequently both original near-linear conclusions hold for every
  fixed c>0, without the smooth-pair literature input.
- Evidence: `QuarticLogPrimePool.actual_pool_count_critical`,
  `QuadraticOrderBranching.quadratic_order_branching`,
  `JointBranchingEvents.retained_joint_factor`,
  `FactorialBranching.factorial_le_power`,
  `QuadraticOrderMoments.factorial_bound`,
  `QuadraticTailScale.probability_bound`,
  `NearLinearThreshold.threshold_ge_power` and
  `VerySmallTail.companion_T19_6`.
- Suggested revision: first prove the uniform factorial recurrence up to
  K*(log N)^2 using the quartic logarithmic prime pool. Apply the actual
  falling-factorial Markov inequality at the explicit ceiling order,
  then deduce the rounded source thresholds by comparison. This also
  removes the source upper restriction on c.

Both original probability and truncated-moment conclusions are proved
under the actual infinite prime-sign law, uniformly over every fixed
critical band. This proof does not establish bounded low-order moments
or the main Poisson theorem. See [alignment](VERY_SMALL_TAIL_ALIGNMENT.md).

The full Lean v4.36.0-rc2 build passed (9,157 jobs), and all 2,969
theorem/lemma declarations passed the actual axiom audit with only
`propext`, `Classical.choice` and `Quot.sound`. All 730 distinct
coverage/finding names were checked directly by Lean. Coverage is
46 / 167, with 33 confirmed improvements. Original source bytes are
preserved; no manuscript revision or Palomar registration is made.

Validated implementation of companion T19.6 and P1-MATH-0033:
[79e4e6d814ac0dc941544b2beb92437e45657a39](https://github.com/Vulkin-prog/paper-p1-lean/commit/79e4e6d814ac0dc941544b2beb92437e45657a39).


## P1-MATH-0034 — An effective-support coefficient chosen before C

- Location: companion Proposition T19.5, page 69, `p1:limits:effective-tail`,
  `companion_sections/limits_appendix.tex:255`; original statement hash
  `8e2ed24d53e5de8afa77692efe805e5747c327d27dbb7f515bda212839f37676`.
- Original dependence: K=K(C,D,r); the proof initializes the growing
  factorial estimate by the bounded pair moment F_2=O_C(1).
- Improvement: the actual recurrence can start at F_0=1. A finite
  logarithmic prime budget at order ceil((log log N)^(2/3)) proves
  both source conclusions without a pair-moment input. The explicit
  coefficient K=E+D+r+log 4 is independent of C. The eventual N
  threshold retains its dependence on C, D and r.
- Evidence: `EffectivePrimePool.raw_budget_le_envelope`,
  `euler_cost_bound`, `EffectiveOrderMoments.factorial_bound`,
  `EffectiveSupport.uniform_tail`, `band_uniform_constant` and
  `companion_T19_5`.
- Suggested revision: prove the actual finite recurrence from zero,
  state the displayed explicit coefficient before choosing C, and
  retain the literal source ceiling. The fixed power-threshold
  conclusion has an eventual N^(-D) bound with constant one.

Both numbered conclusions of T19.5 are proved for the original infinite
count. This does not establish bounded low-order moments or T19.4's
stronger initial-pair bound. See [alignment](EFFECTIVE_SUPPORT_ALIGNMENT.md).

The full Lean v4.36.0-rc2 build passed (9,165 jobs), and all 2,996
theorem/lemma declarations passed the actual axiom audit with only
`propext`, `Classical.choice` and `Quot.sound`. All 757 distinct
coverage/finding names were checked directly by Lean. Coverage is
47 / 167, with 34 confirmed improvements. Original source bytes are
preserved; no manuscript revision or Palomar registration is made.

Validated implementation of companion T19.5 and P1-MATH-0034:
[fa7ba5f5dd20098526dba859bb770a8ba73318f0](https://github.com/Vulkin-prog/paper-p1-lean/commit/fa7ba5f5dd20098526dba859bb770a8ba73318f0).


## P1-MATH-0035 — Finite compression from one normalized coincidence

- Location: article Lemma 3.5, page 16, `p1:arith:compression`,
  `main_sections/arithmetic.tex:230`; original statement hash
  `4b5ad33b5095a54af69a7b243e7e6c652772ff666d9271ec067e63cfe9fb126d`.
- Original scope: good compatible dependent pairs in the two leading
  channels, with an unspecified O(1) rank loss, O(B) width and
  B^{O(1)} choices of endpoint offsets.
- Improvement: one shared normalized value and private coordinates
  suffice for the complete finite compression, for positive coprime
  coefficients a<=b and positive window values. Compatibility,
  dependence, separation and a prior regularity hypothesis are not
  needed. Private coordinates imply both local ranks are L.
- Explicit bounds: rank=|U|-1 >=(2-1/b)*L-1; at most (L+1)^2 integer
  motifs, each in [-bL,bL]. At a fixed offset pattern its anchor
  determines both centres. Repeated normalized values are included once.
- Evidence: `EvenImage.image_eq_span_differences`,
  `FiniteEvenSquareClasses.space_union`, `space_dilate`,
  `CompressionRank.private_local_ranks`, `dependent_two_units`,
  `rank_lower_bound`, `NormalizedMotifs.family_card`,
  `anchor_injective`, `GoodEdgeCompression.finite_compression`
  and `main_3_5`.
- Suggested revision: state this finite version before specializing
  to good edges, replace the unspecified constants by these bounds,
  and give the anchor uniqueness assertion explicitly. For fixed a,b
  the width is logarithmic. No optimality claim is made.

All source conclusions hold for the actual deterministic good-edge
family. Its positive joint mass and dependence are retained in the
definition; normalized dependence supplies at least two exact units.
No pair-count or mass estimate is assumed by the compression proof.
See [alignment](GOOD_EDGE_COMPRESSION_ALIGNMENT.md).

The full Lean v4.36.0-rc2 build passed (9,191 jobs), and all 3,078
theorem/lemma declarations passed the actual axiom audit with only
`propext`, `Classical.choice` and `Quot.sound`. All 793 distinct
coverage/finding names were checked directly by Lean. Coverage is
48 / 167, with 35 confirmed improvements. Original source bytes are
preserved; no manuscript revision or Palomar registration is made.

Validated implementation of article Lemma 3.5 and P1-MATH-0035:
[37c99c7ea71d70271902fd12d1b52494646ec919](https://github.com/Vulkin-prog/paper-p1-lean/commit/37c99c7ea71d70271902fd12d1b52494646ec919).


## P1-MATH-0036 — The universal finite coefficient is attained

- Location: companion Lemma T2.6, page 22, `p1:arith:fixed-channel-rank`,
  `companion_sections/supplemental_arithmetic.tex:209`; original hash
  `8dd614c19e50df20ed1eb9f3ab37c07386f1ce3665c3499e26d83211ceab60b9`.
- Original statement: gamma_{a:b}<=2/3, with a finite numerator range
  and a denominator restricted implicitly by b/2<c/d<2a.
- Improvement: d<=2*b*(a+b-1) is an explicit finite cutoff removing
  no eligible fraction. The exact coefficients are 1/3 in channel 2:3,
  1/2 in channel 3:4 and 2/3 in channel 8:9. For 8:9 the eligible
  fraction 6/1 has gcds 2 and 3, attaining density 2/3.
- Evidence: `FixedChannelGamma.mem_candidates`,
  `mem_values_iff_source`, `isGreatest_real_values`,
  `gamma_le_two_thirds`, `gamma_two_three`, `gamma_three_four`,
  `gamma_eight_nine` and `universal_bound_attained`.
- Suggested revision: give the explicit denominator cutoff, the exact
  leading-channel values and the attaining 8:9 example. The universal
  coefficient ceiling is sharp across admissible fixed channels.

This sharpness concerns the **finite density coefficient**. It makes
no optimality assertion for an actual rank loss or Palm exponent.
T2.6 is only partially formalized: its rank estimate and exceptional
sources remain open. See [alignment](FIXED_CHANNEL_GAMMA_ALIGNMENT.md).

The full Lean v4.36.0-rc2 build passed (9,195 jobs), and all 3,101
theorem/lemma declarations passed the actual axiom audit with only
`propext`, `Classical.choice` and `Quot.sound`. All 816 distinct
coverage/finding names were checked directly by Lean. Coverage remains
48 / 167, with 36 confirmed improvements. Original source bytes are
preserved; no manuscript revision or Palomar registration is made.

Validated coefficient checkpoint for T2.6 and P1-MATH-0036:
[b9ff1b2874b76ba8fe97e314db236980b2fe6e13](https://github.com/Vulkin-prog/paper-p1-lean/commit/b9ff1b2874b76ba8fe97e314db236980b2fe6e13).


## P1-MATH-0037 — A uniform finite error of three matching offsets

- Location: proofs of companion T2.6, page 22,
  `p1:arith:fixed-channel-rank`, and T1.11's matching-density formula.
  Primary statement hash:
  `8dd614c19e50df20ed1eb9f3ab37c07386f1ce3665c3499e26d83211ceab60b9`.
- Original form: the union of the two matching residue classes has
  count at most B*(gcd(c,a)+gcd(c,b)-1)/c+O(1).
- Improvement: on every integer interval the absolute error from
  its length times that density is at most 3, uniformly in the
  shift and all natural parameters with the stated coprimalities.
  No upper height condition is required. The intersection is the
  exact affine class modulo c.
- Evidence: `IntervalResidueError.abs_error`,
  `AffineResidueClasses.solutions_eq_residue`,
  `UnionMatchDensity.solutions_intersection`, `abs_match_error`,
  `FixedChannelMatches.real_abs_match_error`, `window_match_gamma`,
  `window_match_two_three`, `window_match_three_four` and
  `physical_fraction_of_divisor`.
- Suggested revision: give this finite class-count lemma before the
  asymptotic rank argument. State B*gamma+3, including the global
  numerator reduction, and retain a separate argument for physical
  fractions and for actual rank. No optimality claim for 3 is made.

The counted object at this initial checkpoint is exactly the union of
divisibility classes. The actual-value bridge is now proved in
P1-MATH-0038 below; the residual-rank estimate remains open. Neither T2.6 nor T1.11 is counted complete. See
[alignment](FIXED_CHANNEL_MATCHES_ALIGNMENT.md).

The full Lean v4.36.0-rc2 build passed (9,203 jobs), and all 3,123
theorem/lemma declarations passed the actual axiom audit with only
`propext`, `Classical.choice` and `Quot.sound`. All 838 distinct
coverage/finding names were checked directly by Lean. Coverage remains
48 / 167, with 37 confirmed improvements. Original source bytes are
preserved; no manuscript revision or Palomar registration is made.

Validated finite matching checkpoint for T2.6/T1.11 and P1-MATH-0037:
[84c4c9a4016ce9f1c4ab9f7828675f3495eced85](https://github.com/Vulkin-prog/paper-p1-lean/commit/84c4c9a4016ce9f1c4ab9f7828675f3495eced85).


## P1-MATH-0038 — Explicit bounds for actual matches and physical fractions

- Location: companion T2.6, page 22, `p1:arith:fixed-channel-rank`,
  and T1.11, page 15, `p1:arith:palmrank`. Primary source hash:
  `8dd614c19e50df20ed1eb9f3ab37c07386f1ce3665c3499e26d83211ceab60b9`.
- Original form: actual matches are bounded by B*gamma+O(1), with
  B/b+O(1) in the physical cases and an implicit true-window bridge.
- Improvement: the literal actual target-position set has cardinality
  at most B*gamma+3 under the source/target affine identities and
  positive joint mass for the distinct target/source pairs. Each
  physical fraction has the sharper bound B/b+2. The good-edge
  definition supplies a positive integer source parameter.
- Evidence: `ExactMatchCongruences.one_family_congruence`,
  `ActualNormalizedMatches.integerOffsets_subset`, `cardinal_le_classes`,
  `CompatibleWindowOverlap.compatible_pair_overlap_le_one`,
  `PhysicalNormalizedMatches.physical_card`, `physical_a_bound`,
  `physical_b_bound`, `CompatibleTargetMatches.goodEdge_parameter`,
  `compatible_match_bound` and `compatible_triple_match_bound`.
- Suggested revision: define the actual matching set, inject it into
  the two affine classes, and handle the two physical cases using the
  true windows. State the explicit finite constants; no optimality of
  these additive constants is asserted.

At this initial checkpoint residual normalized rank and endpoint estimates
remained open. Later aligned and dyadic checkpoints below extend it. Neither
T2.6 nor T1.11 is counted complete. The result counts actual positions
and does not assert that the count equals a rank loss. See
[alignment](ACTUAL_TARGET_MATCHES_ALIGNMENT.md).

The full Lean v4.36.0-rc2 build passed (9,213 jobs), and all 3,144
theorem/lemma declarations passed the actual axiom audit with only
`propext`, `Classical.choice` and `Quot.sound`. All 859 distinct
coverage/finding names were checked directly by Lean. Coverage remains
48 / 167, with 38 confirmed improvements. Original manuscript bytes
are preserved; no manuscript revision or Palomar registration is made.

Validated actual matching checkpoint for T2.6/T1.11 and P1-MATH-0038:
[4212bf9ec45186af0f1ce85ed9a6fea00542775e](https://github.com/Vulkin-prog/paper-p1-lean/commit/4212bf9ec45186af0f1ce85ed9a6fea00542775e).


## P1-MATH-0039 — Uniform aligned rank from one unit without separation

- Location: companion T1.9, page 14, `p1:arith:alignedrank`,
  `companion_sections/arithmetic_appendix.tex:770`; original hash
  `7de9608ecc780ef5a448579b04b2ebeabe5e1157579ce3025b0303a047157acc`.
- Original assumptions: separated aligned windows of reduced height
  b<=B^3; the residual component argument is asymptotic.
- Improvement: one actual normalized unit suffices for a uniform
  full pair deficiency <=(u-1)+epsilon*B. With positive coprime a<=b,
  the bound is also L/b+epsilon*B. Separation, affine compatibility
  and local regularity are unnecessary. This full deficiency includes
  internal local defects and bounds the actual intersection rank.
- Finite evidence: `EvenSquareSelection.cardinal_gt`,
  `ComponentParityCode.kernel_even`, `kernel_square`,
  `SmallComponentBound.finite_count`, `PrimeRowComponents.free_component_parity`,
  `PrimeComponentCount.large_vertex_budget` and
  `TwoProgressionResidualRank.finite_rank_bound`.
- Uniform evidence: `PrimeFactorBudget.exceptional_budget`,
  `ResidualComponentRank.residual_rank_sublinear`,
  `TwoProgressionSublinear.rank_sublinear`,
  `NormalizedPairResidual.rank_sublinear`,
  `NormalizedPairRankLoss.loss_le_units_add_residual` and
  `AlignedPairRank.units_residual_bound`, `channel_bound`,
  `actual_intersection_bound`.
- Suggested revision: separate this one-unit result from separation
  and compatibility, and give the explicit finite component bound.
  The parity row of the component code is its actual value-set size
  modulo two. The large-component denominator is K+1.

At this initial checkpoint the fixed-height enlarged-cutoff assertion
remained open. Its later completion is recorded below. The target quotient-rank and endpoint
bridges needed by T1.11/T2.6 are also separate work. See
[alignment](ALIGNED_RESIDUAL_RANK_ALIGNMENT.md).

The full Lean v4.36.0-rc2 build passed (9,245 jobs), and all 3,206
theorem/lemma declarations passed the actual axiom audit with only
`propext`, `Classical.choice` and `Quot.sound`. All 921 distinct
coverage/finding names were checked directly by Lean. Coverage remains
48 / 167, with 39 confirmed improvements. Original manuscript bytes
are preserved; no manuscript revision or Palomar registration is made.

Validated uniform residual checkpoint for T1.9 and P1-MATH-0039:
[df34686b343f5297c181e6150e21834acc335ad8](https://github.com/Vulkin-prog/paper-p1-lean/commit/df34686b343f5297c181e6150e21834acc335ad8).


## Completion of companion T1.9

The fixed-height assertion is now closed, in addition to the uniform
part validated with P1-MATH-0039. The exact large-prime value kernel is
supported on actual defective interval values. Its rank is bounded by
their count, giving O(B/log B) for all enlarged cutoffs 2bL<=H<=D B.
The constant is chosen before the critical-band width. Separation,
compatibility and local regularity remain unnecessary. The full-kernel
and (u-1)+K*B/log B pair-deficiency bounds are also proved.

Evidence: `IntervalResidualKernel.mem_largeKernel_iff`,
`coefficient_zero`, `restriction_injective`, `rank_le_interval_defects`,
`FixedHeightResidual.large_kernel_rate`, `full_kernel_rate`,
`AlignedPairTheorem.fixed_height_loss` and `companion_T1_9`.
See [complete alignment](ALIGNED_RESIDUAL_RANK_ALIGNMENT.md).

T1.9 is counted complete. Coverage is 49 / 167 (main 16 / 73,
companion 33 / 94), with 39 confirmed improvements. The full Lean
v4.36.0-rc2 build passed (9,253 jobs), as did the actual axiom audit
of all 3,218 theorem/lemma declarations and all 933 distinct
coverage/finding names. No manuscript revision or Palomar registration
is made. The original P1-MATH-0039 validation remains historical.

Validated complete companion T1.9:
[6165382c14d6f8e653ddec27accb9c042628ae10](https://github.com/Vulkin-prog/paper-p1-lean/commit/6165382c14d6f8e653ddec27accb9c042628ae10).


## P1-MATH-0040 — Explicit finite dyadic exceptions and target counts

- Location: proofs of companion T2.6, page 22, and T1.11, page 15.
  Primary original statement hash:
  `8dd614c19e50df20ed1eb9f3ab37c07386f1ce3665c3499e26d83211ceab60b9`.
- Original form: rational separation at polynomial height, with
  B^{O(1)} endpoint-source and target counts.
- Improvement: t>2H(B+1) gives the weak dyadic fraction bounds for
  actual source labels and target equation d*z=c*t+h, d<=H, |h|<=H.
  Endpoint equalities force strips of radius B+2H. A literal containing
  source family has at most B^2*(2(a+b)*(B+2H)+2) pairs. If H<=B^J,
  J>=1, this is at most (6(a+b)+2)*B^(J+2). The decoded target pool
  for one fixed source parameter has at most 6aB^(3J) targets.
- Evidence: `DyadicTargetInterior.weak_ratio_bounds`, `lower_endpoint`,
  `upper_endpoint`, `ActualDyadicInterior.parameter_large`,
  `DyadicEndpointPairs.exceptional_card`,
  `PolynomialEndpointBudget.exceptional_polynomial`,
  `DyadicTargetCount.actual_target_mem_pool`, `pool_card_polynomial`,
  `CriticalPolynomialScale.source_size_eventually` and
  `DyadicMatchingArithmetic.uniform_core`.
- Actual matching bridge: `SeparatedTargetMatches.match_bound` and
  `DyadicMatchBound.separated_bound` prove B*gamma+3 outside the
  literal exception family using deterministic separation. Positive
  actual joint mass provides one sufficient separation condition.
- Suggested revision: state these finite integer inequalities, actual
  exception sets and polynomial exponents before the asymptotic rank
  argument. A separate numerator-height assumption is unnecessary for
  the target pool: c<=2a*d follows from the weak dyadic bound.

The theorem assumes explicit bounded affine target data. Their construction
from geometric alignment, the actual quotient-rank bridge and old prime
information remain open. T1.11 and T2.6 are not counted complete. No
optimality of the finite constants is asserted. See
[alignment](DYADIC_MATCHING_ALIGNMENT.md).

The full Lean v4.36.0-rc2 build passed (9,271 jobs); all 3,250 theorem/lemma
declarations passed the actual axiom audit with only `propext`,
`Classical.choice` and `Quot.sound`, and all 965 distinct coverage/finding
names were checked directly by Lean. Coverage remains 49 / 167, with
40 confirmed improvements. Original source bytes are preserved; no
manuscript revision or Palomar registration is made.

Validated bounded-affine dyadic checkpoint and P1-MATH-0040:
[1b87f9df9ba2c7a710a86f73443d39c7925abe63](https://github.com/Vulkin-prog/paper-p1-lean/commit/1b87f9df9ba2c7a710a86f73443d39c7925abe63).
