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


## Historical one-unit checkpoint for T1.9

The complete-source mapping recorded at this historical checkpoint was
later corrected; see the scope audit and full enlarged-alignment closure below.

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

The theorem assumes explicit bounded affine target data. At this initial
checkpoint their construction and the actual quotient-rank bridge were
separate unfinished work. P1-MATH-0041 below closes the finite rank and
old-prime-information bridge. T1.11 and T2.6 are not counted complete. No
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


## P1-MATH-0041 — Actual target rank from true matches and remaining rows

- Location: proofs of companion T2.6, page 22, and T1.11, page 15.
  Primary original statement hash:
  `8dd614c19e50df20ed1eb9f3ab37c07386f1ce3665c3499e26d83211ceab60b9`.
- Original form: a geometrically good source pair, an enclosing interval
  and an implicit passage from actual matches to relative rank; the
  extension by old prime information is stated separately.
- Improvement: the actual target deficiency is <=actual matching
  positions+rank of the literal remaining-row kernel on the true scaled
  old/new union. One source unit suffices for this finite rank step,
  without private-source coordinates, local regularity, compatibility
  or separation. Internal target defects and any old prime-coordinate
  span contained in the discarded row set are included.
- Generic evidence: `FiniteSetRelativeRank.matches_add_residual` holds
  over any division ring on actual finite sets. `EvenImageMap.image_map`
  and `MaskedParityRank.kernel_eq_rows`, `matches_add_residual`,
  `finite_loss_bound` prove the projected versions.
- Actual-window evidence: `ProjectedOldInformation.relative_kernel_le_masked`,
  `ScaledTargetValues.old_space`, `new_space`, `intersection_card`,
  `TargetWindowRank.deficiency_empty`, `kernel_rank_eq`, `finite_bound`
  and `interior_bound`.
- Residual evidence: `FiniteResidualRank.finite_row_rank_bound`,
  `ResidualComponentRank.row_rank_sublinear` and
  `TwoProgressionSublinear.row_rank_sublinear` strengthen the component
  bound to the whole solution space after discarded prime rows.
- Suggested revision: give the finite true-set quotient-rank inequality
  before invoking the residual estimate. Distinguish old even selections,
  the larger full old-value span used for the upper bound, and the
  discarded prime rows. The matching count is never asserted equal to
  rank loss.

The weakening concerns this finite rank step, not the entire source-mass
or Palm argument. Connecting the actual target-union geometry to the
uniform residual bound and constructing bounded affine data from geometric
alignment remain open. T1.11 and T2.6 are not counted complete. See
[alignment](TARGET_QUOTIENT_RANK_ALIGNMENT.md).

The full Lean v4.36.0-rc2 build passed (9,285 jobs); all 3,294 theorem/lemma
declarations passed the actual axiom audit with only `propext`,
`Classical.choice` and `Quot.sound`, and all 1,009 distinct coverage/finding
names were checked directly by Lean. Coverage remains 49 / 167, with
41 confirmed improvements. No manuscript revision or Palomar registration
is made; original source bytes are preserved.

Validated finite target quotient-rank checkpoint and P1-MATH-0041:
[469f5ac7ab234cdd18962337291971682554d913](https://github.com/Vulkin-prog/paper-p1-lean/commit/469f5ac7ab234cdd18962337291971682554d913).


## Formalization scope correction — T1.9

The previous complete mapping of T1.9 was too broad. The verified Lean
statements assume an actual normalized unit; the manuscript's enlarged
geometric alignment also allows zero units. The proofs remain valid,
and the wrapper is renamed `AlignedPairTheorem.one_unit_T1_9`. Source
coverage is corrected to 48 / 167 until the zero-unit case and enlarged
geometry are closed. This is a correction to the formalization ledger,
not a new mathematical finding about the manuscript. P1-MATH-0039
continues to record the valid one-unit subcase with its literal scope.
See [scope audit](FORMALIZATION_SCOPE_AUDIT.md).

## P1-MATH-0039 extended — full enlarged alignment, including zero units

The original source uses |b*x-a*y|<=(a+b)B and permits u=0. That literal
condition now replaces the earlier extra one-unit premise. In the
orientation a<=b, the true normalized union lies within radius 3bB
of b*x. The resulting Runge--Hamming--graph estimate bounds the full
residual uniformly over all heights max(a,b)<=B^3.

For u=0, the full span has dimension at most the sum of its two even
spaces plus two. Rank-nullity on the actual disjoint union gives
pairLoss<=rank(valueKernel). Together with the one-unit argument this
proves pairLoss<=(u-1)_++residual for every unit count. Both orientations
are handled explicitly, giving the L/max(a,b)+o(B) bound and the actual
intersection-rank bound. Separation and compatibility are unnecessary.

At fixed height Q, every enlarged cutoff
6*max(a,b)*B<=H<=D*B has actual large-prime kernel rank <=K*B/log B,
with K chosen before the critical-band width. The full-kernel and pair
loss versions follow. Evidence includes `EnlargedPairGeometry`,
`NormalizedPairRankLoss.loss_le_units_add_residual_all`,
`EnlargedAlignedResidual`, `EnlargedFixedHeightResidual` and
`EnlargedAlignedPairTheorem.companion_T1_9`.

This extends the existing improvement P1-MATH-0039, without counting the
coverage correction as a new manuscript finding. Coverage is now 49/167,
with 41 confirmed improvements. The full build passed (9,295 jobs), all
3,319 theorem/lemma declarations passed the actual axiom audit, and all
1,034 coverage/finding declaration names were checked directly. Only
propext, Classical.choice and Quot.sound occur. Original sources remain
unchanged; no manuscript revision or Palomar registration is made.

Validated full enlarged-alignment T1.9 (9,295 build jobs; 3,319 audited
declarations; 1,034 directly checked coverage/finding names):
[e4d183ed6e300f0352f6164c1c049cadfe0c0db4](https://github.com/Vulkin-prog/paper-p1-lean/commit/e4d183ed6e300f0352f6164c1c049cadfe0c0db4).

## P1-MATH-0040 and P1-MATH-0041 extended — complete geometric target rank

The canonical target data are now constructed from literal enlarged
alignment with the compressed source, rather than assumed. Reduction by
the actual gcd preserves the affine equation and reduces displacement.
For B>=2D, the reduced denominator and displacement are <=B^5.
This gives an explicit 6*a*B^15 target count and symmetric endpoint
source exceptions of cardinality <=(12(a+b)+4)*B^7.

The true combined source/target union has radius <=4*a*b*H*B and at
most 3B distinct values. Its two-progression cover is used for residual
rank, while the true old set alone is used for actual matches. The
literal discarded prime rows and all polynomial-height coefficients have
proved budgets. The uniform Runge--Hamming residual now applies to this
actual union, closing the asymptotic quotient-rank argument.

One source unit suffices without private coordinates, local regularity
or source affine compatibility. Both orientations and all old prime bits
of a,b are included. The resulting deficiency is the literal new-window
quotient expression, including internal defects. Actual compatibility
of a distinct target supplies deterministic separation. The source-family
bridge covers raw geometric good pairs independently of event compatibility.

Evidence: `TargetUnionGeometry`, `TargetUnionResidual.row_rank_sublinear`,
`TargetQuotientRank.bounded_affine_rank`, `ReducedAffineData.reduce`,
`CompressedTargetAlignment.bounded_data`, `AlignedTargetRank.uniform_core`,
`AlignedTargetSourceTheorem.uniform_source_bounds`, `uniform_both`,
`geometric_good_source_units`, `companion_T1_11` and `companion_T2_6`.
The exact coefficient bounds and leading values are included in the wrappers.

T1.11 and T2.6 are complete. Coverage is 51/167, with 41 confirmed
improvements; this is an extension of two existing findings. The full
build passed (9,309 jobs), all 3,344 theorem/lemma declarations passed
the actual axiom audit, and all 1,059 coverage/finding names were checked
directly. Only propext, Classical.choice and Quot.sound occur. No
optimality of the explicit polynomial counts, rank bound or Palm bound is
claimed. Original sources are preserved. No manuscript revision or
Palomar registration is made.

Validated complete T1.11/T2.6 (9,309 build jobs; 3,344 audited declarations;
1,059 directly checked coverage/finding names):
[3cc9dc9f816193e9488d32fab93f7aae9f9b6f90](https://github.com/Vulkin-prog/paper-p1-lean/commit/3cc9dc9f816193e9488d32fab93f7aae9f9b6f90).

## P1-MATH-0042 — Replace known-line extraction by the proved residual

- Source: article Proposition 13.7, page 33, `p13:rig:aligned`,
  `main_sections/pair_rigidity.tex:331`, original hash
  `f35f1d523724f58d47358f9401d9a7d7ac65506632395e176199769a7b446a1e`.
- Original proof: short-basis extraction, two norm-polynomial witnesses,
  substitution on the known line and a fixed tau extraction loss.
- Improvement: T1.9 directly gives full pair deficiency
  <=L/max(a,b)+o(B). For fixed tau in (0,1), choose the residual margin
  (2/3)*log(1/tau). The first displayed article bound then holds eventually
  with zero additional error. This does not claim uniformity when tau
  varies with N.
- Height one: actual compatibility forces at most one common true value,
  including contact at exactly L. Thus (u-1)_+=0, giving full pair loss
  and actual intersection rank o(B). At larger height the channel bound
  gives B/2+o(B) uniformly.
- Evidence: `KnownAlignmentRank.height_one_units`, `quantitative_bound`,
  `height_one_bound`, `compatible_half_bound` and `main_13_7`.
- Suggested revision: replace the known-alignment proof by this residual
  corollary and exact contact argument. Keep short-basis and curve
  machinery for the nonaligned arguments, which remain unfinished.

This is reuse of the proved T1.9 estimate, not an independent new residual
theorem. The full pair deficiency retains internal local rank defects.
All three assertions of article 13.7 are complete in both orientations.
Coverage is 52/167, with 42 confirmed improvements. The full build passed
(9,311 jobs), all 3,349 theorem/lemma declarations passed the actual axiom
audit, and all 1,064 coverage/finding names were checked directly. Only
propext, Classical.choice and Quot.sound occur. No manuscript revision
or Palomar registration is made.

Validated complete article 13.7 and P1-MATH-0042 (9,311 build jobs;
3,349 audited declarations; 1,064 directly checked coverage/finding names):
[0b7945eff438d61604f6a3aea0bc33f7263372e9](https://github.com/Vulkin-prog/paper-p1-lean/commit/0b7945eff438d61604f6a3aea0bc33f7263372e9).

## P1-MATH-0043 — Exact channel selections and arbitrary integer shifts

- Context: unnumbered calculation before article Theorem 3.3, page 16,
  equation `p1:arith:channelidentity`, `main_sections/arithmetic.tex:139`.
  The numbered source statement hash is
  `2129f1e0418039211e95fa065f6ae434fe46849de797ea291acb0e08da94b412`.
- Generality: the closed finite formula holds for every integer shift s
  and arbitrary integer coefficients L,a,b,r with L=b*m+r and m>=1.
  The original s=-1 and s=1 cases are specializations. No coprimality,
  positivity or Euclidean remainder restriction is needed for this algebra.
- Counting interpretation: an explicit equivalence with the interior
  zero-sum space proves the actual endpoint-selected even-selection count.
  Literal placements have count L+1-D and signed sum L-1-D for D<=L.
  Contact at D=L contributes -1, and larger diameters have no placements.
  The resulting pair products equal the actual finite U/S definitions.
- Evidence: `ChannelSelectionCount.endpoint_card`, `weight_eq_endpoint_card`,
  `ChannelPlacements.exact_contact`, `unsigned_pair_sum_eq`,
  `signed_pair_sum_eq`, `ChannelSumIdentity.moments`, `channel_identity`,
  `euclidean_identity`, `signed_two_three` and `signed_three_four`.
- Suggested revision: state the arbitrary-shift algebraic identity once,
  give the precise selection/placement interpretation, and keep m=0 as
  an explicit empty-sum boundary. Every finite lower-order term remains.

This is preparatory to article 3.3 and companion T2.5. Neither numbered
arithmetic profile/mass statement is counted complete. Their translation
counts, exceptional hosts, asymptotic estimates and phase equivalents
remain open. Coverage stays 52/167, with 43 confirmed improvements.
The full build passed (9,317 jobs), all 3,375 theorem/lemma declarations
passed the actual axiom audit, and all 1,090 coverage/finding names were
checked directly. Only propext, Classical.choice and Quot.sound occur.
No manuscript revision or Palomar registration is made.

Validated finite channel checkpoint and P1-MATH-0043 (9,317 build jobs;
3,375 audited declarations; 1,090 directly checked coverage/finding names):
[67187ee05582f888683838e0d09f0509a0157867](https://github.com/Vulkin-prog/paper-p1-lean/commit/67187ee05582f888683838e0d09f0509a0157867).

## P1-MATH-0044 — Actual dyadic translations with explicit height-uniform error

- Source: companion T2.5, page 22, `p1:arith:fixed-channel-mass`,
  `companion_sections/supplemental_arithmetic.tex:164`, original hash
  `3f277bcb49753b0c57c75eaa012cdfc127c5f3253a66fb6fe0c40707b4e533e4`.
- Original step: N*w(a,b) translations per within-window placement, up to
  implicit endpoint errors, with w=2*(2a-b)/(a*b).
- Improvement: the literal ceiling interval, actual source-pair bijection
  and both orientations are proved. At N>=(a+b)B, the one-orientation
  error is <=B/a+B/b+1. For strict inequality the orientation families
  are disjoint, giving two-orientation error <=2*(B/a+B/b+1)<=6B.
- Uniformity: one critical-band threshold precedes all reduced a<b<2a
  with b<=B^3 and all actual source-unit index choices. Both leading
  coefficients are exactly 1/3. Negative predecessor offsets are retained.
- Evidence: `SourceTranslationInterval.mem_translations`,
  `translation_count_error`, `ActualSourceTranslations.translations_card`,
  `source_pair_order`, `symmetric_card_error`, `leading_coefficients`,
  `SourceTranslationCount.all_heights` and `leading_counts`.
- Suggested revision: use this exact finite interval and error bound in
  the translation step, and distinguish counts at fixed indices from a
  union over all index witnesses.

The relation-word sum, actual probability/mass bridge and defective
normalizations remain open. Neither article 3.3 nor companion T2.5 is
counted complete. Coverage stays 52/167, with 44 confirmed improvements.
The full build passed (9,323 jobs); all 3,394 theorem/lemma declarations
passed the actual axiom audit, and all 1,109 coverage/finding names were
checked directly. Only propext, Classical.choice and Quot.sound occur.
Original sources are unchanged. No manuscript revision or Palomar
registration is made.

Validated actual translation checkpoint and P1-MATH-0044 (9,323 build jobs;
3,394 audited declarations; 1,109 directly checked coverage/finding names):
[fc4c31d1a01ccb880d28fa6cdbd1d30040e054df](https://github.com/Vulkin-prog/paper-p1-lean/commit/fc4c31d1a01ccb880d28fa6cdbd1d30040e054df).

## P1-MATH-0044 extended — weighted canonical-pattern translation error

The fixed-placement dyadic count is now summed over the exact finite
pattern family: a positive unit gap, both actual within-window placements,
weight A_d and the product of the actual predecessor signs. The dependent
sum and literal nested sums are identified. Their positive and signed
weights are exactly U and S, with U>=0 and |S|<=U.

The finite translation aggregate therefore satisfies

    |unsignedHosts-N*w*U| <= 6B*U,
    |signedHosts-N*w*S|   <= 6B*U.

The signed main term is retained; only its error is controlled by the
positive sum. Empty sums and all finite boundary terms are included.
One critical-band threshold precedes all reduced a<b<2a, b<=B^3 and
all patterns. Evidence: `WeightedTranslationError.weighted_error`,
`ChannelWordHosts.pattern_sum`, `unsigned_weight_total`,
`signed_weight_total`, `signed_abs_le_unsigned`, `unsigned_error`,
`signed_error` and `ChannelWordHostCount.all_heights`.

This extends the existing quantitative translation finding, so there
are still 44 confirmed improvements. The aggregate has not yet been
identified with the actual complete unit-relation/Fourier or probability
contribution. Those bridges and defective-normalization removal remain
open; article 3.3 and T2.5 remain in progress. Coverage stays 52/167.
The full build passed (9,329 jobs), all 3,409 theorem/lemma declarations
passed the actual axiom audit, and all 1,124 coverage/finding names were
checked directly. Only propext, Classical.choice and Quot.sound occur.
No manuscript revision or Palomar registration is made.

Validated weighted canonical-pattern checkpoint (9,329 build jobs;
3,409 audited declarations; 1,124 directly checked coverage/finding names):
[88ce8a72b7b579b3b7442de98efd91af4b445764](https://github.com/Vulkin-prog/paper-p1-lean/commit/88ce8a72b7b579b3b7442de98efd91af4b445764).

## P1-MATH-0035 extended — exact common classes and even-unit coefficients

For actual finite private values S union T, the equality
space(S) cap space(T)=space(S cap T) is now proved. Its actual even
coefficient map is bijective, yielding a linear equivalence. A finite
intersection-restriction sum lemma and an explicit zero-sum reindexing
transport the coefficients, rather than infer equality from dimensions.

Actual normalized units are proved bijective with the true deduplicated
intersection values. Hence, for positive coefficients and centres at least
two, the actual private pair intersection is linearly equivalent to even
selections of those units. Its rank and the full pair deficiency both
equal (u-1)_+, including zero and one unit. This classification needs
neither coprimality nor alignment height, separation or event compatibility.
The full union-image compression identity retains its shared-value premise.

Evidence: `FiniteIntersectionSums.restrict_sum`, `PrivateEvenIntersection.space_inter`,
`intersectionMap_injective`, `intersectionMap_surjective`,
`actual_intersection_rank`, `actual_pair_loss`, `EvenReindex.combination_reindex`,
`UnitIntersectionEquiv.unitValue_injective`, `unitValue_surjective`,
`unitIntersectionEquiv_apply` and `unitClassMap_injective`.
This extends the existing compression improvement, keeping 44 confirmed
findings. Affine characters, word enumeration, actual probability and
normalization errors remain open. Coverage stays 52/167. The full build
passed (9,337 jobs), all 3,425 theorem/lemma declarations passed the actual
axiom audit, and all 1,140 coverage/finding names were checked directly.
Only propext, Classical.choice and Quot.sound occur. No manuscript revision
or Palomar registration is made.

Validated exact unit-coefficient checkpoint (9,337 build jobs;
3,425 audited declarations; 1,140 directly checked coverage/finding names):
[4461d6bdcc7e19648377fe47703c3bd0d14d21ee](https://github.com/Vulkin-prog/paper-p1-lean/commit/4461d6bdcc7e19648377fe47703c3bd0d14d21ee).

## P1-MATH-0035 extended — actual predecessor signs and pair covariance

The actual affine character of an even true-window selection is now
proved to be its predecessor coefficient. For even exact-unit coefficients,
complete multiplicativity and zero-sum cancellation remove the dilation
constants. The paired character is precisely the sign of the sum of
both actual predecessor parities, evaluated at separate local witnesses.

An explicit finite bijection reindexes full-support two-block relations
by nonzero common vectors. Arbitrary actual local witnesses are permitted
in the square-class Fourier formula, with heterogeneous marginals retained.
The actual pair Bochner moment is identified with the actual covariance.
Composing this with the unit-intersection equivalence gives

    q_{x,y}-p^2 = p^2 * signedUnitSum,
    q_{x,y}     = p^2 * (1+signedUnitSum).

Privacy derives the full local ranks and p=2^-L. No joint compatibility,
separation, coprimality, dyadic membership or alignment height is needed.
Jointly incompatible pairs are included, with their sign cancellations.
Distinct centres are required only for the two-element finite-set
covariance and mass statements; the centered moment also permits repeats.

Evidence: `StartVertexSign.even_parity_evaluation`,
`UnitAffineSigns.paired_real_character`,
`PairFourierIntersection.full_support_family_sum`,
`PairSquareClassFourier.full_support_at`, `pair_moment_covariance`,
`PrivateUnitCovariance.private_marginals`, `common_sum_eq_unit_sum`,
`private_pair_centered_moment`, `private_pair_covariance` and `private_pair_mass`.

This extends the existing compression improvement; there remain 44 confirmed
findings. Actual selected-unit word enumeration, defective normalization
removal, baseline correction and the full mass/profile asymptotics remain
open. Neither article 3.3 nor companion T2.5 is newly counted proved.
Coverage stays 52/167. The full build passed (9,347 jobs), all 3,446
theorem/lemma declarations passed the actual axiom audit, and all 1,161
coverage/finding names were checked directly. Only propext,
Classical.choice and Quot.sound occur. No external input, Paper C port,
manuscript revision or Palomar registration is introduced.

Validated actual private pair covariance checkpoint (9,347 build jobs;
3,446 audited declarations; 1,161 directly checked coverage/finding names):
[c4d65eee4e0d0efc81a7e16fcc17538546ba5cdd](https://github.com/Vulkin-prog/paper-p1-lean/commit/c4d65eee4e0d0efc81a7e16fcc17538546ba5cdd).

## P1-MATH-0043 extended — actual word bijection and fixed-pair signed sum

The formal interpretation of A_d now reaches the actual exact units.
Nonzero even coefficient vectors correspond to nonempty even subsets.
Every such subset has unique selected extreme units, a positive primitive
gap d<=L/b and literal fitting placements. Actual primitive-step geometry
supplies all intermediate units. Endpoint-selected words reconstruct every
subset exactly once; injectivity, surjectivity and the coefficient inverse
are proved separately.

For d>0 there are exactly A_d such words at a fixed shape. Their predecessor
parities depend only on the first placement in each window. Therefore the
actual fixed-pair signed unit sum equals the integer finite shape sum of
A_d times both literal placement signs. This preserves cancellation and
includes empty/singleton unit families and diameter-L contacts. The
arithmetic bijection needs neither private coordinates, separation nor
joint compatibility. Its link to actual probability retains the private
normalized-union assumption of `PrivateUnitCovariance`.

Evidence: `BinaryEvenSelections.nonemptyEvenEquiv`,
`ExactUnitProgression.ordered_difference`, `stepUnit_injective`,
`SelectedUnitExtrema.canonical_gap`, `bounds_unique`, `selected_eq_stepUnit`,
`ChannelGapWords.weight_eq_word_card`, `word_sign`,
`SelectedUnitWordBijection.represent_selection`, `encode_injective`,
`encode_surjective`, `SelectedUnitFourierEnumeration.kernelEquiv_sign`
and `signed_unit_enumeration`.

The global dyadic-host reindexing, defective normalization removal,
baseline correction and full mass/profile asymptotics remain unfinished.
Article 3.3 and companion T2.5 remain in progress; coverage stays 52/167
with 44 confirmed improvements. The full build passed (9,361 jobs), all
3,492 theorem/lemma declarations passed the actual axiom audit, and all
1,207 coverage/finding names were checked directly. Only propext,
Classical.choice and Quot.sound occur. No new external input, Paper C
port, manuscript revision or Palomar registration is introduced.

Validated actual local word-enumeration checkpoint (9,361 build jobs;
3,492 audited declarations; 1,207 directly checked coverage/finding names):
[75b7018923d2fc85473e609a5788b6bb97805498](https://github.com/Vulkin-prog/paper-p1-lean/commit/75b7018923d2fc85473e609a5788b6bb97805498).

## P1-MATH-0044 extended — actual dyadic Fourier-word aggregation

Pair-specific fitting unit shapes are now explicitly bijective with
those global patterns carrying the corresponding actual source unit.
Finite sum interchange counts the literal dyadic source-pair set.
The two orientation source families are disjoint once N>(a+b)B.
Thus twice the actual forward dyadic signed unit sum equals signedHosts,
with exact signed main term N*w*S and error <=6B*U. One critical-band
threshold precedes every reduced positive a<b<2a with b<=B^3.

Evidence: `UnitShapePatterns.pattern_shape`, `shape_pattern`, `shape_sum`,
`DyadicUnitWordHosts.weighted_unit_hosts`, `integer_dyadic_sum`,
`signed_hosts_twice_forward`, `DyadicUnitFourierAggregate.pair_pattern_sum`,
`dyadic_unit_sum`, `symmetric_unit_sum`, `finite_signed_sum_error` and
`DyadicUnitFourierCount.all_heights`.

The aggregate is the actual rational-unit Fourier contribution, with
no guessed source multiplicity or assumed probability/mass bound.
Its actual covariance interpretation uses the already proved private
normalized-pair formula. On nonprivate hosts the complete covariance
is not identified with the rational-unit sum. Defective-normalization
removal, the baseline correction, full mass/profile estimates and phase
equivalents remain open. Article 3.3 and T2.5 remain in progress.

There are still 44 confirmed improvements and coverage stays 52/167.
The full build passed (9,369 jobs), all 3,506 theorem/lemma declarations
passed the actual axiom audit, and all 1,221 coverage/finding names were
checked directly. Only propext, Classical.choice and Quot.sound occur.
Current JSON impact/validation summaries for MATH-0035 and MATH-0043
have been synchronized with their earlier validated covariance and
word extensions, preserving their exact validation commits and histories.
No literature input, Paper C port, manuscript revision or Palomar
registration is introduced. Manuscript bytes are unchanged.

Validated actual dyadic unit-Fourier checkpoint (9,369 build jobs;
3,506 audited declarations; 1,221 directly checked coverage/finding names):
[74727a964e38c4b8b556fac2f93194485c695c11](https://github.com/Vulkin-prog/paper-p1-lean/commit/74727a964e38c4b8b556fac2f93194485c695c11).

## P1-MATH-0044 extended — actual normalized exceptions and rational-unit weights

For an actual finite set with distinct values at distance less than H,
privacy above the integer cutoff H is equivalent to nondefectivity of
every value. The true normalized union has diameter <=2bL, so H>=2bB
suffices. Failure supplies an actual H-defective normalized value.

At fixed source-unit indices and fixed normalized vertex index and
window, that value determines both centres injectively. A finite union
over 2B^3 such choices gives

    #badSources <= 2B^3 * #positiveDefectsBelow(H,b(2N+L)).

For each fixed positive a<=b and natural D, one critical-band threshold
precedes all lengths and H in [2bB,DB], giving #badSources<=N^(1/2+epsilon).
This does not put growing b or D after the threshold.

The actual rational-unit signed sum is independently bounded by
2^((u-1)_+)-1<=2^(B/b), with zero at u=0 or 1. No privacy or joint
compatibility is used for these weight bounds. A fixed unit choice has
at most N sources, giving a B^2*N count for all unit hosts. Sources are
actually separated under N>(a+b)B. This records the proved coarser
baseline, without claiming the source's sharper NB intermediate count.

Evidence: `NormalizedPrivateDefects.privateAbove_iff_nondefective`,
`normalized_dist_bound`, `normalized_private_iff`, `normalized_bad_witness`,
`NormalizedDefectSources.value_injective`, `bad_sources_subset`,
`bad_sources_card`, `NormalizedDefectSourceCount.bad_sources_rate`,
`UnitFourierWeight.abs_signed_unit_sum`, `unit_kernel_rank_bound`,
`signed_unit_sum_zero_of_card_le_one`, `abs_signed_unit_sum_le_rpow`,
`FixedChannelSourceGeometry.source_pairs_card`, `unit_sources_card`
and `source_separated`.

There remain 44 confirmed improvements and coverage stays 52/167.
The final retained private-channel mass calculation, baseline correction
and critical-scale phase estimates remain open. The full build passed
(9,379 jobs), all 3,525 theorem/lemma declarations passed the actual
axiom audit, and all 1,240 coverage/finding names were checked directly.
Only propext, Classical.choice and Quot.sound occur. No new literature
input, Paper C port, manuscript revision or Palomar registration is introduced.

Validated actual normalized exceptional-host checkpoint (9,379 build jobs;
3,525 audited declarations; 1,240 directly checked coverage/finding names):
[bd95627543139b4690c1311ce84f622d8ce7a221](https://github.com/Vulkin-prog/paper-p1-lean/commit/bd95627543139b4690c1311ce84f622d8ce7a221).

## P1-MATH-0045 — Finite actual channel mass without defective-pair residual nullity

- Source: companion T2.5, page 22, `p1:arith:fixed-channel-mass`,
  `companion_sections/supplemental_arithmetic.tex:164`, original hash
  `3f277bcb49753b0c57c75eaa012cdfc127c5f3253a66fb6fe0c40707b4e533e4`.
- Original removal step: use the defective host count together with a
  complete-pair nullity estimate L/b+o(L), then add a p^2 baseline using
  O(NB) possible source partners.
- Improvement: define the actual cutoff-private source family, retain
  probability-zero pairs, and prove its actual symmetric joint mass.
  Partition the full rational-unit sum before applying the private
  covariance identity. Its deleted terms have direct coefficient-space
  weight <=2^(B/b), without privacy or complete residual nullity.
- Exact formula: with F the full forward unit sum, V its bad-source sum
  and G the retained forward source count, M=p^2*(2F+2G-2V).
- Explicit finite error:

      |M-p^2*N*w*S| <= p^2*(6B*U+2B^2*N+2*#badSources*2^(B/b)).

- Scope: N>=2, L>0, positive reduced a<b<2a and N>(a+b)B; the integer
  cutoff H is arbitrary in this finite bound. The later square-root
  exceptional count retains the fixed-channel range 2bB<=H<=DB.
- Evidence: `PrivateChannelSources.mem_goodSources`, `good_sources_separated`,
  `orientation_disjoint`, `channel_mass_twice_forward`, `forward_mass_formula`,
  `PrivateChannelRemoval.signed_sum_partition`, `bad_signed_sum_bound`,
  `PrivateChannelMassBound.mass_exact_decomposition` and `finite_mass_error`.
- Suggested revision: use exact rational-unit deletion and its own
  cardinality bound in T2.5. Keep the residual-rank estimates for the
  other regimes that need them. Record the available B^2*N baseline
  honestly; the sharper NB intermediate count is not proved here.

This is a verified finite probability-mass reduction. The unsigned-sum
bound, critical-scale error comparison and positive phase equivalent
remain open, so T2.5 is not newly counted complete. Main 3.3 also keeps
its other regimes unfinished. Coverage stays 52/167 with 45 confirmed
improvements. The full build passed (9,385 jobs), all 3,538 theorem/lemma
declarations passed the actual axiom audit, and all 1,253 coverage/finding
names were checked directly. Only propext, Classical.choice and Quot.sound
occur. No new literature input, Paper C port, manuscript revision or
Palomar registration is introduced.

Validated actual finite channel-mass checkpoint (9,385 build jobs;
3,538 audited declarations; 1,253 directly checked coverage/finding names):
[37e67975065e2b4df18be484c2e7ba9123a6c8b9](https://github.com/Vulkin-prog/paper-p1-lean/commit/37e67975065e2b4df18be484c2e7ba9123a6c8b9).

## P1-MATH-0045 extended — explicit square-logarithmic actual mass remainder

The actual finite channel mass reduction now gives the stronger critical
remainder

    |M-p^2*N*w*S| <= K(C,b)*B^2/N,
    K(C,b)=(2^C)^2*(8*2^((C+1)/b)+2)>0.

The direct finite bound U<=B^2*2^floor(L/b) follows from the exact A_d
weight sum and literal placements. Explicit critical-band word/root
powers and nominal square probabilities combine with the actual bad
host count at exponent 7/12. Since positive a<b<2a implies b>=3, the
deleted contribution has exponent at most -13/12. The endpoint term
uses B<=N^(2/3), and the polynomial baseline is already B^2/N.

One threshold precedes all critical lengths and integer H in [2bB,DB]
for each fixed channel and fixed natural D. The coefficient K depends
only on C,b; a,D can affect the threshold. For every epsilon>0 a larger
threshold yields the paper's N^(-1+epsilon) remainder, even with eventual
coefficient one. Signed main terms and zero-probability retained pairs
are preserved throughout.

Evidence: `ChannelUnsignedBound.weight_sum_le`, `placement_card_le`,
`unsigned_upper`, `unsigned_upper_rpow`, `CriticalChannelPowers.word_upper`,
`window_root_upper`, `nominal_square_upper`,
`FixedChannelErrorAlgebra.error_scale`,
`PrivateChannelMassRate.massConstant_pos`, `mass_error_square_log`
and `mass_error_rpow`.

The positive phase equivalent and any real-cutoff convention transport
remain unfinished, so T2.5 is not newly counted complete. Main 3.3 keeps
its other regimes unfinished as well. Coverage stays 52/167 with 45
confirmed improvements. The full build passed (9,393 jobs), all 3,549
theorem/lemma declarations passed the actual axiom audit, and all 1,264
coverage/finding names were checked directly. Only propext,
Classical.choice and Quot.sound occur. No external input, Paper C port,
manuscript revision or Palomar registration is introduced.

Validated actual fixed-channel remainder checkpoint (9,393 build jobs;
3,549 audited declarations; 1,264 directly checked coverage/finding names):
[b19ae93509861774fd90f72c07a8d452603e5fc5](https://github.com/Vulkin-prog/paper-p1-lean/commit/b19ae93509861774fd90f72c07a8d452603e5fc5).

## P1-MATH-0043 extended — positive finite signed-channel bounds

For the exact Euclidean remainder r and quotient m>=1, the signed
formula is S=2^(m-1)*(A*m+T)-P with

    1<=A<=2b^2,    0<=T<=6b^2,    0<=P<=5b^2*m.

Consequently, for every positive a<b and L>=10b^3,

    L*2^floor(L/b) <= 8b*S,
    S <= 4b*L*2^floor(L/b),
    S>0.

Evidence: `SignedChannelLeadingBounds.coefficient_bounds`, `loss_bounds`,
`signed_formula`, `quotient_bounds`, `length_bounds` and `signed_positive`.
These give actual positive leading bounds, retaining r, without inferring
its sign from an unsigned estimate. The threshold is explicit and the
claim does not put growing b after a fixed-channel phase threshold.

## P1-MATH-0045 completed — full T2.5 with real cutoff and literal separation

The actual retained mass now has both source T2.5 assertions:
M=p^2*N*w*S+O(N^(-1+epsilon)) and M comparable to L*N^(-1+1/b).
The stronger explicit remainder <=K(C,b)*B^2/N is preserved.
Positive constants follow from the finite signed-sum bounds and exact
critical powers; the error is eventually at most half the positive
leading lower bound.

The literal source family uses a fixed real threshold D*B, D>=2b,
with a private prime coordinate on every distinct normalized value.
`privateAbove_floor` proves exact equality with its floor cutoff and
`cutoff_bounds` gives 2bB<=floor(DB)<=ceil(D)B. The separated source
family is defined literally, and its equality with the previously
summed family is proved eventually from actual source geometry.
Both orientations are the forward normalization and its swapped copy;
this makes the source's symmetric-channel convention explicit.
Actual infinite-measure probabilities are summed, with zero-probability
pairs retained.

Evidence: `ChannelMainTermBounds.main_term_bounds`,
`PrivateChannelMassPhase.phase_bounds`, `positive_phase`,
`RealPrivateChannelSources.privateAbove_floor`, `real_good_sources_eq`,
`cutoff_bounds`, `real_sources_separated`, `separated_mass_eq`,
`FixedChannelMassTheorem.eventual_mass_eq`, `strong_error`, `source_error`,
`source_positive_phase` and `companion_T2_5`.
The [alignment note](FIXED_CHANNEL_MASS_ALIGNMENT.md) compares the full
literal family and both source assertions. No residual-nullity bound
on defective pairs is used in this fixed-channel mass route.

Companion T2.5 is now complete. Coverage rises to 53/167, with 45
confirmed improvements. Article 3.3 remains in progress beyond this
fixed-channel input. The full build passed (9,405 jobs), all 3,577
theorem/lemma declarations passed the actual axiom audit, and all 1,292
coverage/finding names were checked directly. Only propext,
Classical.choice and Quot.sound occur. No new literature input, Paper C
port, manuscript revision or Palomar registration is introduced.
Original manuscript bytes are unchanged.

Validated complete companion T2.5 checkpoint (9,405 build jobs;
3,577 audited declarations; 1,292 directly checked coverage/finding names):
[b71d4e7409dccd61850024f99066ecaa24c6bccd](https://github.com/Vulkin-prog/paper-p1-lean/commit/b71d4e7409dccd61850024f99066ecaa24c6bccd).

## P1-MATH-0046 — Explicit actual selected-kernel counts and broader scope

Location: companion Lemma T1.6, page 9, `p1:arith:anchor`, source
`companion_sections/arithmetic_appendix.tex:416`. Both source assertions
are proved by `LargeSelectedKernelTheorem.companion_T1_6`.

The actual mixed-square relation forces each prime above B in a selected
anchor's odd support into the other window. Evenness is unnecessary.
The stronger finite pair family permits overlapping windows and both
orientations. If 2<=N and 1<=B<=N, the explicit bounds are

    #pairs <= 8*sqrt(3)*B*N^(3/2)*T^(-1/2+tau)
      * exp(2*sqrt(B)+(2^tau/tau)*B^(1-tau)),
    #windows <= 2*sqrt(3)*B*N^(1/2)*sqrt(T)*exp(2*sqrt(B)).

The bounds hold for every real T>0 and 0<tau<=1/2. The source separated
family is proved to be a subset of the finite pair family. All labels
include the predecessor. The residue count retains floor(N/r)+1 and
proves it at most 4N/r from r<=3N, also when r>N. A finite rough Euler
product and the already proved integer p-series tail replace an infinite
Euler-product identity. Uniform sublinear logarithmic exponentials give
the two source asymptotics under a single threshold before all lengths
and cutoffs. No target estimate is assumed.

The canonical-triple argument is generalized from the attributed Paper C
source; all code is rebuilt under Lean v4.36.0-rc2. No new unproved
literature input is introduced. See
[full statement alignment](LARGE_SELECTED_KERNEL_ALIGNMENT.md).
Coverage is 54/167, with 46 confirmed improvements. Main 3.2 and the
complete pair profile 3.3 retain their other unproved arithmetic regimes.
The full build passed (9,427 jobs) and all 3,626 declarations passed the
actual axiom audit, permitting only propext, Classical.choice and
Quot.sound. The original manuscript bytes are unchanged.

All 1,341 distinct coverage/finding declaration names were checked directly
by Lean against the compiled root import.

Validated complete companion T1.6 checkpoint (9,427 build jobs;
3,626 audited declarations; 1,341 directly checked coverage/finding names):
[3be7415366bd3d27aa016bf9690b0f93d7304fd9](https://github.com/Vulkin-prog/paper-p1-lean/commit/3be7415366bd3d27aa016bf9690b0f93d7304fd9).

## P1-MATH-0047 — Explicit receiver costs and the actual large-kernel tuple branch

Location: companion Proposition T1.14, page 17, `p1:arith:fixed-support`,
`companion_sections/arithmetic_appendix.tex:1035`. This checkpoint closes
its large-kernel branch, with full T1.14 still in progress.

The finite receiver cost is <=4^m*N^m/K for m receiving windows and
actual selected kernel K<=3N. Each group modulus divides K; this retains
and justifies every additive CRT term, also for moduli>N. The scaled
weighted tail allows (m*B)^omega(K) prime assignments. An injective actual
marked-anchor encoding and the union over all anchors give the stronger
tuple family bound N^(m+1/2+epsilon)*T^(-1/2+tau), uniformly in T>0.
The family permits non-even selections, repeated centres and overlaps.

The exact beta_s identity and the proved choice
tau=min(1/4,epsilon/(4*beta_s)) after epsilon give the source exponent
N^((m+1)-2s/(2s+1)+epsilon) for this branch. Evidence includes
`SeveralKernelReceivers.receiving_card`, `hits_card`,
`WeightedReceiverKernelTail.weighted_tail_exp`,
`SeveralAnchorConfigurations.configurations_weighted`,
`LargeKernelTuples.encode_injective`, `tuples_card`,
`LargeKernelTupleCounts.tuple_count`, `exponent_identity` and `large_branch`.

The all-small-kernel regime still needs T1.13/T1.5. Full compressed
fixed-width/dilation and relative-image assembly are also open. No
completed T1.14 coverage is claimed: coverage remains 54/167 with 47
confirmed improvements. No target count, new unproved literature input,
Paper C port or manuscript revision is introduced. See
[statement alignment](LARGE_KERNEL_TUPLES_ALIGNMENT.md).

The full build passed (9,441 jobs); the actual audit passed for all
3,655 theorem/lemma declarations, permitting only propext, Classical.choice
and Quot.sound. All 1,370 distinct coverage/finding declaration names
were checked directly by Lean. Original manuscript bytes are unchanged.

Validated large-kernel tuple-branch checkpoint (9,441 build jobs;
3,655 audited declarations; 1,370 directly checked coverage/finding names):
[8fa5f5d3988280093242c5b3fce68a506d9d1c80](https://github.com/Vulkin-prog/paper-p1-lean/commit/8fa5f5d3988280093242c5b3fce68a506d9d1c80).

### P1-MATH-0046 extension — Arbitrary selected fixed-width one-kernel blocks

The one-kernel argument now proves the first assertion of T1.13 for actual
positive subsets V(x) varying with the integer centre. Fixed-offset
positive-value injection gives

    #starts <= 2*#offsets*sqrt(X)*sqrt(T)*exp(2*sqrt(H)).

Logarithmic offset and cutoff budgets give one threshold before all
source sets, lengths and nonnegative real T. Real fixed width/height
coefficients are enlarged by proved ceiling inequalities; real prime
thresholds use exact floor equality of the actual selected family. No
lower centre bound, prime/diameter comparison or fixed subset pattern
is needed for this first assertion. Evidence is
`SmallKernelBlocks.fixed_offset_card`, `finite_exp_bound`,
`SmallKernelBlockCount.arbitrary_selected_blocks`,
`FixedWidthSmallKernel.one_kernel_real`, `realSelectedStarts_eq` and
`one_kernel_real_cutoff`.

Full T1.13 remains in progress because the distinct two-small-kernel
assertion is not proved. Numbered coverage stays 54/167, with 47
confirmed improvements. No new unproved literature input, Paper C port
or manuscript revision is introduced. See
[alignment](FIXED_WIDTH_SMALL_KERNEL_ALIGNMENT.md).

The full build passed (9,447 jobs); all 3,667 declarations passed the
actual axiom audit, permitting only propext, Classical.choice and
Quot.sound. All 1,382 distinct coverage/finding names were checked
directly by Lean. Original manuscript bytes are unchanged.

Validated selected fixed-width one-kernel checkpoint (9,447 build jobs;
3,667 audited declarations; 1,382 directly checked coverage/finding names):
[77be471d8c127edb6104caae2922aaef3a95ec54](https://github.com/Vulkin-prog/paper-p1-lean/commit/77be471d8c127edb6104caae2922aaef3a95ec54).

## P1-MATH-0048 — Direct coefficient-independent bivariate level-set count

Location: companion T1.4 Step 3, page 6, `p1:arith:reuss`, source
`companion_sections/arithmetic_appendix.tex:139`. The manual bounded-root
and exceptional-full-fibre argument can be replaced, once the eliminant
is constructed, by the proved Schwartz-Zippel finite-grid count.

If p is homogeneous of degree d>0 and c!=0, the actual level set p=c
in [-H,H]^2 has at most d*(2H+1) integer points. Zero constant coefficient
proves p-C(c) nonzero and subtracting the constant does not increase
degree. The result permits the zero polynomial and powers of linear
forms, without coefficient-height, primitivity or irreducibility
hypotheses. It enlarges a rectangular box to its maximum-coordinate
square box and preserves the source O(T1) or O(L1) contribution.

Evidence: all declarations in `BivariateGridCount`, in particular
`zero_grid_bound`, `sub_constant_ne_zero`, `shifted_degree_le`,
`homogeneous_grid_degree_bound` and `homogeneous_integer_box_bound`.
The proved Mathlib theorem is used at the pinned exact revision.
This is a preparatory ingredient: no completed T1.4 coverage is claimed,
and the determinant, eliminant construction and lattice stages remain
open. Coverage stays 54/167, with 48 confirmed improvements. See
[alignment](BIVARIATE_GRID_ALIGNMENT.md).

The full build passed (9,477 jobs); all 3,677 declarations passed the
actual axiom audit, permitting only propext, Classical.choice and
Quot.sound. All 1,392 distinct coverage/finding names were checked
directly by Lean. Available Ubuntu-root space is 17.75 GiB after the
selected dependency downloads. Original manuscript bytes are unchanged.

Validated bivariate grid checkpoint (9,477 build jobs; 3,677 audited
declarations; 1,392 directly checked coverage/finding names):
[227b402575302cfdd178e7820c980874611a57c5](https://github.com/Vulkin-prog/paper-p1-lean/commit/227b402575302cfdd178e7820c980874611a57c5).

### P1-MATH-0048 extension — Primitive denominator gcd and both signs

The source's primitive-coordinate denominator conclusion now has a
direct gcd proof for arbitrary exponents: q|R*a^m, q|Rprime*b^n and
gcd(|a|,|b|)=1 imply q|R*Rprime. Its actual signed denominator count
is <=2*tau(|R*Rprime|), uniformly subpolynomial at fixed polynomial
product height. A single threshold precedes all primitive coordinates,
exponents and finite denominator families. No coordinate-height bound
is needed for this arithmetic ingredient. Evidence: all six declarations
in `PrimitiveDenominators`, including `dvd_product_int`,
`finite_denominator_count` and `polynomial_height_count`.
Actual resultant/eliminant construction and the full determinant
argument remain open. No additional numbered result is claimed.

The full build passed (9,479 jobs); all 3,683 declarations passed the
actual axiom audit, permitting only propext, Classical.choice and
Quot.sound. All 1,398 distinct coverage/finding names were checked
directly by Lean. Original manuscript bytes are unchanged.

Validated primitive denominator checkpoint (9,479 build jobs;
3,683 audited declarations; 1,398 directly checked coverage/finding names):
[a2aa7351c69460372795ffbe55fc41123821d382](https://github.com/Vulkin-prog/paper-p1-lean/commit/a2aa7351c69460372795ffbe55fc41123821d382).

### P1-MATH-0048 extension — Actual two-chart resultant construction

Homogeneous Bezout and exact padded coefficient reflection now derive
the two coordinate-power divisibilities from actual integer form
evaluations. Primitive cancellation gives q dividing the actual product
of chart resultants. Univariate coprimality over Q and an explicit
full-degree condition prove nonvanishing of padded resultants. The
finite signed denominator family may have different primitive coordinate
witnesses for each q. Its count remains <=2*tau(|R*Rprime|), uniformly
N^epsilon at fixed product height. Evidence: all ten declarations in
`ResultantDivisibility`.

This closes the independent resultant identities; source chart extraction,
nondegeneracy and uniform height, eliminant construction and full T1.4
remain open. Coverage stays 54/167, with 48 confirmed improvements. See
[actual resultant alignment](RESULTANT_DENOMINATORS_ALIGNMENT.md).

The full build passed (9,489 jobs); all 3,693 declarations passed the
actual axiom audit, permitting only propext, Classical.choice and
Quot.sound. All 1,408 distinct coverage/finding names were checked
directly by Lean. Original manuscript bytes are unchanged.

Validated actual chart-resultant checkpoint (9,489 build jobs;
3,693 audited declarations; 1,408 directly checked coverage/finding names):
[582ea278507fd72b88e47d7dbae9d30ff064f179](https://github.com/Vulkin-prog/paper-p1-lean/commit/582ea278507fd72b88e47d7dbae9d30ff064f179).

## P1-MATH-0049 — Actual bidegree-one primitive fibre count with broader height scope

Location: companion T1.4 Step 3, page 6, `p1:arith:reuss`, source
`companion_sections/arithmetic_appendix.tex:139`.

A canonical integer Bezout scale, its actual chart-resultant divisor
budget, a constructed homogeneous eliminant and an injective fixed-scale
fibre map prove the actual finite count

    #solutions <= 2*tau(|R*Rprime|)*(k+d*ell)*(2H+1).

The original equation may have any fixed bidegree (ell,k); the source
cases (2,1) and (1,2) are included. The actual scale is nonzero and both
signs are retained. A fixed scale and the remaining primitive pair
determine the eliminated pair uniquely. Zero or reducible eliminants
are handled by the nonzero-level grid theorem.

Explicit Sylvester bounds give |R*Rprime|<=((2d)!*B^(2d))^2. Auxiliary
coefficient height N^a therefore supplies the polynomial-height divisor
budget, rather than assuming a resultant estimate. Exact real-box floor
transport and real-exponent ceiling transport prove the actual
N^epsilon*H bound under one threshold before all source choices.
No height bound is needed on the original coefficient forms, the
nonzero shift or either box height in this local case.

Evidence: all declarations in `ResultantHeight`,
`BidegreeOneElimination`, `BidegreeOneFibreCount` and
`BidegreeOneCurveCount`. Full T1.4 retains its source auxiliary-form
extraction and nondegeneracy/coefficient height from determinant/lattice
construction, other curve cases and short-vector sums. Coverage stays
54/167, with 49 confirmed improvements. No new unproved literature input,
Paper C port or manuscript revision is introduced. See
[local case alignment](BIDEGREE_ONE_CURVE_ALIGNMENT.md).

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

## P1-MATH-0050 — A single homogeneous resultant controls the denominator

Location: companion T1.4 Step 3, page 6, `p1:arith:reuss`, source
`companion_sections/arithmetic_appendix.tex:139`.

The actual padded chart resultants R,Rprime have the same absolute
value, by exact reversal of the Sylvester rows and of columns inside
each degree-d block. Primitive cancellation in the two coordinate
power divisibilities gives q|R. The previous padded product had absolute
value |R|^2; no comparison with differently normalized native chart
resultants is assumed. The signed scale count is <=2*tau(|R|) and the
finite actual primitive point bound becomes

    #solutions <= 2*tau(|R|)*(k+d*ell)*(2H+1).

Nonzero R also implies nonzero Rprime. The actual real-box N^epsilon*H
count now needs only the first condition, which is derived from
univariate coprimality over Q and one polynomial attaining the padded
degree. The other chart needs no separate nondegeneracy premise.
Evidence: all declarations in `ReflectedResultants` and
`SingleResultantFibreCount`. The original coefficient/shift and real
height scope from P1-MATH-0049 is retained.

This remains the elementary remaining-pair-height bound. Its
complementary Heath-Brown estimate and the source determinant/lattice
construction are open. Full T1.4 coverage is not claimed; coverage
stays 54/167, with 50 confirmed improvements. No new unproved literature
input, Paper C port or manuscript revision is introduced. See
[alignment](SINGLE_RESULTANT_ALIGNMENT.md).

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
