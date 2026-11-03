# Mathematical corrections and improvements

Baseline: original P1 V1.6 article and companion, 31 October 2026, preserved in
`manuscripts/paper-p1/v1.6/`. This log is separate from the original package's
historical reviews and editorial revisions.

**151 mathematical improvements are confirmed; no error in a manuscript conclusion
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

## P1-MATH-0054 — Full quadratic-kernel counts and a precise exponent comparison

Both actual T5.1 counting branches, their minimum and the affine count are now
proved uniformly, including real endpoints and derived square-part/modulus
heights. The stronger capped exponent min(1,c2) is universally bounded by
the affine expression, avoiding the endpoint range issue. The uncapped
comparison is exact for beta-2delta<=2; an arbitrary positive margin is
proved for every actual admissible nonempty family. The unrestricted
abstract comparison fails at beta=5/2, delta=0. This is a range clarification,
not a counterexample to the manuscript counting estimate, whose proof
already uses beta<=2+o(1). The literal display remains unclaimed, so the
numbered row stays in progress. See
[full count and range alignment](QUADRATIC_KERNEL_COMPLETE_COUNTS_ALIGNMENT.md)
and the machine-readable finding for every checked declaration.

## Growing-degree budget verification checkpoint

The factorial prime-support, squarefree-divisor and prime-colouring budgets
used inside T5.2 are now proved with explicit uniform thresholds, including
a fixed cubic-loglog height error. These close source proof ingredients;
they are not claimed as a new mathematical improvement or a complete
numbered result. The number of confirmed improvements remains 54.
See [alignment](GROWING_DEGREE_PRIME_BUDGET_ALIGNMENT.md).

## Actual split-product height and support checkpoint

The previous growing-degree budget now applies to the literal q*D_A,
including signed offsets. The private-prime argument also proves the
actual linear-kernel support restriction. These verify source ingredients
and add no new improvement entry or numbered-result completion. The
confirmed-improvement count remains 54. See
[alignment](SPLIT_OFFSET_KERNEL_BUDGET_ALIGNMENT.md).

## P1-MATH-0055 — Odd degrees and polylogarithmic widths for fixed split-product kernels

The full actual fixed-kernel part of companion T5.2 is proved uniformly
with N^(2c log2+epsilon). This part only needs d>=2; it does not need
even d, and it permits every fixed polylogarithmic offset width. The
other, prescribed-divisor assertion retains its source scope and remains
open. Explicit two-linear-kernel quadratic fibres derive all heights,
including factorizable cases. See
[alignment](SPLIT_OFFSET_FIXED_KERNEL_ALIGNMENT.md) and the machine-readable
finding for every checked declaration. No change to the source exponent
or error in its asymptotic conclusion is claimed.

## P1-MATH-0056 — Exact square-overlap decomposition for arbitrary groupings

The source paired-kernel quotient relation is proved in stronger form:
M=q*R^2 with R|D_A for every disjoint grouping of nonzero linear
factors, with arbitrary block sizes and no even-degree restriction.
The prescribed-divisor count still uses quadratic blocks and is not
completed by this algebraic extension alone. See
[alignment](GROUPED_KERNEL_RESULTANT_ALIGNMENT.md) and the machine-readable
finding for every checked declaration.

## P1-MATH-0056 extension — Explicit general-block divisor allocation

The exact source prime-removal formula, removed-factor logarithmic loss
and actual pairwise coprime block allocation are now proved in the same
general-block scope. The actual divisor enumeration budget is also
closed from its derived height. This extends the existing finding and
adds no new improvement identifier. Full T5.2 remains open at the
selected quadratic counting step. See
[alignment](GROUPED_DIVISOR_ALLOCATION_ALIGNMENT.md).

## P1-MATH-0056 extension — Explicit selected-block error and fixed partitions

An actual pair partition and selected block now give the finite error
4*log(D_A)/(d/2), uniformly absorbed in the source growing-degree
regime. The partition can be fixed before counting solutions under a
common threshold. This extends the existing finding and adds no new
improvement identifier. The final shifted counting/enumeration remains
open. See [alignment](SELECTED_QUADRATIC_BUDGET_ALIGNMENT.md).

## P1-MATH-0054 extension — Uniform wider-range and shifted quadratic counts

The actual affine bound is now proved on N/2<=x<=3N and for actual
two-factor integer-offset blocks, via an exact injective shift. All
new square-part/modulus heights and finite constants are derived. The
unqualified uncapped comparison remains unclaimed; no new improvement
identifier or numbered-result completion is added. See
[alignment](SHIFTED_QUADRATIC_COUNT_ALIGNMENT.md).

## P1-MATH-0057 — Cumulative prescribed split-product kernel count

Full T5.2 is proved with both advertised actual counts. The prescribed
divisor estimate also holds for the cumulative family sf(P_A(n))<=N^beta,
and any fixed comparison factor, without the source lower size condition.
All cell counts and finite enumeration costs are proved; no target-count
premise is used. Both conclusions extend to fixed polylogarithmic widths
(P1-MATH-0055); odd degrees remain specific to the fixed-kernel assertion.
See [complete alignment](PRESCRIBED_SPLIT_PRODUCT_ALIGNMENT.md) and the
machine-readable finding for all declarations. Coverage is 57/167.

The complete T5.2 count includes every fixed comparable positive interval,
with a common threshold before varying source data. The interval transfer
uses an exact scale-independent power profile, so no nonuniform factor in
beta is introduced and the c coefficient is preserved. The real-bounds
formulation also verifies positivity and the literal signed-product
identity. Earlier open-stage entries for T5.2 above are closed by this
checkpoint; they remain as development history.

## P1-MATH-0058 — Choose only a minimum-degree last exposure

The finite correction is exactly sum_S(1-|S|/2)*alpha_S+beta_last/2.
Choosing the last index with minimum weighted degree suffices; no average
over all permutations is needed. The finite lemma works for every
nonnegative weighted family of subsets of size >=2, including odd sizes.
An actual injective exposure rank and its precise earlier-pattern weights
are constructed. At actual kernel height (KN)^d, the total exposure
exponent is <=v/2+log(K)/(2logN), with an explicit error independent of d.

Actual square-product tuples have the canonical unique even-pattern
decomposition, explicit prescribed divisors and last-kernel identity.
Their new coprime factor assignments are counted by an injective prime
code, with the proved growing-degree budget. The exact infinite-model
moment identity is also verified, including repeated tuple entries.
The full profile/prefix-state enumeration is still open, so Proposition
9.1 remains in progress and numbered coverage stays 57/167. See
[alignment](SHORT_MOMENT_ENUMERATION_ALIGNMENT.md).

P1-MATH-0058 closure: uniform size-profile enumeration and actual prefix-state
counts are now complete, so the minimum-degree last-index argument is
instantiated in the full moment and Lp proof of Proposition 9.1.

## P1-MATH-0059 — Arbitrary centre subsets and polylogarithmic widths in 9.1

The full source moment exponent holds for every finite subset of a fixed
comparable positive interval, without a lower size condition, and every
fixed polylogarithmic offset width. Both v and the degree retain their
source evenness hypotheses. Repeated tuple entries are included exactly.
The actual sum is measurable and in every Lp. The explicit choice
c=epsilon*v/(2*[v*(v-1)+2]*log2)>0 is made before the fixed interval and
width constants and gives the actual lpNorm and eLpNorm conclusions.
Uniform positivity identifies the source signed polynomial exactly.

All profiles, prescribed centre counts, factor assignments, state
transitions and the last fixed-kernel fibre are proved and summed. No
count estimate is assumed. Proposition 9.1 is complete; 9.2 remains open.
Coverage is 58/167. See [alignment](SHORT_MOMENT_ENUMERATION_ALIGNMENT.md).

## P1-MATH-0060 — Only the number of old generators is needed in 9.2

The complete projected-list estimate is proved for any old generator set
of cardinality <=E*logN, independently of its geometry or value heights.
The old space is the full square-class span. Its density is positive with
exact mean and moments; the Holder cost is <=(2^|O|)^(r/v), absorbed by a
sufficiently large fixed even v. The actual 9.1 Lp bound then chooses c>0.
All short motifs and actual projected lists are counted, including repeated
centres and arbitrary fixed polylogarithmic widths. The source critical
block version follows from the union cardinality, with signed-product
positivity verified uniformly. No count or analytic inequality is assumed.

Corollary 9.2 is complete; coverage is 59/167. See
[alignment](SHORT_OLD_SPACE_PROJECTION_ALIGNMENT.md).

## P1-MATH-0061 — Uniform real-cap count for two small kernels

Full companion T6.1 holds in the stronger form #S<=Q*N^epsilon, with a
threshold before every real cap Q>=0. Actual kernel heights from the centre
interval permit a fixed polynomial divisor bound independently of Q. The
q version is uniform in every real q, including q varying with N. Cutoff
and window radius are independent: H<=D*logN and any fixed polylogarithmic
width suffice, with no condition H>block diameter. The literal critical
B=L+1 source version and positivity are proved. All support, kernel-pair,
Pell-fibre, offset and interval-cover counts are proved and summed.
Coverage is 60/167; see [complete alignment](TWO_SMALL_KERNEL_ALIGNMENT.md).

## P1-MATH-0062 — A constant selection and squarefree moduli suffice in T6.2

The actual smooth-modulus exceptional set and its count are proved from
only t+26 distinct selected values. One uses full canonical square parts
and squarefree small odd-prime parts; at most one large square part is
removed, leaving 26 large parts after the fewer-than-t large kernels.
Their actual lcm exceeds the interval, and a squarefree first-passage
modulus gives a proved congruence certificate. All Rankin, divisor-code,
offset and centre-fibre counts are proved. The common deterministic set
and constant-selection threshold are independent of t,H and the selection.
Neither H>diameter nor H<=Y is needed. The full original long-selection,
real-cutoff and critical-block theorem follows, with source positivity.
Coverage is 61/167. See [complete alignment](LARGE_SMOOTH_MODULUS_ALIGNMENT.md).

## P1-MATH-0063 — A>1 and one common finite certificate degree bound

The full T6.3 certificate extraction and both actual directed degree bounds
hold for every fixed A>1. Only prime privacy needs that range; graph degree
counts alone need A>0. Actual logarithmic prime-pool budgets and the same
colored-subset tilt give B^t*(e*t*B)^k in both directions, with the minimal
first-passage order k=floor(log(Z)/logY)+1. The incoming pool-size case split
is unnecessary. Full old-span selections, overlaps and dependent sources
are included. A common critical radius proves the literal N*B threshold,
and positivity identifies every actual signed value. Coverage is 62/167;
see [complete alignment](ANCHOR_CERTIFICATE_ALIGNMENT.md). The separate
smooth-modulus lemma retains its A>=2 range.

## P1-MATH-0064 — Constant selection cutoff and full squarefree initial exception

The complete 10.1 induction uses the fixed threshold m=t+25, with
t=5(r+s-1)+1 at the relevant target order. Complete 9.2 handles every
all-short witness eventually, and constant-selection T6.2 handles every
remaining long selection. The initial two-kernel exception uses H=0,
hence complete squarefree kernels. The actual finite schedule j/(2J)
ends at one half exactly. Every one-/two-deletion count is instantiated
by strong induction with fewer new targets and all old-source counts.

The final effective-block theorem counts arbitrary finite candidate sets.
Active centre heights follow from actual value heights and logarithmic
width; empty old blocks can be recentered without changing their full
span. Actual even selections, absolute nonzero vectors and unrestricted
old spans are preserved. Full main 10.1 is complete, bringing coverage
to 63/167. See [complete alignment](CONDITIONAL_HALF_COUNT_ALIGNMENT.md).

P1-MATH-0064 consequence: main Corollary 10.3 is now fully instantiated
from 10.1. Actual equal-centre pairs are also counted separately through
active centres. Explicit fixed-logarithmic-width versions of both results
are proved. This adds no independent mathematical finding; the confirmed
count remains 64 and numbered coverage is now 64/167. See
[pair alignment](DEPENDENT_BLOCK_PAIRS_ALIGNMENT.md).

## P1-MATH-0065 — Separate coordinate relations suffice for the relative half-count

The full half-count holds when each new coordinate participates nontrivially
in some relation modulo the full old span. Different coordinates may use
different relations, with zero projections at other new coordinates. The
actual nonzero support of one relation is counted by complete 10.1; its full
value blocks are adjoined to the old sources. Exact sums preserve relative
participation for all remaining coordinates. Strong induction supplies every
actual remaining population uniformly in all old-source counts.

Canonical connectedness supplies a nonzero relation at every coordinate,
without asserting one global full-support relation. Actual generic connected
block tuples are therefore counted. The original-window/set-family and
independent-mass/primitive alignment in main 10.2 is still open, so coverage
remains 64/167. See [relative participation](RELATIVE_PARTICIPATION_ALIGNMENT.md)
and [connected-family progress](CONNECTED_FAMILY_ALIGNMENT.md).

P1-MATH-0065 closure: the generic connected host count is now aligned with
actual unordered original-window families. The source primitive/nullity
condition supplies an actual full-support relation. Both actual independent
masses are proved using the exact heterogeneous infinite-model marginals
and their proved common critical-band cap. Main 10.2 is complete; coverage
is 65/167 and confirmed improvements remain 65. The earlier generic-only
proof checkpoint is preserved in the finding's validation history. See
[complete connected-family alignment](CONNECTED_FAMILY_ALIGNMENT.md).

## P1-MATH-0066 — A half power for each nonzero block projection

Full T1.14 now has the stronger bound N^(r-s/2+epsilon). Split the actual
nonzero support, of size d>=s, from its k=r-d complementary centres.
The complement has at most O(N^k) choices and the complete conditional
half-count gives N^(d/2+epsilon) at each actual fixed complement. Actual
finite fibres and role codes give r-d/2<=r-s/2. The printed weaker
exponent follows from a proved comparison.

Actual original windows, arbitrary finite even-image blocks and fixed
normalized/compressed block shapes with literal height/radius data are
covered. The actual fixed offset/dilation code cardinal and all coded
records are counted and absorbed. Injectivity of the even-selection map
is unnecessary when actual image vectors are nonzero. Only the new
centre tuple must be injective; separation is not needed. All orders
and code dimensions remain fixed before N.

This complete proof bypasses the unfinished two-small-kernel determinant
estimate for T1.14. Its independent half-count dependency is acyclic.
The separate kernel estimates remain open for other uses. Coverage is
66/167 and confirmed improvements are 66. See
[complete support alignment](SEVERAL_BLOCK_RELATION_ALIGNMENT.md).

P1-MATH-0030 extension: its smaller deterministic exception set now has
the logarithmic cardinality Euler gain needed in T19.4. The literal source
rate is proved uniformly for all orders 1<=j<=log(N). The actual factorial
recurrence retains F_2, and the missing uniform initial pair estimate is
recorded separately; T19.4 remains in progress. No new independent finding
is counted. Coverage and confirmed improvements stay 66/167 and 66. See
[order-dependent alignment](ORDER_DEPENDENT_BRANCHING_ALIGNMENT.md).

## P1-MATH-0067 — Unique primitive extremal rational triple and a sharp gap

Main 14.2 is complete for every integer triple in its literal range.
The exact canonical density reaches 19/30 only at (10,12,15). Every other
primitive ordered triple has density at most 11/18, attained at (8,9,12).
Thus the canonical geometry has the sharp gap 1/45. The improvement does
not assert a gap for additional arithmetic rank losses or prove a
third-cumulant estimate. All pair positions and finite exceptional
numerator/denominator cases are checked. Coverage is 67/167 and confirmed
improvements are 67. See
[complete overlap alignment](RATIONAL_TRIPLE_OVERLAP_ALIGNMENT.md).

T19.9 preparatory checkpoint: the actual late regular population, its
compatible cylinder, absence of leading good pairs, literal 17/12 prime
budget, actual rank-density envelope and integer peeling-order loss are
proved. These source inputs do not supply the final selected component
by assumption. No new independent mathematical finding is counted;
coverage and confirmed improvements stay 67/167 and 67. See
[remaining component scope](QUADRATIC_COMPONENT_ALIGNMENT.md).

T19.9 closure: the actual peeled canonical component is proved connected
and transported to a finite set of original regular starts, with its
exact infinite-model joint and centered moments and square-class nullity.
One family is selected before every asymptotic tolerance. Both lower-bound
coefficients tend to 6 log(2)/17, and the source centered-mass error has
the explicit bound 2/sqrt(L). Full and compatible nullity coincide and
there is no good pair for any threshold. Coverage is 68/167; confirmed
improvements remain 67. No new independent finding is counted. See
[complete component alignment](QUADRATIC_COMPONENT_ALIGNMENT.md).

## P1-MATH-0068 — Near-linear support count with all local kernels retained

The first display of main 3.2 holds with N^(1+epsilon), improving its
printed N^(6/5+epsilon) bound. It also holds without separation, including
contacts and equal centres. A full-loss pair with both coordinates
regular has a nonzero effective intersection and is counted by complete
main 10.3. The remaining pairs have a locally irregular coordinate and
are counted by twice N times the already proved N^epsilon exception
bound. Both internal margins and the fixed factor are absorbed uniformly.

The exact heterogeneous independent pair mass over this larger host set
is at most N^(-1+epsilon). The actual second factorial moment is also
proved at most N^epsilon for every fixed epsilon>0. Neither assertion
proves a bounded second moment or the separate weighted nonaligned
residual in main 3.2. Main 3.2 and T19.4 remain in progress; coverage
stays 68/167 and confirmed improvements are 68. See
[exact host and moment scope](PAIR_HOST_COUNT_ALIGNMENT.md).

## P1-MATH-0069 — Two disjoint square equations and no coefficient-height bound

Full T4.1 is proved with j=2, independent of the fixed degree cap and
error margin, and arbitrary nonzero integer coefficients. One equation
with at least two distinct linear roots fixes the actual squarefree
kernel; the complete fixed-kernel fibre count gives N^epsilon solutions
uniformly for each fixed degree. Multiplying two nonconstant equations
with disjoint root lists supplies that case. Odd degrees and every fixed
polylogarithmic offset width are allowed. The actual integer solution
set on every fixed comparable positive interval is counted.

This arithmetic proof replaces the source many-equation Veronese/Pila
argument at this input. A nonempty fibre supplies the effective kernel
height, so no bound on the input coefficients is needed. The same proof
closes the one-variable assertion of T1.7; its two-variable surface and
graph conclusions remain open. Main 6.2 and 6.3 are still separate
classification and propagation obligations. Coverage is 69/167 and
confirmed improvements are 69. See
[complete square-equation alignment](DISJOINT_SQUARE_EQUATIONS_ALIGNMENT.md).

Main 6.2 preparatory checkpoint: the actual effective nullity increment,
physical relation-code lift, projection restriction budget and fixed-order
recovery regularization are proved. The retained target labels and their
literal finite physical support pools are constructed and bounded. The
prime-group classification and dense-target count remain open. Coverage
and confirmed improvements stay 69/167 and 69; no new independent finding
is counted. See [the precise remaining scope](DENSE_TARGET_ALIGNMENT.md).


Main 6.2 arithmetic checkpoint: actual prime rows, physical supports,
assigned coprime prime groups and the certificate-or-small-groups
dichotomy are proved. The resulting residual kernel bound includes
its full fixed multiplicity/support-pool factor. The small-prime and
source-divisor factors and actual square equations are constructed.
Two-class selection and coefficient enumeration remain open. This
records proof progression without counting a new independent finding
or a completed numbered result. See [alignment](DENSE_TARGET_ALIGNMENT.md).


Main 6.2 is now fully proved. The complete count uses exactly two
selected disjoint nonempty target classes and arbitrary nonzero final
equation coefficients, instantiating P1-MATH-0069. The actual canonical
small-prime/source-divisor/residual decomposition is enumerated in finite
sets; no relation spaces or regularizations are enumerated. The explicit
fixed support bound Dstar includes representations with one source label
(the j=1 term); it can replace the displayed support constant in the
source proof without changing its asymptotic conclusion. The complete
theorem also permits repeated sources and counts source centres among
candidates, with no regularity, separation or compatibility premise.
These scope details are traced in the [complete alignment](DENSE_TARGET_ALIGNMENT.md).
Coverage is 70/167. No additional independent finding is counted beyond
the 69 already registered; main 6.3 and the moment expansion stay open.


Main 6.3 conditional-sum checkpoint: the first assertion is fully proved
for actual infinite-measure conditional affine probabilities, including
homogeneous prescriptions. The proof preserves the exact local rank
and the actual effective nullity increment, so local defects and
incompatible target atoms are accounted for. A stronger bound includes
source centres, repeated sources and centre-dependent target prescriptions.
These scope extensions are recorded without counting a separate
independent finding. Extension-family propagation and the final seed
conclusion remain open. Coverage stays 70/167 and registered findings
stay 69. See [alignment](FIXED_SOURCE_PROPAGATION_ALIGNMENT.md).


Main 6.3 propagation checkpoint: its second assertion now has a full
proof for actual finite extension families and actual original-model
joint masses. Zero-mass seeds, arbitrary seed families, every fixed
intermediate order and the exact distinct-extension condition are
retained. The stronger estimate counts all extensions including repeats,
then bounds every subfamily. These quantifier and scope details are
traced without counting a new independent finding. The final local-
defect/contact seed consequence remains open; coverage stays 70/167
and confirmed findings stay 69. See [alignment](FIXED_SOURCE_PROPAGATION_ALIGNMENT.md).


Main 6.3 is fully proved, including its final exceptional-family
conclusion. At exact contact, an exact span identity replaces a separate
graph-tree calculation: the two effective spaces span the full union
window. Its actual defective positions control the relation rank and
the uniform subpower cost. Actual local and contact seed masses are
placed at all ordered tuple positions by a finite permutation cover
with explicit r! cost. Strict-contact incompatibility is used only for
original run prescriptions. The conditional and propagation assertions
retain their arbitrary affine and homogeneous scope. These proof and
scope details are traced without counting a new independent finding.
Coverage is 71/167 and confirmed findings remain 69. See the
[complete propagation alignment](FIXED_SOURCE_PROPAGATION_ALIGNMENT.md).


P1-MATH-0070: every colored conditional affine atom is pointwise bounded
by its merged homogeneous conditional atom. The exact inverse-image
kernel inclusion proves this for arbitrary finite binary systems under
a common linear merging of relation maps. This simplifies the uniform
colored conditional sum to a direct application of main 6.3. Merged
affine incompatibility is retained, so no comparison with a potentially
zero merged affine atom is claimed. Finite replica identities are also
proved, but the remaining T22.7 assertions keep the numbered result in
progress. Coverage remains 71/167 and confirmed findings are now 70.
See [precise scope](COLORED_REPLICAS_ALIGNMENT.md).


T22.7 formula/propagation checkpoint: the actual infinite conditional
expectation, small-prime sigma algebra, exact heterogeneous marginal
formula, effective relative kernel and its regular p^r specialization
are proved. Colored tuple propagation retains every nonnegative seed
weight exactly and includes all repeated-center extension subfamilies.
No new independent improvement is counted beyond P1-MATH-0070; the
positive random-sum moment assembly remains open. Coverage stays 71/167
and confirmed findings stay 70. See [alignment](COLORED_REPLICAS_ALIGNMENT.md).


Full T22.7 is complete. The exact infinite replica formula, actual
infinite colored conditional target sum and positive weighted random-sum
moments are all proved. An explicit injective flattening keeps every
ordered occurrence and its first-tuple weight, including repeats. The
positive moment bound uses no first-moment lower bound and covers empty
families, zero weights and zero-length tuples. The source p^r formula is
stated on the actual regular set, with the general heterogeneous formula
kept separate. The actual infinite colored atom also satisfies the
pointwise homogeneous domination of P1-MATH-0070. No additional finding
is counted for this proof progression. Coverage is 72/167 and confirmed
findings remain 70. See [complete alignment](COLORED_REPLICAS_ALIGNMENT.md).


P1-MATH-0071: the compatible-triple sign assertion of main 11.3 extends
to every compatible finite binary affine family. Its centered coefficient
is the product of actual heterogeneous marginals times a nonnegative
integer full-support relation count. A single common witness removes
every Fourier sign. The actual original infinite run and physical
square-class identifications are proved. This replaces the ordered
three-pair-rank argument without changing an asymptotic exponent.

The exact incompatible cancellation, canonical connectedness of nonzero
triple coefficients and finite activity comparisons are proved. Only
their independent triple-weight component has the full source decay;
the pair/target deficit and third-cumulant correction assembly remain
open. Main 11.2 and 11.3 stay in progress. Coverage remains 72/167;
confirmed findings are 71. See [alignment](TRIPLE_ACTIVITIES_ALIGNMENT.md).


## P1-MATH-0072 — Exact pair/target incidence removes a factor three

The main 11.2 finite comparison uses one copy of D_(2,1), instead of
the three allowed by the original proof. The exact bijection is
(T,z) -> (T without z,z); each pair/target occurrence has the unique
triple obtained by insertion. Actual nonzero centered activity supplies
a full-support effective relation, proving every target intersection.
Nonzero pair activity forces positive effective pair rank. Thus no sign
or dependence restriction is discarded in the comparison.

This changes only a proof constant. The uniform arithmetic D_(2,1)
estimate remains open. No new numbered result is counted complete.
The exact finite reduction and the remaining obligations are detailed in
[the alignment note](TRIPLE_ACTIVITIES_ALIGNMENT.md).


Third-cumulant assembly checkpoint: the actual original infinite run count
has the complete factorial-cumulant identity, retaining every repeated-
index pair and cubic term. Their uniform critical-band correction is
12 K A2/N+2 K^3/N^2, using proved actual marginal bounds. The source
comparison is now reduced to precisely the actual D_(2,1) and pair
activity A2. Neither of their remaining arithmetic bounds is assumed.
This completes a proof obligation, not a new independent improvement;
confirmed improvements remain 72 and numbered coverage remains 72/167.
See [alignment](TRIPLE_ACTIVITIES_ALIGNMENT.md).


Independent target checkpoint: the actual fixed-source target count and
independent mass are now proved, uniformly for every fixed source
cardinality, including arbitrary overlaps and local defects. This
verifies the source half-count step of main 11.1 and proves the literal
D_(2,1) <= A2 N^(-1/2+epsilon) comparison. The sharper deficit estimate
remains open; no new independent improvement is counted. Coverage stays
72/167 and confirmed improvements stay 72.


## P1-MATH-0073 — Elementary primitive mass suffices at every fixed order r>=5

The complete independent primitive mass and the elementary rho<=L bound
give the stronger total heterogeneous weight N^(1-r/2+epsilon). For every
fixed r>=5 this proves both exponents of main Proposition 15.5 for the
entire population, without a dense-sector restriction. The difficult
source dense-certificate argument can therefore be restricted to r=4.
The same elementary bound controls actual original joint mass and
admissible absolute centered mass.

Every threshold precedes the varying length and dyadic center family,
but depends on the fixed order. No growing-order estimate is inferred.
The r=4 case is now complete under the same three explicit geometric properties, so main15.5 is conditional. CompanionT4.3 was already completed conditionally at every fixed r>=3. The fixed-order moderate budget and source-scope improvements are recorded in the complete four-block checkpoint below.
See [exact statement alignment](PRIMITIVE_GENERAL_MASS_ALIGNMENT.md).


P1-MATH-0073 ordered extension: an exact weighted fiber enumeration
proves the r! factor. The literal nominal p^r 2^rho and actual original
probability sums are bounded independently by N^(1-r/2+epsilon). Both
ordered source T4.3 conclusions now hold for every fixed r>=4, including
all ordered primitive subpopulations without a separation requirement.
The sole remaining T4.3 order is r=3. This extends the existing proof
simplification; no new independent finding is counted. Coverage remains
72/167 and confirmed improvements remain 73.


Two-witness auxiliary checkpoint: the source integer pigeonhole argument
is proved with exact box cardinalities, a nonzero kernel vector and
explicit height (3 n H)^7. The sufficient dimension condition 8t<=7n
also covers the source stricter sixfold gap. The actual rectangular
coefficient slots and triangular equation indices have the stated
cardinalities; all source dimension inequalities and height absorption
are proved. The actual Runge matrix and final norm polynomial remain
open. This is a verified proof component; no new independent finding
or completed numbered result is counted.


## P1-MATH-0074 — Finite coefficient bounds for the two-witness auxiliary

Finite Runge coefficients replace the first Cauchy coefficient estimate
in T9.5. A common denominator 4^(6q), matrix height (B+1)^(28q),
and integer auxiliary-coefficient height (B+1)^(266q) are proved.
The actual formal numerator cancels through total degree 6q, and its
four integer coefficient polynomials have the required degrees with
at least one nonzero member.

This is a proof improvement to the initial coefficient/kernel stage.
Primitive division, the later integer gap and nonzero norm remain open;
T9.5 is not counted complete. No error in the original analytic bound
or the final manuscript conclusion is asserted. See
[the exact alignment](TWO_WITNESS_ALIGNMENT.md).


P1-MATH-0074 coefficient reduction checkpoint: the actual common integer
polynomial factor and primitive quotient family are proved to exist.
Every common quotient divisor is a unit, at least one quotient is
nonzero, the partial degrees decrease exactly and the quotient height
is at most (B+1)^(275q). This uses the complete audited T9.4 bound.
Preservation of the divided numerator vanishing order remains open,
as do the integer gap and nonzero norm. No new independent finding
or completed numbered result is counted.


Reciprocal-order checkpoint: every coefficient of the actual reversed
polynomial is identified and its total formal order is exactly the
pole weight minus the total degree. The multiplicative order law and
coefficient-level quotient vanishing theorem are proved. The actual
source numerator/common-factor product identity is still required for
the final primitive-order conclusion. No new independent improvement
or completed numbered result is counted.


P1-MATH-0074 primitive-order checkpoint: the actual common-factor
reciprocal product identity and the source reduced-numerator vanishing
order are now proved. The constructed primitive integer coefficient
family has height at most (B+1)^(275q); its reduced numerator vanishes
through the remaining pole weight plus the total degree of the removed
factor. The argument includes zero family members and does not divide
by D(x,y). Integer separation, character independence and the nonzero
norm remain open. No new independent finding or completed numbered
result is counted.


## P1-MATH-0075 — An elementary nonzero norm certificate for literal words

The exact reduced-word intersection and symmetric-difference identities
prove the required rational-function nonsquare conditions. Quadratic
anisotropy and a difference of squares prove the literal biquadratic
norm polynomial nonzero for every nonzero coefficient family. This
avoids constructing a degree-four character basis for that conclusion;
evenness and offset bounds are unnecessary for this algebraic stage.
The third integer root and its signed overlap relation are also proved.
A zero actual auxiliary value makes the norm vanish at the point.

The integer-gap estimate, actual branch linkage and final norm degree
and height bounds remain open; T9.5 is not counted complete. No error
in the manuscript conclusion or exponent is asserted. See
[the exact alignment](TWO_WITNESS_ALIGNMENT.md).


P1-MATH-0075 norm degree/height checkpoint: the actual integer word norm
has partial degrees at most 12q and total degree at most 24q. Finite
coefficient arithmetic proves explicit height (B+1)^(1200q) from the
constructed primitive coefficient height (B+1)^(275q). The same actual
w,D,Q,R now retain primitive coefficients, numerator factorization,
original and divided formal cancellations, nonzero norm and all degree
and height bounds. Analytic integer separation and actual word-branch
linkage remain open. No new independent finding or numbered result is
counted; the 75 confirmed improvements are retained.


P1-MATH-0075 convergence checkpoint: the actual primitive numerator
coefficients satisfy (B+1)^(300q)*(2B)^(a+b). Ordinary real absolute
convergence and Cauchy products identify the actual Runge factor values
as positive square-root branches in the required small-parameter domain.
Scaled products have exactly the literal split-product square. The
bivariate vanishing-tail estimate, word enumeration linkage and integer
gap remain open. No new independent finding or numbered result is counted.


P1-MATH-0075 bivariate-tail checkpoint: literal total-degree evaluation
is proved absolutely convergent under the actual geometric coefficient
majorant. Its vanishing prefix gives the explicit value bound
2*C*(M+1)*(R*t)^M. The actual branch, finite sum, scalar and monomial
shift values are identified. Reciprocal polynomial evaluation, word
list linkage, pole scaling and the final integer separation remain open.
No new independent finding or numbered result is counted.


P1-MATH-0075 actual-value checkpoint: finite reciprocal polynomial
evaluation and the scaled full numerator/auxiliary identity are proved.
Every nonzero primitive coefficient has the required remaining-pole
budget under the source rank bounds; zero members are handled directly.
The literal finite word sets supply injective root lists with exact
products and offset bounds. The 1/N scaling, integer root realization
and final integer separation remain open. No new independent finding
or numbered result is counted.


## P1-MATH-0076 — Explicit real-series integer separation for two witnesses

The actual primitive numerator has geometric coefficient exponent 300,
and its divided vanishing order gives an explicit weighted real-series
tail. Exact pole scaling bounds the actual auxiliary by
(B+1)^(400q)/N. The actual word enumerations realize positive integer
roots, including the derived third root, and prove auxiliary integrality.
N>(B+1)^(1200q) therefore forces zero. The same primitive coefficient
family yields a nonzero integer polynomial vanishing at the point with
both partial degrees12q,total24q and height exponent1200q.

This replaces the later bidisc/Cauchy integer-gap step and makes its
constants explicit. It is distinct from the initial matrix estimate
(P1-MATH-0074) and algebraic norm-expression certificate (P1-MATH-0075).
No optimization or error in the manuscript conclusion is asserted.
The explicit degree-four field-norm model is now proved and assembled
with these estimates in `TwoWitnessTheorem.companion_T9_5`, including
real B,q and the full source moreover clause. Coverage is now73/167.
This completes findings75 and76; no new independent finding is counted.
See [the exact alignment](TWO_WITNESS_ALIGNMENT.md).


## Common-curve proof progression after T9.5

The algebraic image-collapse and initial point-factor stages of article
theorem13.2 are proved for actual curve fields and actual polynomial
factorizations. The factor height budget is explicit: c+3*d for input
height exponent c and partial-degree budget d*q. This extends existing
factor-height work and uses the existing Cauchy root theorem; it is not
counted as a new independent correction or improvement. Findings stay76.
The simultaneous resultant stage remains open, so numbered coverage
stays73/167. The exact scope is recorded in
[the common-curve alignment](COMMON_CURVE_ALIGNMENT.md).


## Uniform common-curve resultants: explicit constants

The actual simultaneous polynomial-family construction is now proved.
Its determinant height is n!*((n*d+1)*H)^n. Source budgets give exponent
124608q^2 for the resultant and a convenient safe common threshold
1000000q^2, independently of the family size. The common factor retains
total degree48q and height exponent2472q. This makes constants in the
existing source argument explicit, without changing its conclusion or
claiming optimization. Final basis-norm assembly remains open, so
article13.2 stays in progress, coverage73/167 and findings76.


## Completed common-curve theorem13.2 with explicit constants

The actual bounded even source basis is now assembled with T9.5,
the simultaneous resultant construction and the actual function-field
square-class image. All source conclusions hold with absolute constant
1000000, independent of the basis size, including real parameters.
The stronger natural-parameter curve height exponent2472 and resultant
exponent124608q0^2 remain explicit. This confirms and quantifies the
source argument; no optimized constant or manuscript conclusion error
is asserted. Coverage is74/167 (main26/73, companion48/94); confirmed
findings remain76, and original manuscripts are unchanged.


## Actual exceptional-fibre budget for proposition13.3

The exceptional polynomials and all source regularity facts are now
constructed. Their actual integer root sets cost at most6D^2 across
the two blocks. Every remaining actual fibre retains full degree and
has the expected distinct roots. This quantifies the existing source
argument without asserting an optimized constant, a manuscript error
or a completed integer-grid lower bound. Functional-square matching
and dimension assembly remain open; coverage74/167 and findings76 stay
unchanged. See [alignment](INTEGER_FIBRES_ALIGNMENT.md).


## P1-MATH-0077 — Formal Hensel root matching instead of geometric normalization

A regular fibre root now has an actual branch X=T-u,Y=Y(T) in the
complete power-series ring. The exact substitution kernel and map of
function fields are proved by nonzero resultants and translated-
polynomial injectivity. Without a matching second-block offset, the
literal word series is T times a unit, irreducible and nonsquare even
in its fraction field. A functional square therefore forces the actual
integer-offset match. No geometric normalization or branch is assumed.
The two-block exceptional budget is explicitly at most6D^2.

This supplies an algebraic replacement for the local normalization
paragraph of article13.3. No error in the original conclusion, optimized
constant or completed grid-point lower bound is asserted. Coordinate-
cut dimension and final count assembly remain open. Coverage stays
74/167; confirmed findings now77. See
[exact alignment](INTEGER_FIBRES_ALIGNMENT.md).


## Completed integer-grid proposition13.3, exceptional constant6

The local Hensel replacement recorded in P1-MATH-0077 is now assembled
with actual coordinate kernels, injective physical projections, support
unions and both actual integer-fibre counts. The full proposition holds
with explicit safe constant6, including real parameters and truncation
of negative right sides to zero. No geometric integrality or unproved
normalization input is required. This quantifies and supplies an
alternative proof of the existing conclusion; no optimized constant
or source-conclusion error is claimed. Coverage75/167 (main27/73,
companion48/94); confirmed findings remain77. Originals are unchanged.


## Finite medium-prime deletion and incidence kernel for13.1

The actual source component argument now has explicit finite bounds.
Discarding oversized components costs at most2B/(M+1); discarding
weight>=3 medium-prime columns costs one third of the actual total
column weight, bounded by2B*sum(1/p)+2*#P. No extra component-size
factor enters this deletion count. The actual retained family has
injective physical projections and an injective prime-parity image.
Its actual medium-prime kernel has a constructed labelled incidence
model, with the infinity row equal to the sum of the other rows.
This verifies and quantifies the existing argument, with no new
manuscript correction or optimized constant claimed. The short-cycle
and final short-basis/asymptotic steps remain open; article13.1 is in
progress. Coverage75/167 and confirmed findings77 stay unchanged.


## Constructed sparse kernel basis and final finite cut for13.1

The source fundamental-kernel-basis step is now proved through an
actual supported right inverse and actual projected single columns.
A system of s equations has an actual kernel basis of support<=s+1,
even for arbitrary coordinate index sets. Actual physical support
transports to ell*(s+1). The final pi(z) prime equations and two
separate block parities produce actual complete even relations,
with dimension loss<=pi(z)+2 and support<=ell*(pi(z)+3), preserving
both physical and square-class-image injectivity. This verifies the
source linear-algebra argument and exposes its finite constants;
no new manuscript error or optimized bound is claimed. The required
input short-cycle basis and prime-harmonic estimate remain open,
so coverage75/167 and findings77 are unchanged.


## Sharp actual harmonic error and retained-component coefficient for13.1

The source prime harmonic window now has an actual internal proof,
with an explicit positive constant H and error<=(2H/a+log10)/log B.
Exact factorial floors, actual prime-power summability and actual Abel
integrals discharge all inputs. The actual retained component family
therefore has count>=d_xy-(2/3)B log(1/a)-K_a B/log B uniformly over
every critical pair. K_a precedes C, propagating P1-MATH-0006; only
the threshold depends on C. This verifies the source coefficient and
error order, without claiming optimization or a new source-conclusion
error. Short cycles and full asymptotic short-basis assembly remain
open. Coverage75/167 and confirmed findings77 are unchanged.


## Constructed witness-edge independence and finite complete-relation reduction

The source deletion argument is now proved with actual witness coordinates and actual basis extraction. Its final relation-space assembly has the explicit constants #retained-r-(pi(z)+2) and M*k*(pi(z)+3), under the clearly exposed local short-vector hypothesis. Loops and parallel columns are fully discharged. This verifies the source finite construction without a new correction or an optimized bound. The simple-graph logarithmic length estimate and full asymptotic assembly remain open; coverage75/167 and confirmed findings77 are unchanged.


## Direct finite incidence growth closes the short-vector existence input

The source Moore/BFS step now has a direct proof using actual bounded edge-vector routes and their actual span rank. It preserves all labelled edges and proves explicit constants e>2d*n, n<d^r and support<=2r+1. Combined with actual witness deletion and final prime/parity constraints, the finite complete-relation construction loses at most2d*n+pi(z)+2 dimensions and has basis physical support<=M*(2r+1)*(pi(z)+3). This verifies the finite source argument without an external short-cycle hypothesis. Numerical logarithmic choices and full source asymptotic assembly remain open. No new correction or optimized constant is claimed; coverage75/167 and confirmed findings77 are unchanged.


## Completed13.1: constant uniformity and endpoint a=1

Full article13.1 is proved. P1-MATH-0006 now propagates through the full theorem: KD(a),KS(a) are chosen before C, with only the threshold N0(a,C) depending on C. The support constant can be taken352/a, without an optimization claim. P1-MATH-0078 records the additional endpoint a=1; the source interval(0,1) remains included. Its support bound is coarse at the endpoint, and the universal physical cap2B is proved separately. No a=0 or varying-a extension is claimed. Actual complete-relation subspaces, their actual bases, physical/common-class injectivity and nonzero even selections are all explicit. Coverage76/167(main28/73,companion48/94), confirmed findings78.


## P1-MATH-0079: upper degree caps and the subpolynomial endpoint

The unconditionally proved analytic estimate D^2 H^(1/D)<=4sqrt(H)+e*(M^2+(log H)^2) removes the need for a lower growth condition on the cap M. Its logarithmic square is absorbed into sqrt B. Under the source degree-uniform BCN input, the full corollary13.5 reduction therefore needs only an upper power cap and permitsa=0. Bounded and polylogarithmic caps are included. BCN remains an explicit ordinary hypothesis with its Lean proof and geometric specialization open; no extra proved coverage is claimed. Coverage76/167, confirmed findings79.


## Exact actual-code to word/curve compatibility

The literal offset i-1, total physical support identity, actual image basis, integer-square evaluations and application of the proved common-curve and grid theorems are now verified from actual complete relations. This confirms the source compatibility of the constructions, including overlapping numerical windows and the zero-product edge case, without a new manuscript correction. Critical asymptotic thresholds, degree-one alignment and the final nonaligned contradiction remain open for13.6. Proved coverage76/167 and confirmed findings79 are unchanged.


## P1-MATH-0080: a direct bounded-grid proof of the linear branch

Two actual bounded integer points on the actual line, together with a center beyond the box, force the required positive reduced alignment. The already proved13.3 grid lower bound supplies them at actual relation rank>=9 when D=1. This replaces the coefficient-height sign argument and the additional functional-square/root-pairing choice in that branch. All coefficient, sign, gcd, height and affine-error steps are formalized; no original conclusion error or optimized threshold is claimed. The full13.6 threshold assembly, BCN input and final contradiction remain open. Proved coverage76/167, confirmed findings80.


## Completed conditional nonaligned-rank assembly

The exact source nonaligned-rank threshold, actual finite-pair maximum, literal limsup and a uniform strict half-window gap now follow from one named ordinary integer-polynomial BCN argument. The short basis, support floor, actual common curve and square-word bridge, critical point threshold, degree-one alignment, degree loss and final contradiction are all proved internally. The numerical threshold<1/2 is unconditional. This closes the assembly promised after P1-MATH-0080 without a new mathematical finding. BCN and its presentation specialization remain unformalized;13.6 is conditional, not proved coverage. Coverage76/167; findings80.


## One common external BCN input for13.5 and13.6

The exact integer/rational coefficient map now preserves total degree, the actual integer grid and irreducibility of every positive-degree irreducible integer nested polynomial. Two actual polynomial localizations and the nonunit degree obstruction prove the irreducibility step. The integer BCN input is therefore derived from the same field-polynomial input used by13.5, with no second independent external assumption. This closes a formal presentation gap without a new manuscript correction. BCN and its geometric presentation remain open. Coverage76/167, findings80.


## P1-MATH-0081: a pair controls every larger joint event

The exact actual pair formula and the proved critical cap p_x<=2*2^(-L) give q(I)<=4*2^(-2L+d_xy) whenever I contains that distinct pair. This finite bridge needs no BCN. Under the same BCN-dependent pair-rank bound as the source, q(I)<=N^(-3/2+epsilon) uniformly for every cardinality>=2, including incompatible families. The triple maximum is constructed literally. No third-window rank estimate is needed for this probability branch, and no improved asymptotic exponent is claimed.


## P1-MATH-0082: nonaligned triple rank without compatibility

The exact finite bound rho(T)<=L+d_xy and the compatibility-free nonaligned pair theorem give the stronger1+(2/3)log2 triple-nullity coefficient for every triple containing a nonaligned pair, under the same explicit BCN input. Compatibility remains in the universal3L/2 rank statement because of the aligned branch. Article13.8 is conditional; proved coverage76/167, confirmed findings82.


## P1-MATH-0083: the finite heterogeneous retained reference

The exact retained-reference identity and l1 bound now hold for arbitrary heterogeneous positive actual marginals on a finite admissible ground set. Pair compression is justified by actual relation-kernel support and centered Fourier reconstruction; the finite pair/extension enumeration is disjoint. The original regular equal-marginal setting gives the literal binomial correction for everyN>=2,L>0. The sourceF_r,G_r count grouping remains open, soT17.2 is in progress. Coverage76/167, findings83.


## The homogeneous cardinality form ofT17.2 is complete

The exact sourceF_r,G_r, direct/gamma meanings, binomial complement counts and natural-to-real subtractions are proved. Finite cardinality grouping, r=0,1 and r>n zero conventions, nonnegative coefficients and weighted infinite-tsum identities are checked. The retained equality and l1 bound hold as actual atomic signed measures. This completes the original specialization of P1-MATH-0083 without a new finding. Coverage77/167 (main28/73, companion49/94), confirmed findings83.


## Conditional completion ofT19.4 without a separate seed assumption

The actual host count and the same explicit BCN-dependent pair cap prove F_2<=(2^C)^2+1. Its absorption yields the full growing-order source bound uniformly for2<=k<=logN. K_C precedes the external BCN constants; only the threshold depends on them. The smaller exception of P1-MATH-0030 remains unconditional. No new finding or external input; coverage77/167, confirmed findings83. T19.4 is conditional and is not counted proved.


## P1-MATH-0084: logarithm-free finite Poisson–Charlier conversion

The analytic conversion holds for every n>=2 and0<=p<=1 with explicit constants in a mean bound, through actual summable signed measures. The2p<1 restriction is removed from the analytic argument. The actual critical regular-set reference has error4|beta-c2|+K_C*(N^(-2)+|c2|/N). The source arithmetic C_2=O(a_N) remains open; T17.4 is in progress. Coverage77/167, confirmed findings84.


## P1-MATH-0084 extended to heterogeneous actual marginals

The finite conversion of main15.1 holds with C_M=16exp(2M) for the full probability range0<=p_i<=1, removing p_*<=1/4. Actual signed covariances, the actual count mean and the exact second factorial cumulant are retained. A uniform actual reference bound K_C*(N^(-2)+A_2/N) holds before every deterministic dyadic subset. The source numerical rate remains open for A_2. This extends finding84 without a new finding; coverage77/167.


## P1-MATH-0085: signed irregular-window counts determine the mean bias

The actual finite integer identity is proved without a critical-band premise. In the uniform critical range, zero-marginal and double-marginal windows partition the irregular set, giving M=2*#double-#irregular and identical parity. Odd irregular cardinality forces a nonzero mean bias at that scale; no infinitely-many-scales assertion follows. The actual quadratic references also satisfy an explicit mean-separation lower bound. True-law distance estimates remain open. Coverage77/167, confirmed findings85.


## Actual Hermite reference and its uniform finite comparison

The actual law U+2V is constructed from independent Poisson variables of means mu-alpha andalpha/2. Its factorization and ordinary l1 comparison with Q(mu,alpha) are proved with error4alpha^2 exp(2alpha), plus a finite TV transfer for arbitrary probability laws. Its actual mean and every real exponential moment are proved as integrable Bochner quantities. General natural jump sizes are included in the probability construction. Arithmetic parameter admissibility and source count-law rates remain open; main19.1 is in progress. No new finding; coverage77/167, confirmed findings85.


## P1-MATH-0086: a universal conversion constant with no mean cap

The heterogeneous analytic conversion now has the universal constant16exp(2), valid for every finite Bernoulli family in[0,1], without mu<=M. Norm-one probability factors replace the total-mean exponential bound in the product perturbation. The actual run reference and homogeneous binomial pair reference are included. Arithmetic pair-activity and covariance scales remain open; coverage77/167, confirmed findings86.


## Finite arithmetic foundations ofT19.15

Canonical square-part injection, the literal positive reciprocal sums, a uniform2X/A square tail and a finite logarithmic-preimage dyadic transfer are now proved. These validate the elementary reduction in the manuscript without changing its claim. The cited ordinary reciprocal-prime asymptotic and uniform saddle comparison remain open. No new mathematical finding or proved numbered result; coverage77/167, findings86.


## Coarse actual pair activity and the upper Hermite parameter gap

The exact finite bound2A2<=#hosts*M+actual independent host mass is proved, with the actual factor2 and zero-loss covariance support. Under the existing explicit BCN input this yields A2<=N^(-1/2+epsilon), conversion errorN^(-3/2+epsilon) and uniform decay of the actual second factorial cumulant. Actual two-sided mean bounds are unconditional. The upper gap |alpha|<=mu/2 follows under BCN; alpha>=0 and the source sharp rates remain open. This is a verified intermediate step, without a new mathematical finding or numbered completion. Coverage77/167, findings86.


## P1-MATH-0087: positivity from one channel before the complete pair profile

The actual second factorial cumulant satisfies alpha>=d_C*L*N^(-2/3)>0 without BCN, from the selected-joint host identity and the private2:3 channel alone. Actual Hermite and quadratic probability status then follow using the already checked coarse upper bound under the existing explicit BCN input. The sharp pair profile, count-law errors and explicit fixed-height parameters remain open. The actual mean-bias clause of main1.1 has the explicit unconditional constant2^C. Main1.1 is in progress; coverage77/167, confirmed findings87.


## P1-MATH-0087 extended: explicit parameters without the pair profile

For every fixedh>=3, the literal source finite coefficient is positive and tends uniformly to zero, by finite signed-channel bounds and the2:3 summand. Its quadratic and Hermite references are actual probabilities unconditionally, without alphaHat_h~alpha or BCN. The exact height4 coefficient, singleton masses, phase constants at heights3..6 and height5 polynomial are checked. The source distance and cumulant remainder rates remain open. Main1.4,18.1,18.3 move to in_progress; no new numbered completion or finding. Coverage77/167, findings87.


## Uniform finite-height moving phase is checked

The literal finite omitted-height contribution has the exact source uniform leading equivalent, with the residue and nominal mean moving over the critical band. Normalized integer identities, reciprocal/geometric limits, finite residue assembly and the exact real-power transport are proved. This validates the finite analytic step without assuming or proving the actual pair-profile, cumulant or law remainder. Main3.3,18.1,18.3 remain in progress; coverage77/167, findings87.


## Explicit Hermite reference changes are negligible at every fixed omitted height

The literal explicit Hermite and quadratic signed references have ordinary l1 distance at mostN^(-4/3+epsilon), unconditionally. Their actual probabilities have distance-to-P changes at most half that bound, uniformly for every probability lawP. A proved positive omitted-height phase lower bound makes this change negligible on the actual moving scalar phase. No original-count approximation or distance equivalent is assumed or established; main19.1 remains in progress. Coverage77/167, findings87 unchanged.


## Coarse actual triple estimates and finding82 probability consequence

The actual A3 and third factorial cumulant have a proved vanishing power under the same explicit BCN input. The all-aligned target count is unconditional. The literal D_(2,1) and incompatible/comparison costs have coarse exponent1; repeated-index cost has exponent3/2. The source sharp rates and optimality remain open. Finding82 is extended with the retained stronger nonaligned actual probability cap; no new finding or numbered completion is added. Coverage77/167, confirmed findings87.


## Finding85 reference quantum and universal parameter stability

Actual Poisson and quadratic signed references have universal parameter Lipschitz bounds. The exact-to-nominal mean replacement has unconditional costN^(-1+epsilon), and explicit lower boundc_C/N at every nonzero integer-bias scale with fixedalpha>=-1. For every fixed omitted height, the mean-change cost is negligible on its actual moving phase. Literal explicit coefficients also give probabilities at the actual mean without BCN. True-count law estimates and infinitely-many-nonzero-scale assertions remain open. Finding85 is extended; no new finding or numbered completion. Coverage77/167, findings87.


## Actual conditional mean and uniform negative Palm deviation

For every fixed maximum number of sources, actual negative conditional deviation is at mostN^(-1/2+epsilon) and source deletion costsN^(-1+epsilon), without BCN. Actual conditional Bochner means, the exact positive/negative decomposition and arbitrary nonnegative source averaging are checked. The source-specific positive excess remains open; T2.7 is in progress. No new finding or numbered completion. Coverage77/167, confirmed findings87.


## Actual adjacent-reference distance constants are checked

The ordinary quadratic same-mean distance is exactly|alpha-beta|*norm(Pi_mu*Delta^2)/2, and its actual TV is half that. Literal adjacent fixed-height quadratic references have the full uniform moving-phase equivalent, with actual probability witnesses. Adjacent Hermite references have the same leading TV. Original-count distance equivalents and optimality remain open. No new finding or numbered completion. Coverage77/167, findings87.


## The actual direct maximum has the complete all-order envelope bounds

The largest active direct subfamily is constructed under the original infinite law. All observables are integrable and transported exactly to a concrete finite cylinder. Actual regular-window joint equalities supply unconditional binomial/Poisson factorial bounds, actual tail probabilities and exponential bounds at every order. The shifted maximumR+1 has all corresponding source envelope inequalities, including the repeated-index term. The specified modified-count and exceptional-event/coupling estimate remain open; T19.3 is in progress. No new finding or numbered completion. Coverage77/167, findings87.


## P1-MATH-0088: regularity is unnecessary for the direct-maximum envelope

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


## Finding88 extended: actual retained-modified law and its literal error

An actual retained-configuration modified count is constructed and proved dominated by the shifted direct maximum. Its actual law, every-order heterogeneous moment/tail bound and TV coupling by the exact bad-event probabilitydelta are checked. The retained outside-event subfamily nullity is at mostL/3+1. The source arithmetic rate fordelta and seed-union event identification remain open; T15.2,T19.3 are in progress. No new finding or numbered completion. Coverage77/167, findings88.


## Qualitative control of the actual retained-modification error

The actual bad-event probability and original-to-modified total variation now tend uniformly to zero under explicit BCN. The finite seed/mean decomposition is unconditional; its finite order cutoff is chosen before N. This is a weaker intermediate estimate, with no new mathematical finding or numbered completion. The source quantitative rate and seed-union identification remain open. Coverage 77/167, confirmed improvements 88.


## Bounded original-count moments from actual primitive seed propagation

Canonical tuple enumeration and the proved propagation theorem yield an actual unordered seed-mass bound. Under explicit BCN, every fixed-order dependent joint mass is at most N^(-1/2+eta), giving an actual factorial upper bound by mu^r plus that scale and bounded original moments of every fixed order. This discharges the higher-moment premise in regular-count transfer under BCN. Main 6.4 is now in progress; its sharp two-sided expansion remains open. No numbered completion or new mathematical finding is counted. Coverage 77/167; confirmed improvements 88.


## First two-sided actual factorial-moment convergence estimate

An exact fresh-tuple recurrence and the unconditional negative conditional-deviation estimate prove an unconditional factorial-moment lower bound. Under explicit BCN this combines with actual dependent-family upper bounds to give |E(Z_N)_r-mu_N^r|<=N^(-1/2+eta) at every fixed order. The nominal-mean version is proved too. Main 6.4 remains in progress for its sharper quadratic correction and remainder. No numbered completion or new finding. Coverage 77/167, confirmed improvements 88.


## First actual original-law Poisson approximation under BCN

The original count law now converges uniformly in TV to actual Poisson probability laws with the current actual mean or nominal mean, under explicit BCN. The unconditional finite factorial reconstruction bound and factorial Banach remainder supply the passage from fixed moments to laws. The reconstruction order is chosen after the final tolerance and before N. No optimal rate, quadratic correction, new numbered completion or new mathematical finding is claimed. Coverage 77/167, confirmed improvements 88.


## Stronger coarse triple-activity and cumulant bounds

Actual fixed factorial-moment estimates improve both full absolute triple activity and the third factorial cumulant to N^(-1/2+eta) under explicit BCN for every dyadic subground, including zero marginals. Exact zero-marginal moment restriction and all repeated/incompatible terms are checked. Main 11.3, 14.1 and 14.6 remain in progress for their sharp claims; no numbered completion or new finding. Coverage 77/167; confirmed improvements 88.


## Actual retained-modified moment convergence

The actual original-to-modified moment truncation inequality is proved on a common finite cylinder. Combining the real bad-event probability with the proved higher original moments gives convergence of every fixed ordinary moment under explicit BCN, uniformly over all dyadic subgrounds and every H. Actual modified-law Poisson convergence is also checked. The source numerical error rate remains open. No new numbered completion or finding: coverage 77/167, improvements 88.


## P1-MATH-0089 — Fourth factorial-cumulant identity in a commutative ring

The entire finite identity displayed in the proof of main 16.1 is proved over any commutative ring for normalized coherent centered data, and instantiated to the actual heterogeneous original count. No positivity, regularity, independence, arithmetic hypothesis or analytic logarithm is required for that identity. Every repeated-index term and zero-marginal restriction are checked. The source sharp connected-quartic estimates remain open; a weaker BCN-dependent half-power bound is proved separately. Main 16.1 is in progress. Coverage 77/167; confirmed improvements 89.


## Coarse absolute centered activity at every fixed positive order

A finite actual centering decomposition bounds absolute activity by dependent product mass and lower-order actual dependent joint masses. Product mass is unconditionally at most N^(-1+eta); under explicit BCN the full absolute activity, hence the connected activity, is at most N^(-1/2+eta) for every fixed positive order and every dyadic subground. Companion T14.1 is now in progress for its sharper 4/5 exponent and contact claim. No new numbered completion or finding: coverage 77/167, improvements 89.


## Actual quartic factorization and repeated-index precision

Every nonconnected nonzero actual quartic coefficient factors over two canonical pair components, with exact nullity additivity. All repeated-index corrections satisfy the finite bound 72*P*A3+72*P^2*A2+6*P^3*mu, which is uniformly N^(-3/2+eta) under explicit BCN. The direct-pair-product and incompatible quartic comparisons remain open; main 16.1 is still in progress. No new numbered completion or finding. Coverage 77/167, confirmed improvements 89.


## Actual per-site covariance rows and overlap costs

Fixed-source propagation is specialized exactly to actual original joint rows, including tuple repetitions. The unconditional absolute row bound retains p_x, including p_x=0. Finite repeated-edge and star-square bounds then give N^(-3/2+epsilon) under explicit BCN, supplying the source precision for overlapping edge products in main 16.1. The disjoint non-direct case remains open. No new numbered completion or finding: coverage 77/167, improvements 89.


## Exact isolation of the disjoint non-direct quartic product cost

Actual unordered pair products are partitioned exactly into direct disjoint, non-direct disjoint and shared-vertex populations, with the repeated-edge term retained separately. The shared population is bounded by half the sum of squared rows. This leaves a literal non-direct positive sum, not an assumed target estimate. Main 16.1 stays in progress; coverage 77/167, improvements 89.


## Canonical identification of the quartic direct-pair sum

Nullity additivity is proved equivalent to disjointness of actual block spaces, with an exact cross-block dimension term. Actual centered coefficients factor across arbitrary nonempty direct blocks, including zero marginals. Canonical uniqueness gives the exact sum over all nonconnected quartic families. The full fourth-cumulant comparison is reduced to 24 times the literal disjoint non-direct product cost, plus a checked source-scale remainder under explicit BCN. No new numbered completion or finding: coverage 77/167, improvements 89.


## Unrestricted original component laws and a weaker complete quartic rate

Actual component products are now proved on every finite original family with L>0, without a caller-supplied positivity premise. This matches the unrestricted finite-family scope of main 4.4; it is not counted as a new manuscript correction. The literal disjoint non-direct cost is at most A2^2/2, giving the actual connected fourth-cumulant comparison at N^(-1+epsilon) under explicit BCN. Source 3/2 precision remains open. Coverage 77/167, improvements 89.


## P1-MATH-0090 — Unconditional quantitative absolute-pair/cumulant equivalence

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


## Exact all-order canonical factors and quadratic nonconnected activity

Original canonical component images are injective, connected and cover the actual family; every nonzero factor has at least two sites. An unconditional finite polymer tail bound controls nonconnected activity by W^2*exp(W)/2. Under existing explicit BCN, this yields N^(-1+epsilon) at every fixed order, without a growing-order assertion. Source connected 4/5 and contact estimates remain open. Coverage 77/167, improvements 90.


## Actual fixed moments are subpolynomial without BCN

Positive singleton-seed propagation gives actual joint subset mass, factorial and ordinary moments at most N^epsilon at every fixed order, including zero, without BCN. This does not claim uniformly bounded moments or the source full fixed-moment asymptotics. Coverage 77/167, improvements 90.


## P1-MATH-0091 — Subpower moments and unrestricted original contact activity

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


## Proof progress: finite good-channel activity

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


## Complete aligned principal profile

The entire original enlarged aligned unordered pair family is now
constructed using CompressedTargetAlignment.Aligned 1, with logarithmic
height at most (L+1)^3. Uniform dyadic geometry orients every representing
reduced channel as a <= b <= 2a. Its positive activity is covered by the
height-one and height-two boundary classes, private good 2:3 and 3:4
pairs, their normalized defects, zero-unit alignments, and the full
height-at-least-five tail. No disjointness of that cover is presumed.
Private one-unit pairs have zero actual centered coefficient, including
their affine prescription. All original irregular sites and zero exact
marginals are included.

Let beta be the actual joint mass of the compatible private principal
2:3 and 3:4 edges. For every fixed C, epsilon>0 and natural D, eventually
uniformly in the critical window and 8(L+1) <= H <= D(L+1), both the
absolute activity and the signed centered sum of ALL aligned pairs
differ from beta by at most N^(-4/5+epsilon). This is unconditional: no
BCN assumption is used. Separately, every pair subfamily F of the dyadic
block satisfies 0 <= A_F - C_F <= N^(-1+epsilon), uniformly over F.

An exact original-model identity splits alpha-2 beta into twice the
signed nonaligned sum, twice the aligned error, and the negative
single-site square diagonal. Consequently

    |alpha - 2 beta| <= 2 A_dense + N^(-4/5+epsilon).

Here dense is a literal finite residual family, not a presumed bound:
it consists only of regular, compatible nonaligned unordered pairs with
actual relative nullity greater than L/10. The weak, incompatible,
irregular and zero-coefficient classes have been removed using checked
estimates and an exact finite cover. The nonaligned complement retains
the full dyadic population before those removals.

The same bound holds with 2 beta replaced by the explicit sum
ChannelMainTermBounds.mainTerm N L 2 3 + mainTerm N L 3 4, using both
checked fixed-channel mass errors. These main terms retain the exact
signed finite channel sums, their source translation coefficients and
the nominal single-site scale; no phase limit is assumed.

This completes the aligned part of the actual second-cumulant profile.
It DOES NOT bound A_dense, prove the hard dense nonaligned weighted
estimate T1.8, or complete the unweighted positive/signed profile,
main 3.3 or T7.1. Both numbered results stay in progress and T1.8 stays
not started. Coverage stays 77/167 (main 28/73, companion 49/94), with
94 confirmed improvements. No new correction, external premise, axiom,
dependency download, original manuscript edit or Palomar registration
is introduced.

Verified under Lean v4.36.0-rc2: full lake build (11023 jobs), source and ledger checks, actual axiom audit of 7015 declarations (only propext, Classical.choice and Quot.sound), and 4732 direct ledger/evidence declaration checks; Ubuntu root free space 15.04 GiB. Original manuscript bytes and all 167 statement hashes preserved.


## Retaining the strict nonaligned rank gap

The literal original nonaligned family now has a finite positive host
bound. Every nonzero covariance is represented by an ordered increasing
nonaligned full-loss host. A joint cap M gives

    A_nonaligned <= #hosts * M + independent_host_mass.

The representation includes locally irregular sites, zero marginals and
affine incompatibility. It does not assume pairwise independence or a
positive covariance sign. Zero-loss pairs are removed only after their
actual centered coefficient has been proved zero.

With exactly the existing explicit BCN premise
PlaneCurvePointCount.UniformBound c kappa, c>0, put
s=(2/3) log 2. The already checked nonaligned joint cap N^(-2+s+delta)
and unconditional host count N^(1+delta) give

    A_nonaligned <= N^(-1+s+epsilon).

Independently, the complete aligned family satisfies the unconditional
bound A_aligned <= N^(-2/3+epsilon). Its cutoff can be chosen internally
as H=8(L+1), so this statement has no free private-prime cutoff.

The exact aligned/nonaligned partition therefore gives, under the same
explicit BCN premise and uniformly over every deterministic subset G
of the original dyadic block,

    A_2(G) <= N^(-1+s+epsilon),
    |alpha(G)| <= N^(-1+s+epsilon),
    ||B_2(G)-Q(actual mean, actual alpha)||_1 <= N^(-2+s+epsilon).

The exact single-site square diagonal is retained in alpha. Since
1/3 <= s < 1/2, these improve the previous coarse -1/2 activity/cumulant
and -3/2 conversion exponents by the strict gap 1/2-s. The first two
exponents are approximately -0.5379, and the conversion exponent is
approximately -1.5379. This is the analytic conversion of the finite
second-order reference, not an error bound for the complete count law.

All parameters c, kappa, C and epsilon are fixed before the common
threshold; lengths and deterministic subsets vary afterwards. BCN is an
ordinary theorem argument, not a new kernel axiom or an internally proved
external result. No stronger unformalized input is introduced.

These are intermediate rates, weaker than the source's sharp -2/3 pair
rate and -5/3 conversion rate. They do not establish the weighted dense
nonaligned estimate or finish main 3.3, 3.4, 15.1 or T7.1. All four
remain in progress; T1.8 stays not started. Coverage stays 77/167
(main 28/73, companion 49/94), and confirmed improvements stay 94.
No original manuscript edit, dependency download or Palomar registration
is introduced.

Verified under Lean v4.36.0-rc2: full lake build (11031 jobs), source and ledger checks, actual axiom audit of 7025 declarations (only propext, Classical.choice and Quot.sound), and 4742 direct ledger/evidence declaration checks; Ubuntu root free space 15.03 GiB. Original manuscript bytes and all 167 statement hashes preserved.


## Homogeneous seed probabilities and their principal mass

The homogeneous zero-target window event is now defined under the
actual infinite prime-sign measure. For positive L, its relative bit
prescription is proved equivalent to equality of the value signs at
x-1, x, ..., x+L-1. For any finite family I, its joint probability is
exactly 2^(-rank of the sum of its actual square-class spaces), and is
strictly positive. Tuple support transport includes repetitions and the
empty family. The probability is antitone under adding windows.

For every I contained in the regular dyadic set, this actual homogeneous
probability equals the source weight

    W(I) = p^|I| 2^(rho(I)), p=2^(-L).

The exact rank-nullity identity proves this equality. It is not asserted
with nominal marginals on irregular sites. The actual original run joint
probability is at most the homogeneous probability for every finite I
and every positive L, including irregular and incompatible families.

In a raw private good channel a:b, every pair has homogeneous mass
p^2 2^(u-1), where u is its exact-unit count. This has no affine
compatibility restriction. For each fixed coprime 0<a<b, its total
unordered homogeneous mass is at most K_(C,a,b) L N^(-1+1/b), uniformly
over the private-prime cutoff H and all sufficiently large critical N,L.
The raw principal family is the union of the 2:3 and 3:4 raw good pairs.
Its W mass is bounded above by K_C L N^(-2/3) for every H and below by
c_(C,D) L N^(-2/3) when 8(L+1)<=H<=D(L+1). The lower bound follows from
the actual compatible principal beta mass, which is at most this raw
homogeneous mass. No cancellation or compatibility filter is used in
the upper bound. This proves the principal raw seed scale stated in
the moreover clause of the first part of T1.12.

For fixed positive seed size s and fixed extension size k, the sum of
actual homogeneous probabilities over any unordered family of size
s+k containing a seed is bounded by (s+k)! N^epsilon times the sum of
the seed probabilities. All seed and target populations vary after
the same threshold. On regular populations this transports exactly
to W mass. Consequently, for every fixed r, the sum of W over all
r-subsets of any regular dyadic subfamily is at most N^epsilon.
These statements are unconditional and concern fixed orders only.

The sharp outside-principal residual, dependent-target gains and
two-good-edge bounds of T1.12 remain open. T1.12 is now in progress,
not proved. Main 6.3 stays proved and its homogeneous specialization
is recorded here. Coverage stays 77/167 (main 28/73, companion 49/94)
and confirmed improvements stay 94. No external premise, new axiom,
dependency download, manuscript-byte edit or Palomar registration
is introduced.

Verified under Lean v4.36.0-rc2: full lake build (11037 jobs), source and ledger checks, actual axiom audit of 7046 declarations (only propext, Classical.choice and Quot.sound), and 4763 direct ledger/evidence declaration checks; Ubuntu root free space 15.01 GiB. Original manuscript bytes and all 167 statement hashes preserved.


## T20.4 and P1-MATH-0095: integer plane fibres

Companion T20.4 is proved for the literal population of distinct
offset triples supplied by shared odd-valuation primes above Y>=L+1.
The finite population is proved equivalent to the original prime/offset
description. A finite minimum vertex cover is defined and shown equivalent
to hitting every actual shared-prime hyperedge on the plane. Repeated
prime supports are included and counted once, as in the manuscript.

Let B=L+1 and let A be a primitive integer normal. Its Lean height is
max_i |A_i|, exactly the source infinity norm. For N>=10, B<=N+1,
dyadic centers, an injective first even-selection map and direct first
two square-class spaces, the checked finite bound is

    m_(A,Y) <= M_Y + 4 B^2 / ||A||_infinity,
    M_Y = 1 + log(6NB)/log Y.

This strengthens the source constant 6. No effective-rank condition on
the third window is needed for this finite estimate.

The proof uses a primitive integer direction obtained by dividing a
nonzero difference of two actual offsets by its content. Its height d
is at most B. Bezout coordinates for the primitive normal give integer
parallel-line levels. There are at most 1+2Bd/||A||_infinity levels,
and each line has at most 1+B/d integer points in the cube. Treating one
fibre with the checked M_Y line bound and the remaining fibres with
the cube bound gives M_Y+4B^2/||A||_infinity. No shortest vector,
Euclidean lattice basis, covolume theorem or unformalized geometric
count is assumed.

For fixed delta>0, uniformly after one critical-window threshold and
for all Y>=B, a minimum hyperedge vertex cover of size at least delta L
forces

    ||A||_infinity <= 16 B/delta,
    |h| <= 48 B^2/delta,

strengthening the source constants 24 and 72. The existing uniform
M_Y=o(B) estimate proves the needed small majorant; the existence of
an actual support bounds h. For each delta, a fixed integer K is chosen
before C and N. Every such (A,h) belongs to a finite box of at most
(2K+1)^4 B^5 integer planes. The complete aligned source statement is
PaperP1.OffsetPlaneNormalBudget.companion_T20_4; its full-rank and
pairwise directness assumptions specialize the stronger finite APIs.

No BCN premise or new external input is used. T20.4 moves from not
started to proved. Coverage becomes 78/167 (main 28/73, companion 50/94).
The improved constants and integer-fibre proof are recorded as confirmed
improvement P1-MATH-0095 for the next manuscript version. The weighted
dense nonaligned sector and the complete pair profile remain open.
No dependency download, original manuscript edit or Palomar registration
is introduced.

Verified under Lean v4.36.0-rc2: full lake build (11055 jobs), source and ledger checks, actual axiom audit of 7086 declarations (only propext, Classical.choice and Quot.sound), and 4803 direct ledger/evidence declaration checks; Ubuntu root free space 14.99 GiB. Original manuscript bytes and all 167 statement hashes preserved.


## P1-MATH-0096: counts for moving split roots

The one-variable split-product count now permits arbitrary moving
integer offsets. For fixed natural K,d and epsilon>0, one threshold
precedes every offset set A, nonzero integer coefficient c and finite
solution population S. If 2<=|A|<=d, every actual value n+a is positive
and at most N^K, and

    c * product_(a in A)(n+a) is an integer square,

then |S|<=N^epsilon. The variable n is natural but has no required
comparison with N. The offsets can be arbitrarily far from zero;
only the actual positive values are bounded. The coefficient c has
no height restriction. Two equations with disjoint nonempty offset
sets satisfy the same count. Fixed product-kernel fibres also have
the same bound, uniformly in their squarefree kernel.

The argument is internal. Two fixed individual squarefree kernels give
an injective positive Pell representation, with coefficients, square
parts and offset difference bounded by N^K. The full product kernel
and pairwise offset resultant have height at most N^(K(d+d^2)), using
one actual solution and the positive value cap. Individual prime
supports lie in that fixed kernel-resultant support. The number of
support codes is at most 4^omega(m)<=tau(m)^2=N^o(1), and every code
fibre is bounded by the checked uniform positive quadratic theorem.
Both square and nonsquare coefficient ratios are included.

This strengthens the previously checked one-variable portions of T1.7
and T4.1 beyond logarithmic offset windows, without Pila or another
external curve-counting premise. It provides an input for moving line
substitutions in later planar arguments; those substitutions and the
full planar population count T20.6 are NOT yet proved here. T20.6
stays not started. The two-variable geometric counts in T1.7 and the
dense weighted sector remain open. T1.7 stays in progress; T4.1 stays
proved. Coverage stays 78/167 (main 28/73, companion 50/94).
The relaxation of the offset hypotheses is confirmed improvement
P1-MATH-0096. Confirmed improvements become 96. No new external input,
kernel axiom, dependency download, original manuscript edit or Palomar
registration is introduced.

Verified under Lean v4.36.0-rc2: full lake build (11063 jobs), source and ledger checks, actual axiom audit of 7100 declarations (only propext, Classical.choice and Quot.sound), and 4817 direct ledger/evidence declaration checks; Ubuntu root free space 14.98 GiB. Original manuscript bytes and all 167 statement hashes preserved.


## P1-MATH-0097: three fixed planar motifs

The fixed-plane, fixed-motif arithmetic in T20.6 is now proved
internally, using the checked positive quadratic and moving-root counts.
On a positive rational line b*y=a*x+c, positive integer a,b allow the
integer variable n=a*x and offset lists a*u and c+b*v. Exact product
scaling multiplies the original square prescription by a square, and
the resulting nonzero coefficient has no height restriction. The map
from a pair on the line to n is injective.

For each fixed polynomial value exponent and degree bound, a single
nondegenerate split equation on this line has at most N^epsilon
solutions, uniformly in the rational line and its integer coefficients.
The actual root-separation theorem removes at most two coordinates.
Three pairwise disjoint equation supports therefore leave one equation
with injective integer root shifts. All products and source events are
transported exactly; no affine independence surrogate or curve count
is assumed.

The resulting three-equation line count has one threshold before L,
all slopes, shifts, supports, coefficients and the solution population.
It needs one actual positive regular/direct pair on the line to establish
root separation. All other points are then counted by the same fixed
nondegenerate equation.

For a fixed plane b*y=a*x+g*z-h with 0<a,b<=N, L<=N, fixed triples
of offset motifs P,Q,R and fixed nonzero coefficients D_i, the number
of actual dyadic center triples satisfying all three transverse square
products is at most N^(1+epsilon). P and Q are nonempty and pairwise
disjoint among the three equations, and |P_i|+|Q_i| has a fixed degree
bound. R_i can have any size for this fixed-motif statement. The first
two windows have the actual injective/direct square-class hypotheses.
Neither g,h nor D_i has a height restriction. Fixing z gives positive
scaled values at most N^3, so the checked line estimate applies; summing
over its N dyadic values proves the bound. The proof includes an exact
finite fibre cardinality decomposition.

This replaces the source's per-fixed-motif Pila argument, which chooses
k+2 transverse products, by an internal three-product argument. It is
confirmed improvement P1-MATH-0097. The complete T20.6 still requires
orienting general planes and summing the admissible offset/small-prime
coefficient motifs, as well as selecting bounded-size motifs from its
macroscopic component population. Those steps are not asserted here.
T20.6 moves from not started to in progress. Coverage stays 78/167
(main 28/73, companion 50/94), confirmed improvements become 97.
The dense weighted sector remains open. No new external premise, axiom,
dependency download, original manuscript edit or Palomar registration
is introduced.

Verified under Lean v4.36.0-rc2: full lake build (11073 jobs), source and ledger checks, actual axiom audit of 7125 declarations (only propext, Classical.choice and Quot.sound), and 4842 direct ledger/evidence declaration checks; Ubuntu root free space 14.97 GiB. Original manuscript bytes and all 167 statement hashes preserved.


## Completion of T20.6 and P1-MATH-0097

Companion T20.6 is now complete, including the exact finite host
population and original affine primitive mass. All thresholds are chosen
before the length, integer prime cutoff, plane family, centers and motif
population. The final source population has the real cutoff H=C0*B,
real coefficient exponent K, at most B^K planes, nonzero integer normals
and all normal and constant coefficients bounded by B^K. Regularity,
distinct centers and pairwise direct effective square-class spaces are
retained exactly.

The finite budget of 3B formal window positions selects three disjoint
transverse motifs with a fixed size bound depending only on eta. It
never enumerates the macroscopic family or any covers. The actual
positive motif products have canonical odd-prime support codes, and
multiplying by the product of those codes gives an actual integer
square. Small-prime coefficient codes and bounded offset motifs have
N^epsilon choices, uniformly over every H<=C0*B. There is no bound on
the height of the resulting square coefficients in the arithmetic step.

A plane meeting the dyadic region with |h|<N has a positive and a negative
normal coefficient. A checked permutation orients that pair; relabeling
preserves all actual motif products, small-prime codes, sizes, disjointness
and transverse supports. Six permutations suffice. The oriented fixed-plane
count is summed over all motifs, codes and planes. This gives at most
N^(1+epsilon) ordered hosts, with no external Pila or BCN premise.
The exact real-to-integer cutoff equivalence uses the natural floor.

The actual affine joint probability of any such triple is at most p^2
by restricting to its direct regular pair. Summing the exact probabilities
gives mass at most N^(-1+epsilon), even before restricting to primitive
triples. The primitive mass is defined as the literal filtered sum and
inherits the same bound, including all incompatible zero-probability cases.
The weaker hypotheses and the three-equation argument complete confirmed
improvement P1-MATH-0097. No new improvement identifier is counted for
this completion of the same proof.

T20.6 moves from in progress to proved. Numbered coverage becomes 79/167
(main 28/73, companion 51/94); confirmed improvements remain 97.
This does not establish the six-vertex exclusion T20.8, the general
unrestricted two-parameter count T1.7, or the dense weighted pair sector.
No original manuscript, dependency version or Palomar registration is
changed.

Verified with Lean v4.36.0-rc2: full lake build (11091 jobs), actual axiom audit of all 7173 theorem/lemma declarations, direct Lean checks of all 4890 ledger/finding references, source integrity (138 manifest entries and 167 numbered statements), and git diff --check. Only propext, Classical.choice and Quot.sound occur; no sorry, admit, native_decide, or new axiom was added. Ubuntu root space after verification: 14.94 GiB.


## P1-MATH-0098: general private affine witnesses and rational triple activity

The unconditional positive connected activity assertion of main 14.5
is now proved on the exact positive-marginal original dyadic ground:
K3^+ >= c(C)*N^(-41/30), with explicit positive constant
c(C)=2^(-4-(71/30)*C)/240 and one threshold before N and all critical
lengths. The theorem also holds on every finite ground containing all
regular dyadic starts. This is not yet a lower bound for the total
third factorial cumulant; its incompatible and repeated-index terms
still need the sharper global error estimate. Main 14.5 therefore
moves from not started to in progress and is not counted complete.

For the literal ordered centers (10t,12t,15t), exact normalized pair
and triple intersections give the actual nullity exponent
rho(L)=floor((L-1)/6)+floor((L-1)/3)+floor((L-1)/5)-floor((L-1)/15).
The union cardinality identity is checked, including predecessor
values and all natural subtractions. It gives
(19/30)*L-4 <= rho(L) <= (19/30)*L+1. The original affine probability
is exactly p^3*2^rho, and the three original pair probabilities are
p^2 times the corresponding first three floor powers. The actual
centered coefficient equals p^3*(2^rho-2^f6-2^f3-2^f5+2).
For L>=60 it is at least half the joint probability and is positive,
which also proves actual connectedness.

The dyadic parameter set is the exact integer interval
[ceil(N/10),floor((2N-1)/15)]. Its cardinality is at least N/60 for
N>=1000. With H=10B, every failed private condition supplies an actual
H-defective normalized value. At each fixed offset its value is an
injective function of t. An exact 3B-list cover and the internal global
defect count give at most N^(1/2+epsilon) failed parameters. Hence at
least N/120 actual private witnesses remain uniformly in the critical
band. Their unordered supports are injective in t. Summation of their
actual positive coefficients and nonnegativity of every other
compatible coefficient prove the source positive-activity lower bound.

Confirmed improvement P1-MATH-0098 is the general finite affine witness
behind this argument. Arbitrary value bits on any private finite set
are realized by an actual prime-sign assignment, using a checked
extension of a linear functional. For any finite family of positive
integer-normalized windows, a private normalized union, a common
normalized value, and no predecessor/internal collision give an actual
affine witness and exact joint probability 2^(-(union.card-1)).
A rank/nullity identity turns this into p^r*2^rho. No cutoff, height,
separation, reduced-ratio or dyadic hypothesis is required for that
finite theorem. The source triple is its specialization.

Coverage stays 79/167 (main 28/73, companion 51/94); confirmed
improvements become 98. No Pila, BCN or unproved counting input is
used here. The original manuscripts, dependency versions and Palomar
state are unchanged.

Verified with Lean v4.36.0-rc2: full lake build (11127 jobs), actual axiom audit of all 7280 theorem/lemma declarations, direct Lean checks of all 4997 ledger/finding references, source integrity (138 manifest entries and 167 numbered statements), and git diff --check. Only propext, Classical.choice and Quot.sound occur. Ubuntu root space after verification: 14.87 GiB.


## P1-MATH-0098 extended to connected normalized overlap

The common-value hypothesis in the general finite affine probability
lemma is weakened to connected overlap. Define the actual intersection
graph of a finite family of nonempty value sets. Whenever this graph is
connected, the even square-class image of their union equals the sum
of the individual even images. A checked propagation along graph walks
proves this identity; private primes are not needed for the identity.

For positive integer-normalized windows, private normalized union and
absence of predecessor/internal collisions already supply actual affine
compatibility. Connected overlap now gives the exact total rank
union.card-1 and hence actual probability 2^(-(union.card-1)), even when
no value belongs to every normalized window. The corresponding exact
p^r*2^rho identity retains the literal rank/nullity equation.

This extends P1-MATH-0098 and the rational-witness tools without counting
a new improvement. The rational positive connected lower bound remains
unconditional; the lower bound for the total third factorial cumulant
and the full aligned-triple estimate remain open. Coverage stays 79/167
and confirmed improvements stay 98. No source manuscript, external
premise, dependency version or Palomar state changes.

Verified with Lean v4.36.0-rc2: full lake build (11131 jobs), actual axiom audit of all 7287 theorem/lemma declarations, direct Lean checks of all 5004 ledger/finding references, source integrity (138 manifest entries and 167 numbered statements), and git diff --check. Only propext, Classical.choice and Quot.sound occur. Ubuntu root space after verification: 14.86 GiB.


## Actual private rational sector and P1-MATH-0067

The actual private zero-intercept rational sector of main 14.3 is
proved, uniformly at polynomial logarithmic slope height. For primitive
0<u<v<w<2u and t>=1, use product normalizers (v*w,u*w,u*v) on the
actual centers (u*t,v*t,w*t). A private normalized union implies actual
affine compatibility: its predecessors lie below their common origin
and every internal value lies at or above it. No affine positivity
surrogate is assumed.

Common integer dilation preserves exact intersection cardinalities.
Reducing each physical ratio gives pair intersection bounds
B*gcd(u,v)/v+1, B*gcd(u,w)/w+1 and B*gcd(v,w)/w+1.
The actual triple intersection contains all origin+u*v*w*m for
0<=m<=floor((L-1)/w); only this lower bound is needed. Exact three-set
inclusion-exclusion then proves that 3L-(union.card-1) is at most
D(u,v,w)*L+5. Thus the actual effective rank is at least
(71/30)*L-5, and it is at least (43/18)*L-5 away from the unique
extremal physical triple (10,12,15).

These are finite uniform bounds with no slope-height restriction.
They give original affine probability at most
2^(5+(71/30)*C)*N^(-71/30), or
2^(5+(43/18)*C)*N^(-43/18) in the nonextremal sector.
The existing sharp geometric gap P1-MATH-0067 therefore becomes an
actual probability gap on these private normalized triples.

For each fixed natural k, the exact population enumerates primitive
u,v,w<=B^k and t<2N, retains the actual dyadic and private conditions,
and maps the resulting parameters to actual center triples. A checked
source-membership theorem shows that every qualifying dyadic triple
with w<=B^k is included; the t bound is forced by its first center.
The parameter budget is at most 16*B^(3k)*N. Summing actual joint
probabilities gives mass at most N^(-41/30+epsilon), or
N^(-25/18+epsilon) away from (10,12,15), after one uniform critical
threshold. The same bounds hold for the literal unordered family
populations; positivity justifies any repeated parameter overcount.

Main 14.3 moves from not started to in progress. This checkpoint does
not cover arbitrary affine intercept motifs, nonaligned third targets,
nonprivate normalization, irregular starts, or endpoint/contact cases.
It is not the full source proposition, nor a total third-cumulant
bound. Main 14.5 retains its proved positive connected lower assertion
and its unresolved total-cumulant passage. Coverage stays 79/167 and
confirmed improvements stay 98. P1-MATH-0067 is extended by this
application; no new improvement identifier is counted. No external
Pila or BCN estimate, original manuscript edit, dependency change or
Palomar registration is introduced.

Verified with Lean v4.36.0-rc2: full lake build (11147 jobs), actual axiom audit of all 7329 theorem/lemma declarations, direct Lean checks of all 5046 ledger/finding references, source integrity (138 manifest entries and 167 numbered statements), and git diff --check. Only propext, Classical.choice and Quot.sound occur. Ubuntu root space after verification: 14.83 GiB.


## Full even rank and common normalization invariance

The finite normalized-family criterion P1-MATH-0098 is strengthened:
injectivity on even selections of the normalized union suffices. Full
raw private-prime independence is unnecessary. A finite embedding
extension proves restriction to every subfamily, and rank-nullity
identifies the new condition with exact even-image rank union.card-1.
The literal set {1,2} proves the weakening is strict: its even map is
injective although the square value 1 has no private prime.

Any requested relative value bits are realized by an actual infinite
prime-sign sample, up to one common bit. That bit cancels in all run
constraints, giving actual affine compatibility whenever no normalized
predecessor equals a normalized internal value. Exact local ranks,
joint rank and actual infinite-model joint probability follow. A common
normalized value or, more generally, connected normalized overlap gives
rank union.card-1 and probability 2^(-(union.card-1)). Both versions
retain the exact p^r*2^rho formula with its literal dimension equation.

The new even-injectivity criterion, predecessor exclusivity and union
cardinality are invariant under every common positive integer dilation.
They therefore agree for any two positive normalization vectors with
a common positive rational ratio. There is no restriction on the prime
factors or height of the common factors. This removes a dependence on
the normalization choice that raw private-value independence does not
share.

For primitive zero-intercept rational triples, all checked actual
probability and mass upper bounds now hold under this strictly weaker
even-rank condition: point exponents -71/30 and -43/18, and ordered or
unordered host mass exponents -41/30 and -25/18 at polynomial
logarithmic slope height. The original private host population is
proved contained in the new one and its actual mass is dominated.

This extends findings P1-MATH-0098 and P1-MATH-0067 without adding an
improvement identifier. Main 14.3 and 14.5 remain in progress; arbitrary
affine intercepts, deficient even maps, nonaligned targets, irregular
starts and the total third-cumulant lower passage are still open.
Coverage stays 79/167 and confirmed improvements stay 98. No source
manuscript edit, new literature premise, dependency change or Palomar
registration is introduced.

Verified with Lean v4.36.0-rc2: full lake build (11163 jobs), actual kernel-axiom audit (7381 declarations; only propext, Classical.choice and Quot.sound), 5098 ledger/finding declaration checks, all 138 source manifest entries and 167 numbered-result hashes preserved; 14.80 GiB free on Ubuntu root.


## Unconditional fixed-height rational sector and sharp mass

All zero-intercept rational triples at fixed bounded slope height
now satisfy the sharp actual probability and mass upper exponents,
without a private-prime condition, even-map injectivity, local regularity
or an assumed affine compatibility witness. Incompatible systems are
included through their actual zero probabilities.

Fix Q>=1 before N. For primitive 0<u<v<w<2u with w<=Q, t>=1 and
u*t in the dyadic block, the entire merged product-normalized union
lies in one interval of width 2*Q^2*B, at a base between N/2 and
2*Q^2*N for large critical N. Its full value kernel embeds in the
large-prime kernel, which is supported on actual defective values of
that interval. The already proved local defect count gives a uniform
O_Q(B/log B) bound and hence an arbitrarily small multiple of B.
No Pila or BCN estimate is invoked.

A general finite family inequality retains the whole full-value defect:
union.card-1 <= actual joint rank + full normalized value-kernel rank.
It needs a common normalized value or connected normalized overlap,
with no independence assumption. The actual affine joint mass is at
most the inverse binary power of its actual joint rank, including zero
mass. Combining these checked facts with the rational union-cardinality
bounds proves actual point bounds N^(-71/30+epsilon), and
N^(-43/18+epsilon) away from (10,12,15), uniformly over all w<=Q.

The literal population contains every primitive dyadic zero-intercept
triple of height at most Q, including defective normalizations and
irregular windows. Its ordered count is at most 16*(Q+1)^3*N.
Summing actual probabilities gives ordered and unordered mass bounds
N^(-41/30+epsilon), and N^(-25/18+epsilon) in the nonextremal sector.
Q is fixed before the threshold; these unconditional bounds do not
assert uniformity for Q growing as a power of B.

The extremal private witnesses normalize by (6,5,4), whereas the
product normalizers at (10,12,15) are 30*(6,5,4). The checked common
dilation invariance transfers their full even rank exactly. Their
actual joint-probability sum is at least
(2^(-4-(71/30)*C)/120)*N^(-41/30). It embeds in the even-rank
polynomial-height population and, for Q>=15, in the unconditional
fixed-height population. Both sectors therefore attain the sharp
41/30 exponent. In the even-rank sector, the actual nonextremal mass
is at most an explicit constant times N^(-1/45+epsilon) times the
full mass; it is uniformly negligible in the critical band.

This extends P1-MATH-0067 and P1-MATH-0098 without a new improvement
identifier. The full aligned-family proposition 14.3 remains open:
arbitrary affine intercepts, growing third-slope height, nonaligned
targets and all source contact configurations are not covered here.
Main 14.5 retains its positive connected lower bound but not the total
third-cumulant passage. Coverage stays 79/167 and findings stay 98.
The original sources, dependencies and Palomar state are unchanged.

Verified with Lean v4.36.0-rc2: full lake build (11177 jobs), actual kernel-axiom audit (7416 declarations; only propext, Classical.choice and Quot.sound), 5133 ledger/finding declaration checks, all 138 source manifest entries and 167 numbered-result hashes preserved; 14.77 GiB free on Ubuntu root.


## P1-MATH-0099 — Explicit finite canonical overlap at arbitrary affine positions

A finite divisibility proof makes the canonical-overlap endpoint
error explicit and covers arbitrary independent translations of the
three windows. For primitive u<v<w<2u, every L>=0 and every actual
center vector X with X_i>=2, let U be the union of the three complete
windows normalized by (v*w,u*w,u*v). The checked bound is

3L-(U.card-1) <= D(u,v,w)*L+3.

No geometric alignment, common normalized value, dyadic restriction,
private prime, even-rank injectivity or affine compatibility is needed
for this finite cardinality statement. It implies
U.card-1 >= (71/30)*L-3, and at least (43/18)*L-3 away from
(10,12,15). The absolute error 3 is uniform in all slope heights and
translations. The previous explicit zero-intercept specialization had
error 5; the manuscript itself stated an unspecified absolute O(1).

The proof counts the third window only once. All its coincidences
with the first two windows lie in the union of divisibility classes
w/gcd(u,w) and w/gcd(v,w). Their least common multiple is exactly w
by primitive normalization. Exact floor counts in an arbitrary
complete positive-integer window give upper errors 1,1 and a lower
error 1 for their intersection. Combining this union bound with the
first-pair count proves the finite loss bound, without requiring a
lower bound on the actual triple intersection. In particular, the
three pair-overlap locations need not coincide.

If the normalized intersection graph is connected and the union has
full even rank, this finite result yields actual affine joint
probability bounds with constants 2^(3+(71/30)*C) and
2^(3+(43/18)*C), retaining the original infinite prime-sign law and
all zero-probability incompatible systems. Predecessor exclusivity
is not required for these upper bounds. The asymptotic exponents and
the unique extremal physical triple are unchanged.

P1-MATH-0099 records the new explicit finite proof and bound.
P1-MATH-0067 gains this arbitrary-translation actual-probability
application. Main 14.2 remains proved; main 14.3 remains in progress:
the full affine host aggregation, deficient normalized kernels at
growing height and nonaligned targets are still open. The total
third-cumulant lower passage is unchanged. Coverage remains 79/167;
confirmed improvements rise to 99. No original source, dependency,
external estimate or Palomar state changes.

Verified with Lean v4.36.0-rc2: full lake build (11185 jobs), actual kernel-axiom audit (7434 declarations; only propext, Classical.choice and Quot.sound), 5151 ledger/finding declaration checks, all 138 source manifest entries and 167 numbered-result hashes preserved; 14.75 GiB free on Ubuntu root.


## Distinct interior aligned-target triples at polynomial height

The interior distinct-physical-slope aligned-target sector of
main 14.3 is now unconditional at arbitrary fixed polynomial target
height, with arbitrary affine offsets and without local regularity,
private normalized primes, even-map injectivity or an assumed
compatibility witness.

Fix a reduced source channel 0<a<b<2a and a natural J before N.
Actual source vertices satisfy label_x(i)=a*t and label_y(j)=b*t.
A reduced target c/d satisfies d*z=c*t+h, with d<=B^J and
|h|<=B^J. The three physical slopes a*d,b*d,c are required distinct
and in the strict interior ratio range: c<2*a*d and b*d<2*c.
Every actual dyadic triple with these data is covered, including
arithmetically exceptional source pairs and irregular local windows.
Zero-probability incompatible systems are included in the upper bound.

The existing checked TargetUnionResidual estimate already bounds the
actual omitted-prime row space by an arbitrarily small multiple of B,
uniformly in c,d,h. The full merged-value kernel embeds in this row
space. A new finite algebraic estimate bounds the full span of any
three finite sets by the sum of their local even spaces plus three
anchor directions; it needs no intersections or connected-overlap
assumption. Hence union.card <= actual joint rank + full kernel rank+3.

The physical triple is automatically primitive because the source
and target ratios are reduced. Its three possible orderings transfer
the canonical finite bound of P1-MATH-0099 to the actual old/new merged
set by a common integer dilation. This gives actual joint rank at
least (71/30)*L-5-o(L), and actual infinite-model joint probability
at most N^(-71/30+epsilon). No total-rank bound, compatibility or
point probability is supplied as a premise.

A literal source/target parameter pool enumerates t<3N, the B^2 old
vertex choices and every member of the actual affine target pool.
It has cardinality at most 18*a*N*B^(3J+2). A checked source
membership theorem reconstructs the original x,y,z from these codes;
the numerator bound c<=2*a*B^J follows from dyadic geometry. The final
finite host set retains exactly three-element families with actual
representations and the stated physical conditions. Every qualifying
actual source is included after one common critical threshold.
Its cardinality is at most N^(1+epsilon) and its actual joint mass
is at most N^(-41/30+epsilon).

A separate checked geometric helper shows that three normalized
windows with connected overlap lie in one interval of radius 5*Q*B
around the first normalized center when their multipliers are <=Q.
It supplies exact interval and macroscopic base bounds and a
common-point connectivity construction; the growing-height probability
and mass proof does not assume this connected-overlap criterion.

This extends findings P1-MATH-0067 and P1-MATH-0099 and the partial
main 14.3 correspondence. Nonaligned targets, repeated physical
slopes and dyadic endpoint populations remain open in the full source
proposition. The lower bound for the total third factorial cumulant
also remains open. Coverage stays 79/167 and confirmed improvements
stay 99. The source manuscripts, dependencies, external-input scope
and Palomar state are unchanged.

Verified with Lean v4.36.0-rc2: full lake build (11199 jobs), actual kernel-axiom audit (7463 declarations; only propext, Classical.choice and Quot.sound), 5180 ledger/finding declaration checks, all 138 source manifest entries and 167 numbered-result hashes preserved; 14.73 GiB free on Ubuntu root.


## Repeated physical slopes and every represented interior target

The repeated-physical-slope sector above a fixed exact source
channel is now proved, including every actual compatible contact
at separation exactly L. The union with the distinct-slope sector
covers every represented interior aligned target at polynomial height.

If the reduced target c/d equals a physical source slope, namely
c=a*d or c=b*d, then d=1 and c=a or b. For a positive actual triple
probability, distinct windows at the repeated slope have complete
value sets intersecting in at most one endpoint. Both intersections
with the remaining window lie in one divisibility class of that
remaining window. They must be counted as a union, rather than
adding two full pairwise counts. Exact divisibility counts give
canonical even-image dimension at least (5/2)*L-1. The source channel
0<a<b<2a forces a>=2 and b>=3, so this bound covers both physical
choices uniformly.

The full merged value kernel is still bounded by the proved actual
target-union row estimate. A finite three-window probability lemma
retains that entire defect and the three anchor directions, with no
overlap-graph assumption. Thus every physical target has actual
joint probability at most N^(-5/2+epsilon). Zero-probability triples
are included by a separate proved branch; affine compatibility is not
assumed. The literal three-element host population uses the same
checked source/target pool of size at most 18*a*N*B^(3J+2), and every
qualifying source is included after a common critical threshold.
Its actual mass is at most N^(-3/2+epsilon).

An explicit interior representation keeps arbitrary affine offsets,
reduced c/d, d<=B^J, |h|<=B^J, the exact source-vertex equations,
actual dyadic membership and only the two strict physical-interior
inequalities. It does not require distinct physical slopes. Every
such three-element family belongs to the literal union of distinct
and physical host populations. Their actual combined mass is at
most N^(-41/30+epsilon), uniformly at each fixed source channel
and fixed natural J. No private-prime, local regularity, full even
rank, connected normalized overlap or external counting hypothesis
is imposed. The exact source-pair vertex representation is explicit;
no claim about enlarged source alignments without such vertices is
made here.

This extends the finite canonical counting tools of P1-MATH-0099
without adding an improvement identifier. Main 14.3 remains in
progress: the dyadic endpoint populations and the nonaligned-target
sector still need their actual mass bounds. The total third-cumulant
lower passage is also unchanged. Coverage remains 79/167 and
confirmed improvements remain 99. Original manuscripts, dependency
versions, external-input scope and Palomar state are unchanged.

Verified with Lean v4.36.0-rc2: full lake build (11209 jobs), actual kernel-axiom audit (7483 declarations; only propext, Classical.choice and Quot.sound), 5200 ledger/finding declaration checks, all 138 source manifest entries and 167 numbered-result hashes preserved; 14.71 GiB free on Ubuntu root.


## All represented polynomial-height aligned targets, including endpoints

Every represented polynomial-height affine aligned target of a
fixed reduced exact source channel is now covered, including the
entire dyadic endpoint population. No strict physical-interior or
distinct-slope condition remains in the final representation.

First, the actual fixed-channel source pair satisfies the uniform
point bound N^(-(2-1/b)+epsilon), and hence N^(-5/3+epsilon)
for b>=3. This uses the proved actual pair-loss estimate, includes
all local and normalized arithmetic defects, and does not assume
regularity, private primes or positive affine mass.

For H=B^J, define endpoint radius R=B+2H. The source parameter t<3N
is near an endpoint if |a*t-N|<=R or |b*t-2N|<=R. Injectivity of
the two integer labels gives at most 4R+2 such parameters. Their
literal source/target code pool includes the B^2 actual old vertex
choices and the entire finite affine target pool, and has cardinality
at most 84*a*B^(4J+3), with no factor N. A checked source-membership
proof reconstructs the original x,y,z and proves inclusion of every
qualifying endpoint family. The numerator bound is discharged by
actual dyadic geometry rather than supplied as an extra premise.

Each endpoint triple has actual joint probability at most that of
its source pair. The original infinite-model joint activation is
proved antitone under adding starts. The endpoint host count is
N^epsilon, and summing its actual probabilities gives mass
N^(-5/3+epsilon), uniformly in the critical band, including irregular,
badly normalized and incompatible systems.

Every represented bounded affine target either has a near source
parameter or lies in the strict physical interior. In the away case,
the proved dyadic ratio lemma supplies both interior inequalities.
Thus every three-element family with actual dyadic x,y,z, exact
source vertices label_x(i)=a*t and label_y(j)=b*t, reduced positive
c/d, d<=B^J, |h|<=B^J and d*z=c*t+h lies in the literal union of
interior and endpoint hosts after one common threshold. The union
includes distinct physical slopes, repeated slopes and exact contacts.
Its actual mass is at most N^(-41/30+epsilon), unconditionally for
each fixed reduced channel 0<a<b<2a and fixed natural J.

This extends P1-MATH-0099 and main 14.3's partial correspondence
without a new improvement identifier. The nonaligned-target sector
of the source proposition is still open. Source alignments without
the explicit exact-vertex representation are not silently included.
The total third-cumulant lower passage also remains open. Coverage
stays 79/167 and confirmed improvements stay 99. Original manuscript
bytes, dependency versions, external-input scope and Palomar state
are unchanged.

Verified with Lean v4.36.0-rc2: full lake build (11217 jobs), actual kernel-axiom audit (7500 declarations; only propext, Classical.choice and Quot.sound), 5217 ledger/finding declaration checks, all 138 source manifest entries and 167 numbered-result hashes preserved; 14.69 GiB free on Ubuntu root.


## One common threshold for finitely many represented source channels

The actual aligned-target population and its source completeness
are now aggregated over any fixed finite family F of reduced interior
source channels. Each channel may have its own fixed natural target
height exponent J(a,b). One critical threshold precedes N, L, every
channel in F and every actual three-element represented family.
The literal union mass remains at most N^(-41/30+epsilon); repeated
families are handled by nonnegative actual joint probabilities.
No overlap-disjointness or target probability is assumed.

This is the finite-family aligned-target sector of main 14.3,
retaining all previously proved distinct-slope, physical and endpoint
cases and exact contacts. The nonaligned-target sector remains open,
and no source alignment lacking the explicit exact source-vertex
representation is included silently. Coverage stays 79/167 and
confirmed improvements stay 99. No original source, dependency,
external estimate or Palomar state changes.

Verified with Lean v4.36.0-rc2: full lake build (11219 jobs), actual kernel-axiom audit (7502 declarations; only propext, Classical.choice and Quot.sound), 5219 ledger/finding declaration checks, all 138 source manifest entries and 167 numbered-result hashes preserved; 14.68 GiB free on Ubuntu root.


## Polynomial-height aligned targets above enlarged sources, including zero exact units

The polynomial-height aligned-target sector now allows the manuscript's
enlarged source condition |b*x-a*y| <= (a+b)*B, with B=L+1,
in place of two exact source vertices. Only one actual vertex
label_x(i)=a*t is retained. Every positive source window has such
a vertex once B>a; the second source has the proved virtual bound
|b*t-y| <= D*B with D=a+2*b. Sources with zero exact units are included.

The actual merged value set lies in two progressions of lengths
6*b*B and L and in an interval of radius 8*a*b*H*B around a*b*c*t.
The full residual rank is uniformly o(B) for H=B^J. The actual point
bounds N^(-71/30+epsilon) for distinct interior physical ratios and
N^(-5/2+epsilon) for repeated ratios retain every local defect and
affine incompatibility. No private-prime, even-rank or regularity
premise is introduced.

A literal source code replaces the second vertex by the integer
displacement y-b*t in [-D*B,D*B]. Its complete target-family pool
has at most 18*a*(2*D+1)*N*B^(3*J+2) codes. Near endpoints, radius
D*B+2*B^J yields at most
6*a*(2*D+1)*(4*D+10)*B^(4*J+3) codes, with no factor N.
Actual enlarged-source pair probabilities give endpoint triple mass
N^(-5/3+epsilon). Source completeness and the final actual mass
N^(-41/30+epsilon) hold for all represented polynomial-height affine
targets, including exact contacts, and share one threshold across
any fixed finite family of reduced channels 0<a<b<2*a.

The target representation d*z=c*t+h still has to satisfy the stated
height bounds relative to the chosen source parameter. The nonaligned
target sector and the total third-cumulant lower passage remain open.
Main 14.3 remains in progress; coverage stays 79/167 and confirmed
improvements stay 99. This extends P1-MATH-0099 without claiming a
new manuscript conclusion error or a completed Palomar submission.
Original manuscript bytes, dependencies and external-input scope are unchanged.

Verified with Lean v4.36.0-rc2: full lake build (11245 jobs), actual kernel-axiom audit (7557 declarations; only propext, Classical.choice and Quot.sound), 5274 ledger/finding declaration checks, all 138 source manifest entries and 167 numbered-result hashes preserved; 14.62 GiB free on Ubuntu root.


## Literal geometric and compressed aligned target populations

The aligned-target mass is now stated on literal dyadic three-element
families defined by geometric alignment predicates, rather than an
assumed reduced affine representation. For a source channel in any
fixed finite reduced interior family F, a second geometric relation
|s*x-r*z| <= (r+s)*B supplies the required affine data. The proof
selects one actual x-window multiple of a, reduces the coefficient
pair by its gcd and bounds the resulting integer offset. For fixed
r,s<=Q, quadratic word height suffices. More generally r,s<=B^K
give denominator and offset at most B^(K+2), uniformly for fixed K.
The actual literal family mass is at most N^(-41/30+epsilon).
This includes the paper's cubic geometric target height K=3.

A second literal family uses alignment of the target with the true
compressed center X=a*b*t in a fixed enlarged width D*B. The existing
reduced-data construction supplies height B^5 inside the proof.
Its actual mass has the same N^(-41/30+epsilon) bound across F,
including zero-unit sources, physical ratios, endpoint populations,
local arithmetic defects and affine incompatibility. Source membership
and inclusion in the proved finite affine pool are checked separately.
No affine coefficient or target probability is assumed by either
geometric family definition.

The compressed center in this statement is based on an actual source
vertex label_x(i)=a*t. Changing this parameter or allowing nonaligned
targets is not inferred without a further argument. Main 14.3 remains
in progress and the total third-cumulant lower passage remains open.
Coverage stays 79/167 and improvements stay 99. Original manuscripts,
dependencies, external-input scope and Palomar state are unchanged.

Verified with Lean v4.36.0-rc2: full lake build (11251 jobs), actual kernel-axiom audit (7571 declarations; only propext, Classical.choice and Quot.sound), 5288 ledger/finding declaration checks, all 138 source manifest entries and 167 numbered-result hashes preserved; 14.61 GiB free on Ubuntu root.


## P1-MATH-0100 — An effective all-cutoff lower count for two small odd kernels

The complete lower-count portion of companion T1.5 is now proved on
literal dyadic windows, with a stronger explicit scope. For every
fixed 1/2<beta<1 and epsilon>0, one threshold precedes N, every
natural prime cutoff H and every length L>=2. The number of actual
dyadic windows containing at least two distinct values whose
individual large odd kernels are at most N^beta is at least
N^(beta-epsilon). Taking H=B=L+1 and a critical-band length gives
the source lower count. This concerns two individual bounds, rather
than the different existing product-cap upper count.

The proof makes the source CRT construction effective. In the box
[1,M]^2, a common-divisor cover and the elementary finite bound
sum_(d=2)^M 1/d^2 <= 3/4 supply at least M^2/4 coprime pairs.
Restricting to [D,10D]^2 leaves at least 5D^2 such pairs. For each
positive coprime d,e, CRT constructs at least N/(d^2*e^2)-1 integer
solutions in the exact interval [N,2N). If N>=40000*D^4, their
literal square-divisibility incidence count is at least
N/(4000*D^2). Each integer has at most tau(n)*tau(n+1) witnesses,
and the proved uniform divisor bound absorbs this multiplicity.
A squared divisor d^2 of n proves K_H(n)*d^2<=n for arbitrary H.
The scale D=ceil(2*N^((1-beta)/2)) then yields the asserted exponent.
The neighboring values n,n+1 are proved to belong to the actual
complete window at x=n for every L>=2.

This is P1-MATH-0100: the lower exponent and its all-cutoff uniformity
are isolated explicitly, with finite constants. The CRT idea and the
condition beta>1/2 were already present in the source proof; no error
in a manuscript conclusion is asserted. The upper count
N^(max(beta,7/12)+epsilon) still requires the unresolved determinant
estimate. Hence T1.5 moves from not_started to in_progress and is
not counted complete; neither is its full sharpness equality.
Coverage stays 79/167. Improvements now total 100. There are no new
external estimates, dependency changes or Palomar claims, and the
original manuscript sources remain byte-for-byte unchanged.

Verified with Lean v4.36.0-rc2: full lake build (11261 jobs), actual kernel-axiom audit (7593 declarations; only propext, Classical.choice and Quot.sound), 5310 ledger/finding declaration checks, all 138 source manifest entries and 167 numbered-result hashes preserved; 14.60 GiB free on Ubuntu root.


## Actual overlapping principal-edge mass is negligible relative to beta squared

The literal dyadic triples containing at least two actual compatible
principal edges now have total joint activation mass at most
N^(-41/30+epsilon), uniformly in every source private-prime cutoff H.
Every such triple is proved to have an exact-unit source in 2:3 or 3:4
and a bounded geometric target relative to one of that source's two
endpoints. Common exact-unit parameters convert either endpoint
relation into reduced affine height B^2 inside the proof. The source
edge may be any actual retained principal edge; no triple compatibility
or private normalization of the target is assumed.

The complete ordered overlapping-edge population consists of
(e,f) in the actual principal edge family squared, with e!=f and
nonempty intersection. Its union is proved to be a three-element
family in the preceding literal population. Fibres over a triple
have at most nine ordered edge pairs. Grouping the actual nonnegative
q(e union f) weights proves that their complete sum is at most nine
times the triple mass, and hence at most N^(-41/30+epsilon).
The estimate retains incompatible triples with zero actual mass.

For cutoffs 8*B<=H<=D*B with D fixed, the proved actual beta phase
beta>=c*L*N^(-2/3) yields an explicit relative conclusion: for every
delta>0, one threshold precedes N,L,H and the ordered overlapping
joint mass is at most delta*beta^2. Thus the shared-vertex portion
of the second principal-edge factorial moment is o(beta^2), with
actual probabilities and the actual beta, rather than nominal weights.

The disjoint-edge, four-start contribution and its leading beta^2
asymptotic remain open. Companion T1.17 stays in progress. The target
nonalignment sector of main 14.3 and the total third-cumulant lower
passage also remain open. This is a consequence and extension of
P1-MATH-0099, without a new improvement ID. Coverage stays 79/167
and improvements stay 100. Original manuscripts, dependencies,
external-input scope and Palomar state are unchanged.

Verified with Lean v4.36.0-rc2: full lake build (11275 jobs), actual kernel-axiom audit (7615 declarations; only propext, Classical.choice and Quot.sound), 5332 ledger/finding declaration checks, all 138 source manifest entries and 167 numbered-result hashes preserved; 14.57 GiB free on Ubuntu root.


## P1-MATH-0101 — An explicit actual principal-edge second-moment lower error

The complete lower direction of companion T1.17 is now proved for
the actual principal-edge count Xi, with the sharper explicit error

  E[Xi*(Xi-1)] >= beta^2 - N^(-7/3+epsilon).

One critical threshold precedes N, L and every private-prime cutoff H.
Here beta is the actual sum of joint activations over the literal
compatible principal edges in channels 2:3 and 3:4. For fixed D and
8*B<=H<=D*B, the proved beta phase implies that, for every delta>0,
the actual second factorial moment is eventually at least
(1-delta)*beta^2, uniformly before L and H.

For fixed channel and two exact vertex offsets, the normalized source
union is reconstructed as an effective finite block at its actual
anchor. The anchor determines the original pair injectively. Every
value is between N/2 and 12*N and within 4*B of that anchor. Applying
the complete actual dependent-block count (main 10.3) and enumerating
the 2*B^2 source patterns proves that the entire principal-edge pair
population whose event spaces intersect nontrivially has cardinality
at most N^(1+epsilon), including diagonal pairs. No private-prime
assumption is added to this intermediate compressed-source count.

Each actual principal-edge probability is at most N^(-5/3+epsilon).
Consequently the sum of the independent product weights q(e)*q(f)
over all those coupled pairs is at most N^(-7/3+epsilon). Across
direct event spaces the actual joint activations factor exactly,
with every zero-mass case retained by the unrestricted component
factorization. The exact finite inequality
beta^2 <= sum_(e!=f) q(e union f) + coupledProductMass
then gives the claimed lower error. A generic Boolean-family identity
and the actual infinite-cylinder transport identify this ordered
joint sum with E[Xi*(Xi-1)] under the original prime-sign measure.

This controls product weights in the coupled population. Its actual
joint activation mass still needs an upper estimate, so the full
T1.17 asymptotic beta^2+o(beta^2), and its stated full upper bound,
remain open. T1.17 stays in progress. This is P1-MATH-0101: an explicit
one-sided error and a proof of the lower direction using the unweighted
half-count, without the unresolved weighted nonaligned profile.
Coverage stays 79/167; improvements now total 101. No manuscript
conclusion error, new external estimate, dependency change or Palomar
submission is asserted. The original manuscript bytes are unchanged.

Verified with Lean v4.36.0-rc2: full lake build (11295 jobs), actual kernel-axiom audit (7652 declarations; only propext, Classical.choice and Quot.sound), 5369 ledger/finding declaration checks, all 138 source manifest entries and 167 numbered-result hashes preserved; 14.53 GiB free on Ubuntu root.


## P1-MATH-0102 — An elementary uniform upper count for two small odd kernels

An unconditional elementary upper count for two individually small odd
kernels is now proved on the literal complete windows. For every fixed
epsilon>0, one threshold precedes every T>=0, cutoff H<=D*log N and
length with L+1<=E*(log N)^A and L<=N. The actual window count is at
most (T+N^(2/3))*N^epsilon. In the critical band, H=B=L+1 and T=N^beta
give the upper exponent max(beta,2/3)+epsilon for every real beta.
Together with the previously proved all-cutoff lower count, this
establishes the sharp exponent beta for 2/3<=beta<1. This is a complete
subregime of companion T1.5, rather than its full 7/12 conclusion.

The proof makes a different use of the source elementary congruence
calculation. Fix the two actual small-prime odd supports and a positive
shift h. The canonical square parts d,e give divisibilities c1*d^2|n
and c2*e^2|n+h. An injection into actual integer linear fibres proves
the finite bound X*h/(c1*c2*d^2*e^2)+1 up to height X. The individual
kernel bounds imply c1*d^2,c2*e^2>=N/(2T) for n>=N/2. Summing their
reciprocal weights gives the explicit bound 24*h*T plus the number of
distinct actual square-part pairs, for n<=3N. This uses a finite
reciprocal-square tail bound 2/A for every positive real lower endpoint
A, including A<1. No dyadic subdivision of d,e is needed.

Split at P=ceil(N^(2/3)). Below P, the proved positive product-pair
count bounds the number of actual square-part pairs by P*N^epsilon.
Above P, the proved identity K_H(n)*K_H(n+h)*(d*e)^2<=n*(n+h)
forces the ACTUAL kernel product to be at most 16*N^(2/3). Only this
large-square sector is passed to the earlier product-cap count. The
argument never substitutes a product cap for the two individual bounds.
Small-prime support counts, the shift, the number of window offsets
and all constants are absorbed uniformly. A literal finite offset
cover and an injective translation identify the actual window count.

This is P1-MATH-0102: a Reuss-free upper estimate uniform in the real
kernel threshold, with explicit finite weighted fibres and an exact
sharpness subregime. It complements P1-MATH-0100. The full source
upper exponent max(beta,7/12), and sharpness on 7/12<=beta<2/3,
remain open. T1.5 stays in_progress and coverage stays 79/167.
There is no new external input, dependency change or manuscript
conclusion error. The original sources remain byte-for-byte unchanged;
Palomar remains a later milestone. There are now 102 improvements.

Verified with Lean v4.36.0-rc2: full lake build (11311 jobs), actual Audit.lean kernel-axiom audit (7674 declarations; only propext, Classical.choice, Quot.sound), all 5391 ledger references, source integrity (138 manifest entries / 167 numbered results), and git diff --check. Ubuntu root free space: 14.50 GiB.


## P1-MATH-0103 — Aligned principal-edge pairs and the exact residual second-moment error

The four-vertex principal-edge sector containing an actual aligned
triple now has total ordered joint mass at most N^(-41/30+epsilon),
uniformly over every private-prime cutoff H after one critical-band
threshold. The seed may use either principal source channel and every
reduced affine target of any fixed polynomial height B^J, including
physical, endpoint, contact, irregular and badly normalized targets
already retained by the aligned-triple mass theorem. The literal pair
sector contains every disjoint actual principal-edge pair whose union
contains such a represented triple; the source-cover theorem checks
this inclusion. More generally, for every fixed finite source channel
family and fixed additional size k, the actual mass of all (3+k)-sets
containing an aligned triple has the same N^(-41/30+epsilon) bound.
The fourth and further windows require no extra alignment condition.

The proof uses the already proved actual unordered seed propagation,
with all zero masses retained, followed by the proved sharp aligned
triple bound. A four-set has at most 36 ordered pair codes in the
literal two-edge cover; the constant is absorbed asymptotically.
This improves the source N^(-27/20+o(1)) upper exponent in this
aligned sector, without a separate rank-loss argument for the last
window. Its contribution is proved o(beta^2).

The entire actual second factorial joint sum S has a precise residual
description. Define R as the sum of absolute actual covariances over
distinct principal edges with disjoint vertex sets, coupled event
spaces, and no aligned triple seed of the above polynomial height.
These definitions retain incompatible merged systems and their zero
joint probabilities. A finite upper decomposition proves
S<=beta^2+shared_joint_mass+aligned_joint_mass+R. Conversely,
R<=S-beta^2+2*coupled_product_mass; independent event spaces factor
exactly, and every negative covariance is bounded by its baseline
product. The product mass includes the diagonal and was already
proved at most N^(-7/3+epsilon).

Consequently the new unconditional estimates are
  |S-beta^2| <= R + N^(-41/30+epsilon),
  R <= S-beta^2 + N^(-7/3+epsilon), and
  ||S-beta^2|-R| <= N^(-41/30+epsilon).
The first is transported to the actual infinite prime-sign expectation
of Xi^2-Xi. The last also holds with error delta*beta^2 for every
fixed delta>0 and cutoffs 8B<=H<=D*B, after one common threshold.
Thus the remaining relative second-moment claim is exactly localized
to a concrete nonnegative residual covariance sum, up to a proved
negligible error. No residual asymptotic estimate is assumed as a
proof of T1.17, and that numbered result stays in_progress.

This is P1-MATH-0103. It records the stronger aligned-sector exponent
and the effective two-sided residual characterization. Coverage stays
79/167 and improvements total 103. The nonaligned residual covariance
bound is still open; no manuscript conclusion error is asserted.
There are no new external estimates or dependencies, the original
sources are unchanged, and Palomar remains a later milestone.

Verified with Lean v4.36.0-rc2: full lake build (11321 jobs), actual Audit.lean kernel-axiom audit (7694 declarations; only propext, Classical.choice, Quot.sound), all 5411 ledger references, source integrity (138 manifest entries / 167 numbered results), and git diff --check. Ubuntu root free space: 14.48 GiB.


## P1-MATH-0104 — Only dense block intersections remain in the second-moment error

The remaining actual principal-edge second-moment covariance sum is
now localized further to pairs whose complete event-space intersection
has dimension greater than 29L/30. This is an actual block intersection,
not an assumed relation-count input. The pairs still have disjoint
vertex sets, coupled spaces and no aligned triple seed of fixed
polynomial target height B^J, as in P1-MATH-0103. Write R_dense for the
sum of their absolute actual covariances and S for the complete
ordered factorial joint sum. Uniformly over all private cutoffs H,
  ||S-beta^2|-R_dense| <= N^(-41/30+epsilon),
  R_dense <= S-beta^2 + N^(-7/3+epsilon).
The comparison is also transported to the actual infinite-measure
expectation of Xi^2-Xi and to an error delta*beta^2 for every fixed
delta>0 and cutoffs 8B<=H<=D*B. No estimate for R_dense is presumed.

The generic finite probability argument is proved first. Every actual
positive block activation has exactly its homogeneous zero-target
probability. For arbitrary finite blocks e,f, the homogeneous union
probability is exactly 2^d times the product of their homogeneous
probabilities, where d is the dimension of the intersection of their
full square-class spans. Consequently, for positive actual marginals,
the absolute actual covariance is at most 2^d*q(e)*q(f). Incompatible
unions, including zero joint probabilities, are explicitly retained.
The identity holds for overlapping blocks as well.

An exact finite rank split and the previously proved coupled product
mass then show that, for every fixed real theta, all coupled principal
edge pairs with d<=theta*L have total absolute covariance at most
N^(-7/3+theta+epsilon). One threshold precedes every private cutoff.
The conversion from 2^d to a power of N is proved uniformly on the
critical band. Taking theta=29/30 makes this error
N^(-41/30+epsilon), the same as the aligned-sector error. Thus only
the strictly denser residual population can affect the beta^2 scale.

This is P1-MATH-0104: an explicit quantitative cutoff and a two-sided
characterization of the remaining second-moment obstruction. It does
not prove the dense residual covariance estimate or complete T1.17.
Coverage stays 79/167 and improvements total 104. No manuscript
conclusion error is asserted. No external estimate, dependency change,
source-byte edit or Palomar registration is introduced.

Verified with Lean v4.36.0-rc2: full lake build (11329 jobs), actual Audit.lean kernel-axiom audit (7711 declarations; only propext, Classical.choice, Quot.sound), all 5428 ledger references, source integrity (138 manifest entries / 167 numbered results), and git diff --check. Ubuntu root free space: 14.46 GiB.


## Multiquadratic split radicands — the exact square-class independence step

The square-class independence assertion at the beginning of Step 1
of companion T1.7 is now proved literally. Let F be ANY field of
characteristic zero, and use the fraction field of F[X][Y]. For a
family of integer root lists I_i,J_i, pairwise disjoint within each
coordinate list, and arbitrary nonzero constants c_i in F, the actual
square classes of
  c_i * product_(a in I_i)(X+a) * product_(b in J_i)(Y+b)
are linearly independent over F_2 whenever I_i or J_i is nonempty
for each i. The index type can be arbitrary; linear independence is
checked on every finite subfamily. In particular this applies over
an algebraically closed characteristic-zero base, not just over Q.

The proof uses the existing internal reflection of squares from a
fraction field to its integrally closed polynomial ring. Passing to
one coordinate fraction field makes the scalar and the other split
factor units; the remaining nonempty split factor is separable and
not a unit, so its product with this nonzero scalar is not a square.
Swapping coordinates covers an empty root list on either side.
Exact product identities identify a finite subfamily product with
the nonzero product scalar times the split word on the two literal
unions of its disjoint root lists. Every nonempty subfamily product
is therefore nonsquare. The existing actual field square-class
quotient and a proved binary coefficient argument turn this into
literal F_2 linear independence. Nonzero radicands are proved too.

There is no smoothness or coefficient-height hypothesis in this
algebraic assertion. These hypotheses were already unnecessary for
the source independence argument, so no new mathematical-improvement
identifier is assigned. This adds the checked algebraic independence
part of Step 1, rather than a multiquadratic surface point count.
The general coordinate-ring freeness, field/localization and finite
birational projection arguments, the surface covering, curve-degree
exclusions and the two-variable estimates remain open. T1.7 stays
in_progress, coverage stays 79/167 and confirmed improvements stay
104. No external determinant estimate is treated as proved, and no
dependency download, original source change or Palomar registration
is introduced.

Verified with Lean v4.36.0-rc2: full lake build (11333 jobs), actual Audit.lean kernel-axiom audit (7726 declarations; only propext, Classical.choice, Quot.sound), all 5443 ledger references, source integrity (138 manifest entries / 167 numbered results), and git diff --check. Ubuntu root free space: 14.45 GiB.


## The literal multiquadratic generic field and its degree

The generic multiquadratic field in Step 1 of companion T1.7 is now
constructed internally and proved to have degree 2^k. This advances
the previously checked square-class independence to a literal field
construction, rather than postulating an abstract extension degree.
For every commutative base ring and finite radicand list, a recursively
defined tower of actual quadratic algebras has an explicit free basis
indexed by one binary choice per equation. Over a nontrivial base its
finite rank is 2^k. The base embedding is proved injective, each actual
radical generator squares to its specified base radicand, and those
generators generate the entire algebra. A structural induction
principle is proved on the literal tower.

Over a characteristic-zero field, an exact one-step criterion says
that a base element g becomes square after adjoining sqrt(f), f!=0,
if and only if g or f*g is square in the base. This includes the
reducible one-step algebra as well. Induction proves a full descent
criterion for an independent radicand list: a base element g becomes
square exactly when g times the product of some selected sublist is
square in the original field. If every nonempty selected sublist has
nonsquare product, each successive radical remains nonsquare and the
literal tower is a field. No fieldhood or extension degree is assumed.

The source application uses the actual scaled split radicands over
Frac(F[X][Y]), for every characteristic-zero field F. Pairwise disjoint
integer root lists, at least one nonempty root list per equation, and
arbitrary nonzero constants prove the required sublist condition by
the already checked nonsquare finite-product theorem. Every finite
list of distinct equations therefore gives an actual generic field
of degree 2^k. This remains true when F is algebraically closed; no
smoothness or coefficient-height hypothesis enters this algebraic
step.

The explicit coordinate-ring quotient presentation and its embedding
in this generic field, the finite birational sum-of-radicals projection,
the projective and curve-degree arguments and the two-variable point
counts remain open. Thus this is further checked algebraic groundwork
for T1.7, not completion of the geometric count. T1.7 stays in_progress,
coverage stays 79/167 and improvements stay 104; the source already
uses this algebraic argument, so no new improvement identifier is
assigned. No external counting input, dependency download, original
manuscript change or Palomar registration is introduced.

Verified with Lean v4.36.0-rc2: full lake build (11341 jobs), actual Audit.lean kernel-axiom audit (7745 declarations; only propext, Classical.choice, Quot.sound), all 5462 ledger references, source integrity (138 manifest entries / 167 numbered results), and git diff --check. Ubuntu root free space: 14.44 GiB.


## The actual coordinate domain and the finite affine radical-sum projection

The actual split-radical coordinate algebra in Step 1 of companion
T1.7 is now proved to be a domain, and the affine sum-of-radicals
projection is proved finite. The construction continues to work over
every characteristic-zero base field F, including an algebraic closure.
It uses the literal tower over F[X][Y] of the actual scaled split
polynomials, rather than assuming geometric integrality of a surface.

First, the tower has its exact universal property. For every base
ring homomorphism R->A and every actual family x_i in A satisfying
x_i^2=phi(f_i), there exists a unique ring homomorphism from the
tower to A that agrees with phi on the base and sends each actual
radical generator to x_i. The corresponding algebra-point equivalence
is also constructed. An explicit two-coordinate quadratic ring map,
its uniqueness and a recursive lift prove this, including empty
systems and arbitrary commutative target algebras. Thus the tower
represents precisely the simultaneous polynomial equations. Evaluation
at actual values X,Y specializes this statement to the source split
system; the scaled-word evaluation formula is checked explicitly.

Next, an actual recursive base-change homomorphism is constructed for
every ring homomorphism R->S. It is proved to commute with the base
embeddings, and it is injective whenever the base homomorphism is.
The quadratic step keeps the literal new parameter and the proved
coefficient equality visible, avoiding an assumed localization map.
Specializing to F[X][Y]->Frac(F[X][Y]) embeds the coordinate tower in
the actual generic field already proved to have degree 2^k. This
proves the coordinate domain property for every disjoint root-list
system with nonzero coefficients and at least one selected root per
equation. No coefficient height or smoothness is used in this step.

Finally the image algebra of the sum-of-radicals map is defined as
R[sum_i sqrt(f_i)] and identified with the literal range of polynomial
evaluation at that sum. Since the entire coordinate tower is a finite
R-module, it is a finite module over this actual image algebra. The
radical sum is also proved integral over R. This establishes the
algebraic finiteness of the affine projection; its birationality is
NOT yet proved. The generic primitive-element argument, Krull and
projective dimensions and degrees, curve exclusions, surface covering
and all two-variable point estimates remain open.

These are exact internal algebraic parts of the source proof, with
no new improvement identifier. T1.7 stays in_progress, coverage stays
79/167 and improvements stay 104. No surface-counting estimate is
treated as proved, no new external input or dependency download is
introduced, and the original sources and Palomar status are unchanged.

Verified with Lean v4.36.0-rc2: full lake build (11351 jobs), actual Audit.lean kernel-axiom audit (7767 declarations; only propext, Classical.choice, Quot.sound), all 5484 ledger references, source integrity (138 manifest entries / 167 numbered results), and git diff --check. Ubuntu root free space: 14.43 GiB.


## The actual primitive radical sum and the birational affine projection

The radical-sum projection in Step 1 of companion T1.7 is now
proved birational in its literal algebraic sense. The inclusion of the
actual image algebra R[sum_i sqrt(f_i)] into the actual coordinate
tower induces a ring isomorphism of their fraction fields. The
isomorphism is proved to send every image-algebra element to that
same element in the source fraction field. Combined with the
previous finite-module theorem, this verifies the finiteness and
birationality of the actual affine projection.

First, each radical generator is identified with a distinct vector
of the explicit binary tower basis, proving their linear independence
over any commutative base ring. Every actual choice of radical signs
defines an algebra endomorphism by the already checked universal
property. Its square is the identity, so an actual sign automorphism
is constructed. In characteristic zero the sums for the 2^k sign
choices are pairwise distinct. Every such sum is a root of the
original sum's mapped minimal polynomial. The root count forces
degree at least 2^k; the tower dimension bounds it from above. The
minimal polynomial therefore has degree exactly 2^k, and its power
basis proves K[sum_i sqrt(f_i)] is the entire generic tower. The
independence hypothesis is discharged internally for the actual
generic split-radical family.

The recursive base-change map is proved to preserve the literal
radical sum. A general fraction-field lemma then identifies the
generic field as a fraction field of both the coordinate algebra
and its actual projection image: the subfield generated by the
base ring's image contains its fraction field K, and contains the
generic primitive sum, hence the whole generic extension. This
uses the actual injected ring maps and proves the extension on
every original element. It does not merely identify abstract
fields of the same degree or assume birationality as an input.

For the source system these statements hold over every characteristic-
zero field F, including an algebraic closure, for pairwise disjoint
integer root lists, nonzero coefficients and at least one selected
root per equation. Together with the previously proved coordinate
domain, free rank and universal point property, this completes the
algebraic integrality and finite birational projection assertions of
Step 1. The projective degree bounds on the image, Krull and
projective geometry, curve exclusions, surface coverings and the
two-variable host counts remain open. In particular the degree
2^k of the generic minimal polynomial is not yet counted as a proof
of the source projective-degree assertion.

These are internal proofs of the source algebra, with no new
mathematical-improvement identifier. T1.7 stays in_progress, coverage
stays 79/167 and confirmed improvements stay 104. No unproved
counting estimate, dependency download, original-source modification
or Palomar registration is introduced.

Verified with Lean v4.36.0-rc2: full lake build (11365 jobs), actual Audit.lean kernel-axiom audit (7793 declarations; only propext, Classical.choice, Quot.sound), all 5510 ledger references, source integrity (138 manifest entries / 167 numbered results), and git diff --check. Ubuntu root free space: 14.42 GiB.


## P1-MATH-0105 — A monic equation and a free power basis for the actual affine image

The actual affine image in companion T1.7 now has its literal
monic irreducible equation and an explicit free power basis over the
base polynomial ring. Write R=F[X,Y], A for the actual quadratic
tower and s for the sum of its k radical generators. The actual
minimal polynomial P in R[Z] is monic, has Z-degree exactly 2^k,
and generates the full kernel of evaluation Z->s. The quotient
R[Z]/(P) is identified with the actual image subalgebra R[s], with
the isomorphism proved on every polynomial. Thus this is a
presentation of the image, rather than a polynomial merely
vanishing on a collection of source points.

The general argument works over any domain R with a characteristic-
zero fraction field K for which the actual mapped radicands are
independent. Every nonzero annihilating polynomial over R has
Z-degree at least 2^k. The finite free coordinate tower bounds the
minimal polynomial degree from above. Its coefficient map to K is
the actual generic minimal polynomial. Monic division then reflects
divisibility from K[Z] to R[Z] and proves the complete kernel
identity. No integral-closedness hypothesis on R is needed.

Transporting the actual quotient's power basis gives
  R[s] free and finite over R, of rank 2^k,
  with actual basis 1,s,...,s^(2^k-1).
This strengthens the source's description of the affine image and
is recorded as P1-MATH-0105. The freeness concerns the image as an
algebra over the plane; the finite birational map from A to its
image is a different morphism. All coefficients remain arbitrary
nonzero constants, and no height or smoothness premise is used
for this algebraic assertion.

A concrete algebra equivalence transports the nested polynomial
to Mathlib's MvPolynomial (Fin 3) F. Its coordinate 0 is Z, 1 is Y
and 2 is X; the variable images and literal evaluation are checked.
The transported equation is irreducible and its actual totalDegree
is at least 2^k. Every actual solution of the original split
equations maps to its zero at (sum w_i,Y,X). The point statement
is obtained from the already proved unique source ring map, not
from an assumed point-count or geometric correspondence.

Finally the monic projection equation is proved to commute with
arbitrary base changes that retain the actual generic independence.
For every characteristic-zero field extension the actual scaled
split polynomials, root-list system and projection equation all
commute with the literal coefficient maps. The original image
equation therefore remains irreducible after every such extension,
including passage to an algebraic closure. This verifies the
coefficient compatibility needed for geometric irreducibility.

The uniform upper bound on the defining total degree, projective
closure and degree formulas, curve exclusions, surface coverings
and two-variable host estimates remain open. The totalDegree
lower bound proved here is not a completed projective intersection-
theoretic degree argument. T1.7 stays in_progress and numbered
coverage stays 79/167. Confirmed improvements total 105; no error
in a manuscript conclusion is asserted. No external counting
input, dependency download, source-byte change or Palomar
registration is introduced.

Verified with Lean v4.36.0-rc2: full lake build (11379 jobs), actual Audit.lean kernel-axiom audit (7836 declarations; only propext, Classical.choice, Quot.sound), all 5553 ledger references, source integrity (138 manifest entries / 167 numbered results), and git diff --check. Ubuntu root free space: 14.40 GiB.


## A universal integer equation and the coefficient-uniform image-degree bound

The actual defining polynomial of the split-radical image now
has both degree bounds needed in Step 1 of companion T1.7:
  2^k <= totalDegree(H) <= C(k)*max(1,K),
where each equation's two root lists have total size at most K.
The natural constant C(k) is defined as the actual total degree of
one fixed integer-coefficient universal polynomial. It depends only
on k, independently of the coefficient values, their heights,
smoothness, the selected integer roots, and the base field. This
also makes the upper dependence on the root-list degree linear.
The lower bound and the exact image presentation are the ones
already verified in the preceding checkpoint.

The proof constructs a literal tower over Z[T_1,...,T_k] and takes
the actual minimal polynomial of the sum of its formal radicals.
It is monic and has degree in Z at most 2^k by the already proved
finite free tower. Mapping T_i to the actual radicands specializes
this SAME polynomial to the actual image equation whenever the
target generic radicands are independent. The earlier base-change
theorem requires only independence in the target, so no unproved
generic square-class assertion about these universal parameters
is needed. The parameter-list map and every coefficient homomorphism
are checked on the actual rings.

The universal equation is transported to a multivariable polynomial
over Z, with one variable for the radical sum and k for the
radicands. Its literal evaluation in MvPolynomial (Fin 3) F is
proved equal to the actual image equation. A general support-sum
argument bounds the total degree of polynomial substitution by
the original total degree times the maximum substituend degree.
Each actual split radicand has lifted total degree at most its
two root-list sizes, and the sum variable has degree one. This
gives the displayed bound with no coefficient-height dependence
and no elimination or geometric estimate supplied as an input.

This extends P1-MATH-0105 with the fixed universal equation and
the linear-in-K degree bound. Its earlier free-power-basis finding
and validation are preserved in the history. Confirmed improvement
count remains 105, numbered coverage remains 79/167 and T1.7 stays
in_progress. The remaining work includes identification of the
projective closure's intersection-theoretic degree, the weighted
embedding and curve-degree formulas, surface coverings, curve
exclusions, and the actual two-variable host counts. No completed
projective or counting claim is inferred just from a total-degree
inequality. No external input, dependency download, original-source
change or Palomar registration is introduced.

Verified with Lean v4.36.0-rc2: full lake build (11387 jobs), actual Audit.lean kernel-axiom audit (7856 declarations; only propext, Classical.choice, Quot.sound), all 5573 ledger references, source integrity (138 manifest entries / 167 numbered results), and git diff --check. Ubuntu root free space: 14.39 GiB.


## The actual radical, Veronese-chart and projection point heights

The actual point-height assertion in Step 2 of companion T1.7
is now proved from the literal integer equations. If |X|,|Y|<=2N,
the selected offsets have absolute value at most N, each pair of
root lists has total size at most K, and |c_i|<=N^A, every actual
integer solution of
  w_i^2=c_i*product_(a in I_i)(X+a)*product_(b in J_i)(Y+b)
satisfies |w_i|<=3^K*N^D whenever A+K<=2D. Here the finite radical
bound allows real D; the common-coordinate theorem takes an integer
D for the monomial degrees. It retains signed coefficients, all
integer X,Y, zero factors and zero radicals.

For k equations a single positive constant
  C(k,K,D)=2^D+(k+1)*3^K
bounds the absolute values of every actual affine monomial X^aY^b
with a+b<=D, every w_i and their literal sum by C(k,K,D)*N^D.
These are precisely the affine coordinates underlying the weighted
Veronese chart at Z=1, together with the radical-sum projection.
The integers remain actual integer coordinates; no presumed geometric
height or abstract bounding-box hypothesis is substituted for them.

The finite proof first bounds the natural absolute value of each
integer split product and squares the actual radical equation.
Real power monotonicity converts the coefficient-height exponent
to the required D, and the triangle inequality controls the sum.
The monomial bound is proved separately on the actual integer powers.
An eventual version then handles offset bounds b*(log N)^r for
arbitrary fixed b,r: one threshold precedes every coefficient family,
root-list system, point and radical solution. In particular it covers
the logarithmic offsets in the source with the asserted uniformity.

This verifies the elementary height component of Step 2, while the
construction of the projective embedding and its degree and curve-degree
identities remain open. The curve exclusions, surface coverings and
two-variable host counts also remain open. T1.7 stays in_progress,
coverage stays 79/167 and confirmed improvements stay 105; no new
improvement identifier is assigned to this checked source height
calculation. No external estimate, dependency download, original
source edit or Palomar registration is introduced.

Verified with Lean v4.36.0-rc2: full lake build (11393 jobs), actual Audit.lean kernel-axiom audit (7866 declarations; only propext, Classical.choice, Quot.sound), all 5583 ledger references, source integrity (138 manifest entries / 167 numbered results), and git diff --check. Ubuntu root free space: 14.38 GiB.


## The actual selected-value obstruction on rational lines

The functional-square obstruction on affine rational lines in
Step 3 of companion T1.7 is now proved for the actual finite sets of
selected positive values. It uses their literal even-selection maps
and square-class spaces, rather than requiring independence of the
larger full windows. Two equations with disjoint nonempty first root
lists already suffice. The second selected set's even-selection map
need not be injective; the two actual even image spaces must remain
in direct sum. Coefficients are arbitrary nonzero rational constants.

The polynomial proof is explicit. A square polynomial has zero
derivative at each root. If a product c*P*Q is square, c!=0 and P
is separable, every root of P must therefore be a root of Q.
Applying this to the literal restriction Y=alpha*X+beta of each
scaled split equation forces every first-list root to match an
actual second-list root. Squares in the actual rational-function
field are reflected to the integrally closed polynomial ring before
this argument is applied. No root-matching statement is assumed.

The selected-value arithmetic is proved on arbitrary finite positive
integer sets S,T. Two distinct elements of S and a proportional pair
in T give the same nonzero even square class in both actual spaces.
Injectivity of the first even map makes that class nonzero, and
directness gives the contradiction. The positive offset values are
identified with their actual natural absolute values and rational
casts. Two disjoint equations supply the required distinct pair.
This includes horizontal slopes alpha=0; swapping the coordinates
also proves the vertical-line functional-square obstruction.

The result is connected to the actual split-radical coordinate
algebra. The literal polynomial map substituting a rational line
is checked on each scaled split radicand. Any ring homomorphism
from the actual coordinate tower to Q(T) agreeing with that line
map on Q[X,Y] would turn every actual radical-square relation into
the forbidden functional squares. Its nonexistence is proved, so
the obstruction is not left as an unexplained square-condition input.

This extends the one-sided arithmetic refinement P1-MATH-0019 to
selected sets and the line step of T1.7. Its earlier complete T20.5
validation is preserved in the finding history. No independence
weakening is claimed for the entire two-variable host-count lemma.
The geometric step identifying a curve of minimal projective degree
with a degree-one function-field map to a line remains open, as do
the weighted projective degree formulas, surface coverings and final
two-variable counts. T1.7 stays in_progress, coverage stays 79/167
and confirmed improvements stay 105. No external estimate, dependency
download, source-byte modification or Palomar registration is introduced.

Verified with Lean v4.36.0-rc2: full lake build (11401 jobs), actual Audit.lean kernel-axiom audit (7882 declarations; only propext, Classical.choice, Quot.sound), all 5599 ledger references, source integrity (138 manifest entries / 167 numbered results), and git diff --check. Ubuntu root free space: 14.37 GiB.


## The literal homogenized split-radical coordinate domain

The underlying coordinate algebra of the actual homogenized
split-radical presentation in Step 2 of companion T1.7 is now proved
to be a domain. Over every characteristic-zero field F, take the
literal polynomial ring F[Z][X][Y] and actual radicands
  c_i*Z^(e_i)*product_(a in I_i)(X+a*Z)*product_(b in J_i)(Y+b*Z).
The coefficients c_i are arbitrary nonzero elements, the integer
root lists are pairwise disjoint in each coordinate, and at least
one list in each equation is nonempty. The literal quadratic tower
is finite free of rank 2^k over this three-variable base. Its domain
property is proved internally for arbitrary natural e_i, and hence
includes the source exponents e_i=2D-|I_i|-|J_i|. No point-height
or coefficient-smoothness premise enters this algebraic assertion.

The proof first extends the nonsquare split-word lemmas from integer
roots to arbitrary finite sets of distinct field roots. These
supporting nonsquare and finite-product independence statements hold
over any field; the subsequent actual quadratic-field construction
uses characteristic zero as before. Nonempty disjoint selections
have nonsquare product, and their actual generic tower is proved
to be a field of degree 2^k. No Kummer or field-degree assertion
is assumed as an input.

For the homogenized system, an explicit injective coefficient map
F[Z]->F(Z) is lifted through both polynomial coordinates. If z is
the actual nonzero fraction-field image of Z, the source root lists
become the literal finite sets {a*z:a in I_i} and {b*z:b in J_i}.
Their disjointness is proved using the injectivity of a->a*z in
characteristic zero. The mapped coefficient is c_i*z^(e_i), proved
nonzero. Every actual radicand and the complete equation list are
proved to map to these exact scaled root words. Passing to the
fraction field F(Z)(X,Y) gives the internally constructed generic
field. The recursive tower base-change map is faithful, proving
that the original homogenized coordinate algebra is a domain.

This provides the literal integral algebra underlying the source
weighted presentation, including over an algebraically closed base.
The formal grading, the explicit Z=1 specialization, generation of
the D-th Veronese algebra, the projective embedding and cover-degree
and curve-degree identities remain open. The surface coverings and
two-variable host counts also remain open. T1.7 stays in_progress,
numbered coverage stays 79/167 and confirmed improvements stay 105.
These are checked source-algebra foundations with no new improvement
identifier. No external input, dependency download, original-source
change or Palomar registration is introduced.

Verified with Lean v4.36.0-rc2: full lake build (11409 jobs), actual Audit.lean kernel-axiom audit (7911 declarations; only propext, Classical.choice, Quot.sound), all 5628 ledger references, source integrity (138 manifest entries / 167 numbered results), and git diff --check. Ubuntu root free space: 14.36 GiB.


## The literal weighted presentation, homogeneous relations and Z=1 chart

The literal weighted polynomial quotient in Step 2 of T1.7 is
now identified with the already constructed homogenized radical
coordinate algebra. This is an explicit ring equivalence, rather
than an identification of informal presentations. The actual
quotient by W_i^2-c_i*Z^(2D-|I_i|-|J_i|)*product(X+aZ)*product(Y+bZ)
is consequently proved to be a domain over every characteristic-zero
field, under the source nonzero-coefficient, nonempty and disjoint
root-list hypotheses. No integrality premise is left in this source
corollary.

A general presentation theorem first constructs inverse algebra maps
between R[W_1,...,W_k]/(W_i^2-a_i) and the literal quadratic tower,
for every commutative ring R and every radicand list, including the
empty list. The maps preserve every radical generator. The kernel
of the actual polynomial evaluation is proved to be exactly the
relation ideal. The weighted presentation is transported to this
general quotient through the actual variable-sum equivalence and
the checked three-variable polynomial equivalence. Every generator
and every actual source relation is tracked through those maps.

In the native three-variable polynomial ring, the homogenized
radicands are proved homogeneous of degree 2D whenever their root
count is at most 2D. Nonzero coefficients give nonzero radicands and
exact total degree 2D; these polynomial statements hold over every
field, without a characteristic-zero assumption. The actual weighted
relations, with base-variable weights 1 and radical-variable weight
D, are proved weighted homogeneous of degree 2D. Their literal span
ideal is homogeneous for the native weighted polynomial grading.

The Z=1 coefficient evaluation, lifted through both polynomial
coordinates, sends each actual homogenized radicand and the entire
list to the previously checked affine system. The recursive base
change supplies an actual ring homomorphism between the corresponding
coordinate algebras, commuting with this base evaluation.

The induced quotient grading as a bundled graded algebra, generation
of its D-th Veronese algebra, the projective construction and its
cover- and curve-degree formulas remain open. This checkpoint does
not infer projective degree formulas from the affine polynomial
identities. The external surface covering and the two-variable host
counts also remain open. T1.7 stays in_progress, numbered coverage
stays 79/167, and confirmed improvements stay 105. These are checked
source-algebra foundations with no new improvement identifier. No
external estimate, new dependency, original manuscript change or
Palomar registration is introduced.

Verified with Lean v4.36.0-rc2: targeted builds and full lake build (11419 jobs), actual 7955-declaration axiom audit, all 5672 ledger/finding declaration references, 138 preserved source-manifest entries and the complete 167-result inventory. Only propext, Classical.choice and Quot.sound occur. Ubuntu root free space: 14.34 GiB. Numbered coverage remains 79/167; confirmed improvements remain 105.


## The actual quotient grading and precise Veronese generators

The literal weighted quotient in T1.7 Step 2 now carries a
constructed GradedAlgebra structure. Weighted homogeneous polynomial
components descend through the actual homogeneous relation ideal as
linear projections on the quotient. On each actual image piece,
projection to its own degree is the identity and projection to every
other degree is zero. These projections prove injectivity of the
canonical direct-sum recomposition; polynomial decomposition proves
surjectivity. Multiplication and the unit respect the actual pieces.
This is a proved quotient grading, not a grading asserted from the
notation. The general construction works over every commutative
coefficient ring and every homogeneous weighted polynomial ideal.

For the source quotient, the actual base variables have degree 1 and
the actual radical variables have degree D, with their literal
projection formulas checked. For positive D its degree-zero piece
is exactly the scalar image. The root-count bound at most 2D supplies
the previously proved homogeneity of the source relation ideal.

The D-th Veronese algebra is defined as the actual range of the
canonical algebra map from the direct sum of pieces of degrees nD.
Its underlying module is proved to be the supremum of these actual
pieces. It equals the subalgebra generated by those pieces, and is
now proved generated by the single piece of degree D. The argument
splits actual finitely supported exponent vectors of weights 1 or
D into successive vectors of weight D, proves the monomial image
statement and then sums homogeneous polynomials. It applies through
every algebra map, including the actual quotient map; no Veronese
generation assertion is supplied as an input.

The precise source generator set is also proved: the base monomials
of ordinary degree D with every radical exponent zero, together
with the individual radical variables. Every weight-D monomial with
a radical factor is proved to be that single radical times a scalar;
all remaining monomials are the stated pure base monomials. Their
images generate the actual source Veronese algebra. For finitely many
radicals the generator set is finite and the Veronese algebra is
proved of finite type. Under the actual characteristic-zero source
root-list hypotheses, its domain property is discharged internally
using the previous literal quotient-domain theorem.

This completes the source-algebra grading and Veronese-generation
steps. The projective construction, finiteness over the projective
plane, its cover degree and the surface- and curve-degree identities
remain open. No projective degree formula is inferred solely from
this algebraic generation result. The external surface covering and
the two-variable host counts remain open. T1.7 stays in_progress,
numbered coverage stays 79/167 and confirmed improvements stay 105.
No new improvement identifier, external estimate, dependency download,
original manuscript change or Palomar registration is introduced.

Verified with Lean v4.36.0-rc2: targeted builds and full lake build (11431 jobs), actual 7993-declaration axiom audit, all 5710 ledger/finding declaration references, 138 preserved source-manifest entries and the complete 167-result inventory. Only propext, Classical.choice and Quot.sound occur. Ubuntu root free space: 14.33 GiB. Numbered coverage remains 79/167; confirmed improvements remain 105.


## The finite inclusion over the pure base Veronese image

The actual inclusion of the pure base Veronese image into the
source Veronese algebra is now proved to be a finite ring map.
The base image is the subalgebra of the literal weighted quotient
generated by the images of the degree-D monomials in the three base
variables. The target is the actual Veronese algebra constructed as
the range of the direct sum of its multiple-degree pieces. The map
is the literal inclusion of these subalgebras.

Native homogeneous polynomials of every degree nD in the three base
variables are proved to map into that pure base algebra, using the
already checked exponent splitting and the explicit coefficient and
monomial maps. In particular every actual source homogenized
radicand, of degree 2D, belongs to the base image. This membership is
proved for the exact c_i*Z^(2D-|I_i|-|J_i|) split products, rather
than supplied as an abstract integrality premise.

Each actual quotient radical is packaged as an element of the target
Veronese algebra. Its square is proved equal to the actual radicand
image using membership of the literal defining relation in the
literal relation ideal. The target is proved to be generated by the
base image and these radicals. A general checked finite-inclusion
lemma constructs the canonical relative algebra, proves every such
radical integral by its monic quadratic relation, verifies that its
adjoin is the entire target and proves module finiteness. Applying
that lemma discharges every premise with the actual source objects.

This finite-map statement holds over every field, for finitely many
equations, positive D and root counts at most 2D. It needs no
nonzero-coefficient, characteristic-zero or disjointness hypothesis;
those separate hypotheses already prove integrality of the source
Veronese algebra. Finiteness here concerns the affine Veronese cone
inclusion. The identification of the pure base image with the
standard plane Veronese algebra, the relative free rank and cover
degree 2^k, the projective finite morphism and all projective degree
formulas remain open. The external surface covering and two-variable
host counts remain open. T1.7 stays in_progress, numbered coverage
stays 79/167 and confirmed improvements stay 105. No new improvement
identifier, external estimate, dependency download, original-source
change or Palomar registration is introduced.

Verified with Lean v4.36.0-rc2: targeted builds and full lake build (11437 jobs), actual 8004-declaration axiom audit, all 5721 ledger/finding declaration references, 138 preserved source-manifest entries and the complete 167-result inventory. Only propext, Classical.choice and Quot.sound occur. Ubuntu root free space: 14.32 GiB. Numbered coverage remains 79/167; confirmed improvements remain 105.


## The faithful finite map from the standard base Veronese algebra

The pure base algebra in T1.7 Step 2 is now identified by an
explicit F-algebra equivalence with the standard D-th Veronese
algebra of the native polynomial ring F[X,Y,Z]. This standard algebra
is defined as the actual range of the direct sum of the ordinary
homogeneous pieces of degrees nD, not as a polynomial ring assumed
to represent the base.

The coded pure base monomials in the full weighted variable set are
proved to be exactly the images, under the literal base-variable
rename, of ordinary degree-D monomials in three variables. The reverse
identification constructs the actual exponent preimage and proves
that its image is the original exponent vector using the vanishing
of all radical exponents. Native homogeneous degree-D polynomials
and the standard Veronese algebra have these exact generators.
Mapping them through the actual quotient gives precisely the pure
base image used in the finite-inclusion checkpoint.

The complete native three-variable polynomial map into the literal
weighted quotient is proved injective. Under the explicit weighted
presentation equivalence, its value on every polynomial is the
canonical base image of that polynomial under the checked
three-variable equivalence into the actual radical tower. The base
map into this tower is injective even for arbitrary radicands. Thus
the base injectivity uses no domain assertion and no square-class
independence premise. Restriction to the standard Veronese algebra
gives the stated explicit base equivalence and its value formula.

Composing this equivalence with the already verified pure-base
inclusion constructs the actual standard-base-to-source-Veronese
ring map. Its injectivity and finiteness are proved. These results
hold over every field for the exact indexed source system; positive
D and the source root-count bound supply the finite-map assertion.
No nonzero-coefficient, characteristic-zero or disjointness premise
is needed for this finite faithful base map. The separate source
integrality theorem retains its own exact hypotheses.

The relative free rank and generic cover degree 2^k, the projective
finite morphism, the identification of the base projective scheme
with the projective plane, and all projective degree formulas remain
open. This checkpoint identifies and proves the actual affine-cone
base map; it does not infer those projective conclusions from ring
finiteness alone. The external surface covering and two-variable
host counts remain open. T1.7 stays in_progress, numbered coverage
stays 79/167 and confirmed improvements stay 105. No new improvement
identifier, external estimate, dependency download, original-source
change or Palomar registration is introduced.

Verified with Lean v4.36.0-rc2: targeted builds and full lake build (11441 jobs), actual 8015-declaration axiom audit, all 5732 ledger/finding declaration references, 138 preserved source-manifest entries and the complete 167-result inventory. Only propext, Classical.choice and Quot.sound occur. Ubuntu root free space: 14.31 GiB. Numbered coverage remains 79/167; confirmed improvements remain 105.


## P1-MATH-0106 — An actual relative free basis of the source Veronese algebra

The actual source D-th Veronese algebra is now proved finite
free of rank 2^k over the standard three-variable D-th Veronese
base. A literal basis is constructed and its value in the weighted
quotient is checked on every basis index. This strengthens the
finite-base-map result and is recorded as P1-MATH-0106. It concerns
the source Veronese algebra; P1-MATH-0105 concerns the different
radical-sum affine image algebra.

Each actual homogenized radicand has ordinary degree 2D and is
constructed as an element of the standard Veronese base. The literal
quadratic tower over that base is free of rank 2^k by its recursive
normal basis. Its coefficient inclusion into the full three-variable
polynomial ring is proved injective, and each actual radicand and
the complete equation list are proved to map to their exact original
homogenized polynomials. The faithful tower base change is followed
by literal list transport and the explicit weighted presentation
equivalence, giving an actual injective map into the source quotient.

Every radical generator, every normal basis vector and the base
inclusion are proved to commute with the actual base change. The
relative map sends its generators to the exact source quotient
radicals, with all list indices tracked. Its image as a base algebra,
after restricting scalars, is proved to be exactly the source
Veronese algebra: the scalar range is the previously identified pure
base image and the generator range is the actual radical range.
The exact source generation theorem supplies both inclusions.

The image basis is transported through this proved image equality
to the actual source Veronese algebra. Its module structure is the
one induced by the previously constructed standard-base ring map,
and the scalar compatibility is checked explicitly. The resulting
basis, freeness, module finiteness and exact rank 2^k are internal
Lean conclusions. No freeness, image equality, degree or counting
assertion is supplied as an assumption.

The finite-free statement holds over every field and for arbitrary
coefficients, including zero coefficients, whenever D is positive
and every root count is at most 2D. It does not require characteristic
zero, disjointness, nonempty root sets or generic square-class
independence. Those hypotheses remain separate inputs to the already
proved integrality statement. The general basis and faithful-map
lemmas work for arbitrary commutative coefficient rings, with
nontriviality where needed for finrank.

This supplies the exact relative algebraic free rank underlying
Step 2. The projective construction, the base projective-scheme
identification, the degree-zero function-field bridge, the projective
cover degree and all surface- and curve-degree formulas remain open.
No projective conclusion is inferred solely from this affine-cone
module computation. External surface coverings and two-variable
host counts remain open. T1.7 stays in_progress and numbered coverage
stays 79/167. Confirmed improvements total 106; no manuscript
conclusion error is asserted. No external estimate, dependency
download, original-source change or Palomar registration is introduced.

Verified with Lean v4.36.0-rc2: targeted builds and full lake build (11455 jobs), actual 8044-declaration axiom audit, all 5761 ledger/finding declaration references, 138 preserved source-manifest entries and the complete 167-result inventory. Only propext, Classical.choice and Quot.sound occur. Ubuntu root free space: 14.29 GiB. Numbered coverage remains 79/167; confirmed improvements total 106.


## P1-MATH-0106 extended — The actual rescaled grading, homogeneous basis and graded base map

Both actual Veronese algebras now carry the grading in which
original degree nD becomes degree n. The construction is made on
their literal direct-sum range algebras, with degree-n piece equal
to the preimage of the original degree-nD piece. Original homogeneous
projections lift to actual linear projections on the Veronese
algebra. For positive D their action on each image piece is the
identity in its own degree and zero in every other degree.
Injectivity and surjectivity of recomposition are proved, followed
by the actual GradedAlgebra structure and its projection formula.

For the standard three-variable base and the literal source weighted
quotient, generation in degree D is transported to generation of
these actual rescaled rings by their degree-one pieces. Every exact
source generator, including each radical, is proved to belong to
degree one. The source degree-zero piece is exactly its scalar image.
The source quotient grading uses the source root-count bound; the
rescaling uses positive D. No generation or decomposition assertion
is assumed as an unproved interface.

The free normal basis of P1-MATH-0106 is now proved homogeneous. A
recursive index weight counts the selected radicals and is proved
at most k. For any actual ring map from a quadratic tower to a
graded ring, homogeneous radical images of degree D imply that the
image of each literal normal basis vector has degree D times its
index weight. Applying this statement to the exact relative map,
using its checked generator formulas, proves that the actual source
basis vector belongs to rescaled degree equal to that weight, with
all weights between 0 and k. This is a statement about the already
constructed source basis, not a new basis assumed homogeneous.

Finally the actual finite faithful standard-base map is proved to
preserve every rescaled degree and is bundled as a GradedRingHom.
The proof transports every ordinary homogeneous native base
polynomial through the literal variable rename into the weighted
polynomial grading, and then through the actual quotient map. The
bundled graded map retains the previously verified injectivity and
finiteness properties. These results extend P1-MATH-0106 without a
new improvement identifier.

The Hilbert-function computation, projective construction and its
degree-zero function-field bridge, finite projective cover degree
and all surface- and curve-degree identities remain open. The
external surface covering and two-variable host counts remain open.
T1.7 stays in_progress, numbered coverage stays 79/167 and confirmed
improvements stay 106. No external estimate, dependency download,
original-source change or Palomar registration is introduced.

Verified with Lean v4.36.0-rc2: targeted builds and full lake build (11469 jobs), actual 8070-declaration axiom audit, all 5787 ledger/finding declaration references, 138 preserved source-manifest entries and the complete 167-result inventory. Only propext, Classical.choice and Quot.sound occur. Ubuntu root free space: 14.28 GiB. Numbered coverage remains 79/167; confirmed improvements remain 106.


## Actual projective scheme map

The actual rescaled standard-base inclusion now induces a constructed
morphism of schemes from the source Proj to the native standard
Veronese Proj. Its inverse image of every base basic open D(b) is
exactly the source basic open D(f(b)). This construction uses the
literal graded inclusion and the actual source quotient, rather
than an assumed projective model.

The admissibility criterion is proved: the source irrelevant ideal
is contained in the radical of the mapped base irrelevant ideal.
The source generators are proved to generate their actual ring;
the irrelevant ideal of a ring generated in degree one is proved
to be their ideal span. Each pure base generator lies in the mapped
base irrelevant ideal, while the square of each radical generator
lies there by its actual homogeneous radicand relation. These
arguments apply over every field, including zero radicand
coefficients, for positive D and root counts at most 2D.

The pinned Mathlib Proj functor takes the stronger condition
H_plus <= map(G_plus). The quadratic source supplies the sufficient
radical containment above. A local extension implements the point
map, its continuity, the structure-sheaf map and its locality on
stalks under that weaker condition, and bundles the resulting
Scheme.Hom. This is a library interface extension, not an error
in the manuscript or a new mathematical-change identifier.

Finiteness of the scheme morphism, identification of the base Proj
with the projective plane, the degree-zero function-field bridge,
the degree 2^k of the projective cover, surface degree 2^k D^2,
curve-degree identities and the external surface covering and
host counts remain open. T1.7 stays in_progress, numbered coverage
stays 79/167 and confirmed mathematical improvements stay 106.
No original manuscript source is changed. Palomar remains deferred.

See [statement alignment and upstream provenance](PROJECTIVE_MAP_ALIGNMENT.md).

Verified with Lean v4.36.0-rc2: full build 11821 jobs, direct axiom audit of 8089 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 5799 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 13.95 GiB.


## P1-MATH-0106 extended — Finiteness of the actual projective morphism

The constructed projective source morphism is now proved finite
as a morphism of schemes. This is the literal map from the source
Veronese Proj to the standard native Veronese Proj, not merely the
already verified finite map of affine cones. The theorem applies
over every field for arbitrary coefficients, positive D and root
counts at most 2D. Characteristic zero and root independence are
not required for finiteness.

For any nonnegatively graded commutative ring and any homogeneous
element b of degree one, a ring homomorphism to its degree-zero
homogeneous localization is constructed by sending each degree-n
component a to a/b^n. Compatibility with addition, multiplication
and one is proved, followed by its formula on homogeneous
elements, surjectivity and naturality for actual graded ring maps.
Surjectivity and naturality transport a finite total ring map to
a finite map of these actual chart rings, including degenerate
charts, without a nonzero or domain assumption.

The radical-admissible projective morphism is proved to restrict on
each degree-one basic open to the corresponding Spec map, under
the actual chart isomorphisms. Finiteness of that ring map proves
finiteness of each restricted scheme map. Degree-one base opens
cover the entire target by the proved irrelevant-ideal span
identity and generation in degree one. Zariski locality then
proves finiteness of the actual global projective morphism.

This extends the argument supporting P1-MATH-0106; no new
mathematical-change identifier is introduced. The cover's generic
degree, identification of the base Proj with the projective plane,
the degree-zero function-field bridge, the Hilbert calculation,
surface degree 2^k D^2, curve-degree identities and external host
counts remain open. T1.7 stays in_progress, coverage stays 79/167,
confirmed improvements stay 106 and Palomar remains deferred.

Verified with Lean v4.36.0-rc2: full build 12009 jobs, direct axiom audit of 8103 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 5813 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 13.78 GiB.


## P1-MATH-0106 extended — The actual finite flat cover has constant rank 2^k

The actual projective source morphism is now proved finite,
flat, surjective and of constant scheme rank 2^k. The rank statement
is the equality of Mathlib's Scheme.Hom.finrank with 2^k at every
point of the actual native Veronese Proj. It applies over every
field, to arbitrary coefficients including zero, for positive D
and source root counts at most 2D. In particular the geometric
flatness and constant-rank assertions do not require generic
square-class independence or characteristic zero.

The degree-one dehomogenization map has proved kernel generated
by b-1, and gives an actual ring equivalence from that quotient to
the homogeneous localization. The proof constructs the inverse
evaluation using the ordinary localization, where b maps to one.
A literal ring basis is transported to the quotient by tensor
base change, then through the constructed ring equivalences and
coefficient transport. This proves that a free graded ring map
has an actual free map on each degree-one chart, with basis the
dehomogenized original basis. Homogeneity of the original basis
is used for the explicit fraction formula, not assumed for the
base-change basis argument itself.

For the source, the exact chart basis vector is the previously
constructed normal basis vector divided by f(b) to its explicit
radical-count weight. Every nonzero native chart is a domain and
the actual source chart module is finite free of rank 2^k. The
base and source actions are the actual homogeneous-localization
map, not auxiliary actions assumed compatible.

The actual projective map is flat by those chart bases and Zariski
locality. Each chart square is proved to be a pullback. Mathlib's
finite-flat scheme rank is then computed on that pullback from
the literal chart basis. The proved degree-one target cover gives
constant rank everywhere, and its positive value proves
surjectivity. This establishes the projective cover rank, not
only the rank of its affine cone.

This extends P1-MATH-0106 without a new identifier. The geometric
base is still the actual standard Veronese Proj; its explicit
identification with the projective plane remains open. The
degree-zero function-field bridge and its identification with
the manuscript's generic field, Hilbert computation, surface
degree 2^k D^2, curve-degree identities and external host counts
remain open. The constant scheme rank does not replace those
separate alignment steps. T1.7 stays in_progress, numbered
coverage stays 79/167, confirmed improvements stay 106 and
Palomar remains deferred.

Verified with Lean v4.36.0-rc2: full build 12061 jobs, direct axiom audit of 8129 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 5839 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 13.71 GiB.


## Actual integral projective schemes and their function fields

The actual native base and the actual source projective schemes
are now proved integral under the source integrality hypotheses.
The base needs only a field and positive D. The source retains
characteristic zero, nonzero radicand coefficients, at least one
root in each equation and the exact pairwise disjoint root-set
hypotheses already used for its coordinate-domain proof. The
positive degree and root-count bounds supply its rescaled grading.
No domain or integrality assertion is assumed as a new interface.

For a graded domain, homogeneous localization at any submonoid
avoiding zero is proved a domain by its faithful embedding into
the ordinary localization. Every actual Proj stalk is consequently
a domain, and the scheme is reduced. If the irrelevant ideal is
nonzero, the literal zero homogeneous prime is constructed as a
point and proved generic. This proves irreducibility, nonemptiness
and integrality, and identifies the scheme's chosen generic point
with that zero prime.

The native coordinate powers X_j^D are constructed in the actual
standard Veronese algebra, with proved degree-one membership and
nonvanishing. The Z^D coordinate proves nonzero irrelevant ideals
for both the base and, by the faithful graded base inclusion, the
source. These facts discharge the nonempty-Proj hypotheses on the
literal algebras used for the projective cover.

The actual scheme function field is constructed as ring-equivalent
to the homogeneous localization at the zero ideal: fractions of
homogeneous numerators and nonzero denominators of the same degree.
The latter ring is proved a field. A faithful radical-admissible
graded map is proved to map the zero prime and generic point to
their actual counterparts. Its map of scheme function fields is
constructed directly from the scheme morphism's stalk map and
proved injective. The corresponding map on degree-zero homogeneous
fractions is also constructed. These constructions are instantiated
for the exact projective base inclusion of the source, retaining
all the stated source hypotheses.

The remaining alignment includes the compatibility of the two
function-field maps under these equivalences and identification
with the affine split-radical generic field in the manuscript.
The degree of that actual field extension is not yet certified by
the already proved constant scheme rank. The explicit base Proj
identification with the projective plane, Hilbert computation,
surface degree 2^k D^2, curve-degree identities and external host
counts remain open. T1.7 stays in_progress, coverage stays 79/167,
confirmed improvements stay 106 and Palomar remains deferred.

Verified with Lean v4.36.0-rc2: full build 12075 jobs, direct axiom audit of 8151 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 5867 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 13.69 GiB.


## Naturality of the actual projective function-field map

The map on actual scheme function fields is now proved compatible
with the map on actual degree-zero homogeneous fractions. The
function-field equivalences and the generic-point stalk map are
exposed as their categorical isomorphism and morphism, preserving
their previous ring types and constructions. Their commuting
diagram is a proved equality of actual ring homomorphisms.

The proof transports a scheme stalk map along proved equalities
of source and target points. A Proj stalk compatibility theorem
identifies it with the actual homogeneous local ring map after
that point transport. At the zero homogeneous primes, this is
exactly the degree-zero fraction map of the original graded ring
homomorphism. Applying the checked generic-point equalities gives
the categorical square and then the ring-homomorphism square.

For the paper's source, the separately constructed map induced by
the actual projective morphism is proved equal to the general
construction. The literal base and source function-field
equivalences then give the commuting diagram with the actual
graded base inclusion on homogeneous fractions. All source domain
and integrality hypotheses remain explicit and are discharged by
the previously proved source domain and nonempty-Proj results.

Thus the naturality part of the degree-zero function-field bridge
is complete. Identification with the manuscript's affine
split-radical generic tower and the numerical degree of this
actual field extension remain open. The explicit plane
identification, Hilbert computation, surface degree 2^k D^2,
curve-degree identities and external host counts also remain
open. T1.7 stays in_progress, coverage stays 79/167, confirmed
improvements stay 106 and Palomar remains deferred.

Verified with Lean v4.36.0-rc2: full build 12079 jobs, direct axiom audit of 8157 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 5876 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 13.68 GiB.


## The actual projective function-field extension has degree 2^k

The actual extension of projective scheme function fields is now
proved finite of degree 2^k. Its algebra structure is the actual
stalk-induced map of the constructed source projective morphism.
By the previously proved naturality diagram, the actual map of
degree-zero homogeneous fraction fields has the same degree 2^k.
This computes the numerical field degree, separately from the
already proved constant finite-flat scheme rank.

For a nonzero degree-one homogeneous element b, its basic open
is proved nonempty by the actual zero homogeneous prime. The
chart map to the scheme function field is constructed by the
canonical localization-to-sections map followed by the actual
germ at the generic point. The scheme function field is proved
to be the fraction field of that chart ring, by its existing
affine-open fraction-field theorem and the actual chart section
isomorphism. No abstract field identification is assumed.

Naturality of these chart maps is proved first for germs and the
generic-point stalk map and then for the actual homogeneous
localization maps. This supplies both scalar-tower identities.
The fraction-ring dimension theorem equates the actual
function-field degree with the rank of the actual chart module.
The literal free chart basis therefore computes that field degree.

For the paper's source, the chart is the nonzero native Z^D
coordinate. The source chart basis and its index-cardinality
formula discharge the rank calculation as 2^k. The actual
geometric field extension is explicitly proved module-finite.
The checked ring equivalences and commuting diagram transport
the numerical degree to the actual homogeneous fraction-field
map. All source integrality hypotheses remain explicit:
characteristic zero, nonzero coefficients, nonempty root data,
pairwise disjoint root sets, the literal homogenized radicand
identities, positive D and the root-count degree bound.

Identification of these fields with the manuscript's explicit
affine split-radical generic tower remains open. The base target
is still the native standard Veronese Proj; its explicit plane
identification, the Hilbert/intersection calculation of surface
degree 2^k D^2, curve-degree identities and external host counts
remain open. T1.7 stays in_progress, numbered coverage stays
79/167, confirmed improvements stay 106 and Palomar remains
deferred. Original manuscript sources are unchanged.

Verified with Lean v4.36.0-rc2: full build 12087 jobs, direct axiom audit of 8167 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 5888 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 13.67 GiB.


## P1-MATH-0107 — Exact Hilbert function, polynomial and multiplicity of the actual source

The actual source homogeneous pieces now have explicit coefficient-field
bases and exact dimensions. If e ranges over the literal quadratic
normal-basis indices, and |e| is its proved radical-count weight, then

    h_S(n) = sum_{|e| <= n} binom(D(n-|e|)+2,2).

Every homogeneous piece is finite dimensional. For n >= k all normal
indices occur. The rational polynomial

    P_S(T) = (1/2) sum_e (DT-D|e|+1)(DT-D|e|+2)

is proved to equal these actual dimensions for every n >= k. Its
quadratic coefficient is 2^k D^2/2; for positive D its degree is exactly
two and its Hilbert multiplicity is 2^k D^2. This last invariant is
constructed from the unique eventual polynomial of the actual graded
pieces, not supplied as a premise or defined to be the target value.

The proof first restricts actual homogeneous vector bases to components.
The native standard Veronese basis consists of literal monomials.
The scalar-preserving literal base inclusion then composes that vector
basis with the actual relative free quadratic basis. Its component
indices are explicitly reindexed by radical weight and polynomial
exponents. Exponents of degree m are identified with symmetric powers,
giving the proved monomial count binom(m+2,2). The native base pieces
accordingly have dimension binom(nD+2,2).

All these dimension and Hilbert identities hold over any coefficient
field, including positive characteristic and zero radicand coefficients,
under the literal radicand identities, positive D and degree bound.
The separate characteristic-zero, nonzero-coefficient and root-disjointness
hypotheses remain necessary in the existing source-integrality argument.
This gives an elementary Hilbert-function proof of the numerical surface
factor appearing in Step 2, and a stronger exact formula for a revision.

The invariant computed here is the Hilbert multiplicity of the actual
chosen graded presentation. A scheme-theoretic comparison with the
manuscript's explicit projective embedding and hyperplane bundle, the
native target's identification with the plane, the curve-degree
projection formula and the external surface/curve host counts remain
open. The explicit affine generic-tower identification is also still
open. T1.7 remains in_progress and numbered coverage remains 79/167.
Confirmed mathematical improvements now total 107; no manuscript
conclusion error has been confirmed. Palomar remains deferred.
Original manuscript sources are unchanged.

Verified with Lean v4.36.0-rc2: full build 12115 jobs, direct axiom audit of 8213 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 5949 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 13.64 GiB.


## Actual projective charts and function fields match the literal affine system

The actual native and source Z-charts are now identified with the
literal affine rings in the manuscript. The native chart is the
polynomial plane F[X][X]. The source chart is the actual iterated
quadratic algebra with radicands c_i prod(X+a) prod(Y+b), indexed by
the original finite list. Scheme isomorphisms identify the actual
basic-open subschemes with the spectra of these rings.

The construction first proves, for any graded commutative coefficient
algebra and positive D, that its rescaled Veronese chart at b^D is
isomorphic to the original homogeneous chart at b. The literal map
uses dehomogenization and the quotient by b^D-1; its injectivity and
surjectivity are proved by clearing powers of b. No domain hypothesis
is used, and rings with zero divisors are included.

For the quadratic tower, coefficient specialization is proved
surjective when the base specialization is surjective, with kernel
exactly the extended base kernel. Specializing the homogenizing
variable to one has exactly the principal kernel (Z-1), both in the
coefficient ring and in the actual source coordinate quotient.
This produces the affine chart isomorphism without assuming a
geometric identification. The actual base variables and radical
generators are proved to map to their literal affine counterparts.
These ring and chart computations allow any coefficient field and
zero coefficients, under the explicit radicand identities and degree
bound used to construct the grading.

Under the separate existing source-integrality hypotheses, the
canonical scheme function fields are now explicitly isomorphic to
F(X,Y) and the affine generic split-radical tower. The proof uses the
canonical chart-to-generic-stalk map and its actual fraction-field
property, together with the previously verified affine generic tower
fraction-field theorem. The actual projective function-field map
commutes with these two explicit isomorphisms and the literal base
field inclusion. Naturality is proved on dehomogenized chart elements
and extended to the full fields by the localization universal property.
This closes the previously open affine generic-tower identification.

The native target's global projective-plane identification, the
comparison of the chosen graded presentation with the explicit
projective embedding and hyperplane bundle, the curve-degree
projection formula and the external surface/curve host counts remain
open. The source Hilbert multiplicity 2^k D^2, finite-flat rank 2^k
and actual function-field degree 2^k remain previously checked facts.
T1.7 remains in_progress, numbered coverage remains 79/167, confirmed
improvements remain 107 and Palomar remains deferred. Original
manuscript sources are unchanged.

Verified with Lean v4.36.0-rc2: full build 12143 jobs, direct axiom audit of 8258 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 6010 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 13.60 GiB.


## Global standard projective-plane target and finite flat source projection

The native standard Veronese projective target is now globally
isomorphic to the standard projective plane, defined as Proj of the
ordinary homogeneous grading on F[X_0,X_1,X_2]. This is an actual
scheme isomorphism, constructed from the literal Veronese inclusion.
Composing it with the existing source morphism gives the actual
projection to that plane. This projection is proved finite, flat,
surjective and of constant scheme rank 2^k at every plane point.
These cover statements allow arbitrary coefficient fields and zero
radicand coefficients; the separate source-integrality hypotheses
remain explicit for function-field assertions.

The underlying general theorem proves Proj invariance under every
positive Veronese construction on an internally graded commutative
coefficient algebra. No domain, reducedness, characteristic-zero,
Noetherian or generation-in-degree-one hypothesis is used. The
inclusion multiplies the grading by D, so it is handled by a verified
positive-degree-scaling Proj functor, not incorrectly treated as a
same-degree graded homomorphism. Homogeneous ideal pullback is
justified by a proved projection identity; actual homogeneous
localization and local-ring maps multiply fraction degrees by D.

For admissibility, a positive-degree homogeneous element has its Dth
power in the positive part of the actual Veronese. The necessary
irrelevant-ideal containment therefore holds in the radical. On
every positive homogeneous chart the actual ring map is proved
bijective: all relevant numerator degrees are already multiples
of D. Local scheme chart compatibility and locality of being an
isomorphism then prove the global isomorphism. The point map,
structure sheaf maps and generic local-ring locality are constructed
and checked, rather than supplied as an abstract isomorphism premise.

The scaled-localization and Proj chart constructions adapt the
pinned Mathlib source with its Kenny Lau copyright and Apache 2.0
attribution preserved in the new modules. The upstream files and
pinned dependency are unchanged.

This closes the previously open global projective-plane target
identification. The numerical Hilbert multiplicity 2^k D^2, explicit
affine generic-field identifications and actual function-field
degree 2^k remain checked. Comparison with the chosen projective
embedding and hyperplane bundle, the curve-degree projection
formula, low-degree curve geometry and external surface/curve
point counts remain open. T1.7 remains in_progress, numbered
coverage remains 79/167, confirmed improvements remain 107 and
Palomar remains deferred. Original manuscript sources are unchanged.

Verified with Lean v4.36.0-rc2: full build 12159 jobs, direct axiom audit of 8285 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 6049 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 13.58 GiB.


## Actual closed projective embedding, coordinate quotient and Hilbert degree

The actual source now has the closed projective immersion defined
by precisely its degree-D base monomials and radical coordinates.
The ambient scheme is the standard Proj of the ordinary polynomial
ring on that literal coordinate index. An explicit bijection
identifies the index with the disjoint union of ternary degree-D
exponents and the original radical indices. Its cardinality is
binom(D+2,2)+k, giving the manuscript ambient coordinate count.

The polynomial evaluation map to the actual source Veronese is
constructed, proved surjective and proved to preserve every
homogeneous degree. Its irrelevant-ideal admissibility follows
from the actual degree-one generators. Surjectivity descends to
all degree-one affine chart maps by dehomogenization. Their actual
spectrum maps are closed immersions, and the checked chart
compatibility proves the global source map is a closed immersion.
No closed-immersion premise is supplied as an external input.

The homogeneous coordinate ideal is exactly the kernel of that
same polynomial evaluation map. It is proved homogeneous. Its
literal polynomial quotient has the grading whose pieces are the
images of the ordinary homogeneous polynomial pieces. The actual
quotient algebra is proved isomorphic to the source Veronese, and
every graded piece is identified by a linear equivalence.
Thus the coordinate quotient and grading used in the Hilbert
calculation match the verified chosen projective presentation.

Every coordinate piece is finite dimensional. The previously
computed exact source Hilbert function and unique eventual
quadratic polynomial are transported to these actual coordinate
pieces. Their Hilbert multiplicity is proved to be 2^k D^2.
The closed immersion and this numerical multiplicity are bundled
in one checked statement. This computes the Hilbert degree in the
manuscript's explicit projective coordinates, rather than only an
invariant of an unidentified graded algebra.

The structural embedding permits arbitrary coefficient fields and
zero coefficients under the explicit degree bound and positive D.
The Hilbert formula retains the literal original radicand identities.
The separate source-integrality hypotheses are unchanged for
function-field arguments. The hyperplane-bundle pullback comparison,
curve-degree projection formula, low-degree curve geometry, a
scheme-dimension comparison and external surface/curve point counts
remain open. T1.7 stays in_progress, numbered coverage remains
79/167, confirmed improvements remain 107 and Palomar remains
deferred. Original manuscript sources are unchanged.

Verified with Lean v4.36.0-rc2: full build 12173 jobs, direct axiom audit of 8318 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 6098 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 13.56 GiB.


## Plane-equation quotient and actual Veronese Hilbert degree

For the literal quotient F[X,Y,Z]/(f), with nonzero homogeneous f
of degree e, multiplication by f is an injective map from the
ordinary degree-n piece to the degree-(n+e) piece. Its actual range
is exactly the kernel of the homogeneous quotient map. Rank-nullity
and the proved monomial bases therefore give
h(n+e)+binom(n+2,2)=binom(n+e+2,2).
Every quotient piece is finite dimensional. Its unique eventual
Hilbert polynomial is eT+(3e-e^2)/2. For positive e its degree is
one and its Hilbert multiplicity is e.

For any internally graded algebra over a field, the actual rescaled
D-th Veronese piece is proved linearly equivalent to the original
degree-nD piece. For positive D, any established Hilbert polynomial
P becomes P(DT); its multiplicity is multiplied by D^(deg P).
These are proved from the actual pieces and polynomial composition.
Applying this to the literal plane-equation quotient gives Hilbert
degree De for its D-th Veronese, with its quotient and Veronese
gradings explicitly constructed.

These calculations hold over any coefficient field. The plane
Hilbert identities require neither irreducibility nor reducedness
of f, only f nonzero and homogeneous; positivity of e and D is
explicit when claiming degree one or Veronese rescaling. No general
Hilbert-polynomial existence theorem is assumed.

This proves the target plane-curve factor De needed in Step 2.
The remaining comparison with the Hilbert degree of an arbitrary
integral curve in the actual source still requires the finite
graded-module rank formula and its degree-zero field comparison.
The full curve projection-degree formula, scheme-dimension and
hyperplane-bundle comparisons, low-degree curve geometry and
external host-count inputs remain open. T1.7 stays in_progress,
numbered coverage remains 79/167 and confirmed improvements remain
107. Palomar remains deferred; original sources are unchanged.

Verified with Lean v4.36.0-rc2: full build 12185 jobs, direct axiom audit of 8351 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 6144 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 13.55 GiB.


## Actual graded curve quotients, finite module rank and Hilbert comparison

The finite graded-module comparison is now constructed from actual
homogeneous generators. The component map sends a tuple of coefficients
in degrees n-w_i to the actual sum of their images times the generators.
Projection onto homogeneous components proves surjectivity for a
generating family; actual module independence proves injectivity.
Both dimension inequalities follow from checked linear maps.

A maximal independent subfamily of finite generators is selected using
the pinned Mathlib theorem, with a common nonzero module denominator.
A nonzero homogeneous component of that denominator gives an injection
from each sufficiently high target piece into the range of a shifted
free component map. The reverse injection comes from independence.
Thus the actual target Hilbert function is squeezed between the sums
of the source functions at n-w_i and n+m-w_i. The subfamily cardinality
is proved equal to the actual module finrank, and also to the rank of
compatible fraction-field extensions, rather than supplied as a premise.

If the base function is eventually an+b, the target function differs
from rank*a*n by a bounded rational error. This numerical slope is
proved unique. Any polynomial eventually equal to a function with
that bounded error must be affine: a nonconstant remaining polynomial
would have unbounded absolute evaluations on natural arguments.
Consequently, if a target Hilbert polynomial exists and a is positive,
its degree is proved to be one and its Hilbert multiplicity equals
rank*a. Neither the polynomial degree nor the multiplicity identity
is assumed. General existence of the target polynomial remains an
explicit ordinary theorem argument, with no new axiom.

The actual quotient by any homogeneous ideal is supplied with its
image grading, decomposition, projection maps and graded quotient map.
An actual graded algebra map descends to the quotient by a target
ideal and its actual preimage. The descended map is injective, and
the given finite homogeneous module generators descend literally.

These constructions are instantiated for homogeneous prime quotients
of the manuscript source Veronese, using its actual quadratic normal
basis and radical-count weights. The source quotient and its base
preimage quotient are domains, their actual pieces are finite
dimensional, and their module rank is between 1 and 2^k. Their Hilbert
slope and, when the explicitly required polynomial exists, their
multiplicity obey the proved rank formula for any established affine
base Hilbert polynomial. The actual quotient maps, gradings and
generator identities are included in the checked statements.

The full manuscript curve projection formula is still open. The
remaining bridges include general Hilbert-polynomial existence for
these curve quotients, identification of the image with its literal
plane-equation Veronese, and comparison of cone-module rank with the
degree-zero projective function-field extension. Scheme dimension,
hyperplane-bundle comparison, low-degree curve geometry and external
host-count inputs also remain open. T1.7 stays in_progress; numbered
coverage remains 79/167, confirmed improvements remain 107 and Palomar
remains deferred. Original manuscript sources are unchanged.

Verified with Lean v4.36.0-rc2: full build 12203 jobs, direct axiom audit of 8413 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 6229 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 13.53 GiB.


## Actual projective curve quotient function-field rank

The finite graded-module rank is now identified with the degree of
the actual projective function-field map. This comparison is proved
through literal degree-one affine charts, with no Laurent-polynomial
identification or cone-field degree supplied as a premise.

The common denominator of an independent homogeneous free approximation
can be chosen homogeneous and nonzero. Every component of an arbitrary
clearing denominator still clears the entire module: the proof handles
both the allowed-degree terms and the terms below a generator weight,
then recomposes an arbitrary element from its homogeneous components.

For a nonzero degree-one chart coordinate, dehomogenization is injective
on each homogeneous component of a domain. Every chart element has
representatives in all sufficiently large degrees. For a finite family
of chart coefficients, their representative degrees can be adjusted
simultaneously against the actual generator weights. Thus a relation
between the dehomogenized independent generators lifts to a single
homogeneous relation in the original module, proving chart independence.
Actual finite generators and the homogeneous denominator descend by
the checked dehomogenization diagram. The same independent subfamily
therefore computes both the global module rank and the chart-module
rank. Their equality is proved, rather than assumed.

The actual generic-point function fields are already proved to be the
fraction fields of these charts. Their checked naturality and the
pinned fraction-field rank theorem identify the degree of the actual
scheme function-field map with the chart rank, hence with the global
finite graded-module rank.

Irrelevant ideals commute with surjective graded maps. The actual
irrelevant-ideal radical bound is proved to descend to a homogeneous
target quotient and its actual base preimage quotient. This constructs
the projective morphism between the literal source prime quotient and
its literal base quotient. A nonzero degree-one base coordinate proves
both projective spectra nonempty and integral. Their actual geometric
function-field map is constructed and its degree is proved equal to
the already computed source-quotient module rank, between 1 and 2^k.
The source Hilbert multiplicity comparison is restated using this
actual projective field degree, still with the target Hilbert-polynomial
existence and the actual affine base polynomial as explicit arguments.

This closes the module-to-projective-function-field rank comparison
for these actual quotients. The full manuscript curve formula still
requires general Hilbert-polynomial existence for the curve quotients
and identification of the base image quotient with the literal
plane-equation Veronese, whose Hilbert degree De is already checked.
Scheme dimension, hyperplane-bundle comparison, low-degree curve
geometry and external host-count inputs remain open. T1.7 stays
in_progress; numbered coverage remains 79/167, confirmed improvements
remain 107 and Palomar remains deferred. Original sources are unchanged.

Verified with Lean v4.36.0-rc2: full build 12221 jobs, direct axiom audit of 8440 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 6261 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 13.50 GiB.


## Hilbert-polynomial existence from two actual parameters

Hilbert-polynomial existence is now proved for an internally graded
F-algebra domain finite over two actual degree-one parameters, with
finite-dimensional homogeneous pieces. Finite module generation, rather
than a Hilbert-polynomial existence premise, is the input.

A homogeneous polynomial in one variable is its actual coefficient
times the corresponding monomial. After the degrees of finitely many
homogeneous generators, multiplication by that parameter is surjective
on consecutive module pieces. Their finite dimensions decrease and
therefore eventually stabilize. This proves an actual constant Hilbert
polynomial for any such one-parameter module, including rings with
zero divisors.

For two parameters, the actual homogeneous quotient by the first
parameter is generated over the second. The polynomial coefficient
map that kills the first variable is constructed and checked. The
quotient Hilbert function therefore stabilizes. If the first parameter
is nonzero in the domain, the checked hyperplane exact sequence gives
an affine Hilbert function by a natural-number recurrence. If it is
zero, the original Hilbert function is already eventually constant.
Both cases produce actual rational Hilbert polynomials. Finally, finite
module generation yields a finite homogeneous generating family by
taking the finitely many components of actual finite generators.

The theorem still needs a checked two-parameter finite normalization
for the actual curve quotients. Identification of the base image
quotient with the literal plane-equation Veronese remains open, as do
scheme dimension, hyperplane-bundle comparison, low-degree geometry
and external host-count inputs. No manuscript result is counted as
complete on the basis of this general algebraic step. Coverage stays
79/167 and the confirmed mathematical-improvement count stays 107.
Palomar remains deferred; original manuscript sources are unchanged.

Verified with Lean v4.36.0-rc2: full build 12235 jobs, direct axiom audit of 8466 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 6289 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 13.49 GiB.


## Literal Veronese quotients and plane-equation Hilbert degree

The literal Veronese construction now commutes with quotient by a
homogeneous ideal, after contracting that ideal along the inclusion.
A graded map is restricted to the actual Veronese subalgebras. Its
surjectivity follows by lifting each homogeneous component, rather
than by assuming surjectivity after restriction. The restricted
quotient kernel is proved equal to the contracted ideal. The actual
quotient isomorphism identifies every rescaled homogeneous piece,
including its vector-space dimension.

For a nonzero homogeneous plane equation f of degree e, this constructs
an isomorphism from the native Veronese quotient by the contracted
principal ideal (f) to the literal D-th Veronese of F[X,Y,Z]/(f).
The native quotient therefore has the actual affine Hilbert polynomial
De*T + (3e-e^2)/2 and Hilbert multiplicity De when D,e are positive.
This identifies actual quotient pieces; no Hilbert-degree comparison
is supplied as an assumption.

The remaining geometric step is to extract the homogeneous plane
equation and prove that the actual image prime ideal is its contracted
principal ideal. The Veronese/quotient algebra comparison needed once
that equality is established is now proved. Finite two-parameter
normalization for actual source curve quotients, scheme dimension,
hyperplane-bundle comparison, low-degree geometry and external host
counts remain open. T1.7 stays in_progress, numbered coverage stays
79/167, confirmed mathematical improvements stay 107, and Palomar
remains deferred. Original sources are unchanged.

Verified with Lean v4.36.0-rc2: full build 12241 jobs, direct axiom audit of 8484 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 6313 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 13.48 GiB.


## Finite plane normalization and actual source curve degree

Finite two-parameter normalization is now constructed over an infinite
field for an actual homogeneous plane quotient containing a nonzero
homogeneous relation. A checked scaling identity proves nonvanishing
somewhere on the fixed projective affine patch X0=1. An explicit
invertible linear shear preserves every homogeneous degree and makes
the first-variable leading coefficient a nonzero scalar. Its monic
normalization and the actual polynomial quotient isomorphism prove
module finiteness over the remaining linear coordinates.

A polynomial algebra is proved finite over its positive coordinate
powers: each coordinate is integral over its power, and the actual
finite coordinate family generates the algebra. For an algebra already
finite over linear parameters, their D-th powers give a finite action
on the actual ambient algebra. Its literal Veronese embeds linearly
into that finite module over a Noetherian polynomial ring, so it is
finite too. The same parameters are proved to have rescaled degree one.
This supplies actual finite parameters, rather than assuming them.

Finite parameters transfer through the checked Veronese quotient
isomorphism and through actual finite graded maps. The actual source
prime quotient map is constructed as an F-algebra map and is proved
finite from its existing homogeneous generators. Hence it inherits
finite parameters and an actual Hilbert polynomial from its native
base quotient.

When the actual base ideal is the contraction of the principal ideal
of a nonzero homogeneous plane equation f of positive degree e, the
native base has the explicit affine Hilbert polynomial
De*T+(3e-e^2)/2, and source Hilbert-polynomial existence is now proved
from that ideal equality. Neither Hilbert existence nor an assumed
Hilbert slope remains a separate input. The actual source Hilbert
multiplicity is proved equal to D*e times the degree of the actual
projective function-field map between the literal quotient Proj schemes.
The stored public theorem states this literal field finrank, verified
by inspecting its elaborated type and kernel axioms.

This discharges the Hilbert-existence and Veronese-quotient comparison
steps for an identified plane-equation image. Extracting that equation
from the actual geometric curve image prime remains open; the image
ideal equality is still an explicit premise. Scheme dimension,
hyperplane-bundle comparison, low-degree geometry and external host
counts remain open. T1.7 stays in_progress, coverage stays 79/167,
confirmed improvements stay 107, and Palomar remains deferred.
Original manuscript sources are unchanged. No new Paper C code is reused;
the adapted homogeneous top-coefficient argument is attributed to the
pinned Mathlib source with its Apache licence.

Verified with Lean v4.36.0-rc2: full build 12269 jobs, direct axiom audit of 8532 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 6372 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 15.21 GiB.


## Actual source prime heights and extracted plane-equation degree

The actual homogeneous prime ideals now pass through the checked
Veronese projective isomorphism. Its underlying point equivalence is
constructed, and the contraction of its inverse prime is proved to be
the original Veronese prime. For an actual source prime quotient, a
nonzero degree-one base quotient coordinate constructs its projective
base prime. Its inverse gives an actual homogeneous prime in the
ordinary three-variable plane ring, with contraction exactly equal to
the actual base ideal.

A nonzero principal homogeneous polynomial ideal is proved to have a
homogeneous generator. The proof takes a nonzero homogeneous component
of a generator. Divisibility by the generator and additivity of total
degree force the quotient to be a nonzero constant. The generator is
therefore a scalar multiple of that homogeneous component. For a proper
ideal its degree is positive. The pinned UFD height-one theorem then
produces a positive-degree homogeneous generator of a height-one prime;
primality of the principal ideal proves the generator irreducible.

Prime contraction is strictly increasing along chains under integral
maps. The actual height inequality is proved using order height. With
going down, chains lift and the heights are equal. The actual source
projection has both properties: its checked finite free basis supplies
integrality and flatness, hence going down. Therefore the actual source
prime and its native base contraction have equal heights. Every positive
Veronese inclusion is also proved integral by taking D-th powers of
homogeneous elements and recomposing arbitrary elements. The lifted
ordinary plane prime has height at most the native base prime. If the
source prime has height one, its base contraction is nonzero of height
one, so the lifted ordinary plane prime is nonzero and has height one.

Consequently a height-one actual source prime supplies its own
homogeneous irreducible plane equation and the exact contracted-ideal
equality. Over an infinite field, source Hilbert-polynomial existence
then follows from the preceding finite-normalization proof. The actual
source Hilbert multiplicity equals D times the extracted equation degree
times the actual projective function-field degree. The final theorem
assumes neither a plane equation, an image ideal equality, an image-height
condition, a Hilbert polynomial nor a slope. The source-height-one input
and a nonzero degree-one base quotient coordinate remain explicit.

The algebraic image-equation extraction is thus complete in this
source-height-one formulation. A separate statement-alignment step must
relate the manuscript's geometric dimension-one curve condition to that
source prime height, and compare the actual Hilbert multiplicity with
the intrinsic hyperplane degree. Low-degree geometry and external host
counts remain open. T1.7 stays in_progress, coverage stays 79/167,
confirmed improvements stay 107 and Palomar remains deferred. Original
manuscript sources are unchanged.

Verified with Lean v4.36.0-rc2: full build 12297 jobs, direct axiom audit of 8555 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 6399 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 15.18 GiB.


## Actual projective curve points and their constructed chart coordinates

The source curve degree theorem now takes an actual projective source
point and the height-one condition on its homogeneous prime. The point
itself supplies primality, homogeneity, and relevance. Its image under
the actual source projection is a relevant native Veronese prime.

For any internally graded algebra generated in degree one, relevance
of a quotient ideal is proved to yield a nonzero degree-one quotient
coordinate: otherwise all degree-one generators would lie in the ideal,
forcing it to contain the irrelevant ideal. The native base satisfies
the required generation theorem. An actual nonzero base coordinate is
therefore constructed from the source projective point and its actual
projection. No coordinate witness is a separate theorem input.

The resulting theorem constructs the homogeneous irreducible plane
equation, proves the actual base ideal equals its contracted principal
ideal, proves source Hilbert-polynomial existence, and identifies the
actual source Hilbert multiplicity with D times the extracted plane
equation degree times the actual projective function-field degree.
The stored public statement uses literal quotient Proj function fields;
its elaborated type and kernel axioms are inspected directly.

The remaining statement-alignment steps concern the geometric curve
dimension versus homogeneous prime height and intrinsic hyperplane
degree versus the actual coordinate Hilbert multiplicity. Low-degree
curve geometry and the external uniform host counts remain open.
T1.7 stays in_progress, numbered coverage stays 79/167, confirmed
mathematical improvements stay 107, and Palomar remains deferred.
Original manuscript sources are unchanged.

Verified with Lean v4.36.0-rc2: full build 12303 jobs, direct axiom audit of 8565 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 6413 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 15.17 GiB.


## Actual small-degree curves and degree-one function-field square descent

For an actual height-one projective source point, source Hilbert
multiplicity below 2D now forces a homogeneous linear irreducible
plane-image equation and actual projective function-field degree one.
The proof uses the already established literal degree formula and the
positive integer factors; it assumes no line equation or birationality.

A degree-one field extension is proved to be an actual algebra
isomorphism and to reflect squares and quadratic roots. The generic
finite graded-map rank comparison is used to construct the isomorphism
of its actual projective function fields when module rank is one.
This is specialized to the actual source-point projection. The public
square-reflection theorem concerns the literal quotient Proj function
fields and their actual scalar map. It requires no infinite-field
assumption. The public elaborated types and kernel axioms are inspected
directly. Instance-preserving generic specialization avoids rebuilding
large stalk-map expressions in handwritten source-point field types.

Thus a source curve below 2D has the linear image and degree-one field
map needed for the next exclusion step. The existing functional-square
line obstruction still needs the checked affine line parametrization
and the actual curve-coordinate/function-field diagram before it can
exclude all such curves through admissible hosts. This geometric
exclusion is not claimed here. Geometric dimension/prime-height and
intrinsic hyperplane-degree/Hilbert-multiplicity alignment, higher
low-degree geometry, and the external uniform host counts remain open.
T1.7 stays in_progress, coverage stays 79/167, confirmed improvements
stay 107 and Palomar remains deferred. Original sources are unchanged.

Verified with Lean v4.36.0-rc2: full build 12311 jobs, direct axiom audit of 8573 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 6425 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 15.15 GiB.


## Actual radical descent, affine quotient charts, and graph-line exclusion

The literal homogeneous radical equations are now proved in the actual
source and base curve quotients. For a finite graded projection of rank
one, these equations descend to squares in the actual projective base
function field on any nonzero degree-one chart. This is specialized to
an actual projective source point and its actual degree-one field map.

For any surjective graded map, the kernel of the actual degree-one
chart map is proved to be the image of the graded-map kernel under
dehomogenization. The actual native Veronese quotient Z-chart is thereby
identified with the affine polynomial-plane quotient. Contracting a
homogeneous principal plane ideal and then taking this chart gives
exactly the principal ideal of its affine equation, for any homogeneous
equation degree and any positive Veronese degree.

For a plane-image ideal whose affine equation is Y = alpha X + beta,
the actual base chart is constructed as a polynomial ring in one
variable. Its nonzero chart coordinate follows from the image-ideal
condition. The chart equivalence sends every literal radicand to exactly
the line-restriction polynomial used in the proved square obstruction.
The actual source degree-one projection therefore produces functional
squares in the ordinary rational function field, without separate
square or coordinate-diagram assumptions. Over the rationals, the
admissible-host square-class and disjoint-support hypotheses contradict
this. An actual height-one source curve with such a graph-line image
through an admissible host has Hilbert multiplicity at least 2D.

The graph-line image ideal and host-on-line conditions remain explicit.
The classification of an arbitrary homogeneous linear image into a
graph or vertical line, and the corresponding actual vertical-chart
diagram, remain open. So do geometric dimension/prime-height and
intrinsic hyperplane-degree/Hilbert-multiplicity alignment, higher
low-degree geometry, and external uniform host counts. T1.7 remains
in_progress, coverage stays 79/167, confirmed improvements stay 107,
and Palomar remains deferred. Original sources are unchanged.

Verified with Lean v4.36.0-rc2: full build 12331 jobs, direct axiom audit of 8599 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 6464 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 15.12 GiB.


## Actual full low-degree exclusion through affine source points

The actual vertical base-curve chart is now constructed as a polynomial
ring in one variable. Its equivalence sends each literal radicand to
the polynomial used in the existing vertical functional-square
obstruction. Degree-one projection of the actual source curve gives
these functional squares, without separate square or chart-coordinate
assumptions. The admissible-host hypotheses exclude this projection.

A homogeneous polynomial of degree one is proved to equal its literal
linear coefficient form. On the native Z-chart, a nonzero such equation
through an affine point is classified exhaustively as a graph line
through that point or the corresponding vertical line, including the
horizontal case. Multiplication by the appropriate nonzero scalar is
proved to preserve the exact principal ideal.

Combining this classification, the previously established actual curve
degree formula, and both actual chart-square diagrams proves the full
coordinate-algebraic version of Step 3: an actual height-one projective
source curve whose affine image contains an admissible rational host
has Hilbert multiplicity at least 2D. No line, plane equation,
birationality, or functional-square witness is an input. Both block
independence conditions, direct sum, nonzero coefficients, at least two
equations, and both disjoint nonempty support families are explicit.

The containment condition is also proved from an actual affine point
of the split-radical source with its literal base evaluation and an
actual source-curve ideal contained in that point's evaluation kernel.
The actual affine source point restricts to a map on the homogeneous
source Veronese ring, and its base image is proved to be the literal
affine host evaluation. Thus the projection/point containment diagram
is checked, rather than an independent assumption in the degree bound.

The previously open vertical diagram and linear-image classification
are discharged. Geometric curve dimension versus source prime height
and intrinsic hyperplane degree versus coordinate Hilbert multiplicity
still require statement alignment. Higher low-degree curve geometry
and external surface/curve uniform point counts remain open. T1.7
stays in_progress, coverage stays 79/167, confirmed mathematical
improvements stay 107, and Palomar remains deferred. Original sources
are unchanged.

Verified with Lean v4.36.0-rc2: full build 12349 jobs, direct axiom audit of 8623 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 6496 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 15.10 GiB.


## Actual embedded-curve coordinate quotients and degree comparison

The actual ambient homogeneous coordinate ideal of a source curve is
now constructed as the preimage of its source prime under exactly the
polynomial evaluation map defining the chosen projective embedding.
Its coordinate quotient is constructed as an algebra isomorphic to the
actual source prime quotient, with a linear equivalence of every pair
of corresponding graded pieces. These constructions work for general
homogeneous ideals; no primality or Hilbert polynomial is assumed for
the coordinate algebra comparison itself.

For an actual source projective point, the ambient coordinate ideal is
proved to be the ideal of its actual image under the chosen embedding.
It is prime and projectively relevant and contains the global source
embedding relations. Thus the coordinate quotient is attached to the
actual embedded image point, rather than an unrelated presentation.

Equality of the actual graded-piece dimensions transports Hilbert
polynomial existence, the polynomial itself, and its multiplicity.
For an actual height-one source point this gives the ambient curve
coordinate Hilbert polynomial, its multiplicity equality with the
source quotient, and the literal degree formula D times the plane-image
equation degree times the actual projective function-field degree.
Over the rationals, the full low-degree exclusion through an actual
admissible affine source point therefore yields multiplicity at least
2D in the actual ambient homogeneous coordinate presentation as well.

The curve-level comparison with the chosen projective coordinate
presentation is now discharged. A separate intrinsic line-bundle
intersection-degree theory is not constructed or claimed here.
Geometric curve dimension versus homogeneous source prime height,
higher low-degree curve geometry, and external surface/curve uniform
point counts remain open. T1.7 stays in_progress, numbered coverage
stays 79/167, confirmed mathematical improvements stay 107, and Palomar
remains deferred. Original manuscript sources are unchanged.

Verified with Lean v4.36.0-rc2: full build 12361 jobs, direct axiom audit of 8648 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 6529 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 15.08 GiB.


## P1-MATH-0108 — Explicit grid-uniform rational interpolation

A bounded-degree rational function is now proved to be determined by
more than twice its degree many distinct abscissae. The cross product
of two interpolating polynomial pairs vanishes by its actual degree
and roots. For a reduced pair of exact maximum degree a with nonzero
denominator, every other interpolating pair of degrees at most a is
an actual constant scalar multiple. The actual linear interpolation
constraint map on the bounded-polynomial pair space is constructed;
its kernel is proved to equal the span of that pair and has dimension
one.

An elementary bounded integer-kernel construction is proved for every
integer matrix with t rows and t+1 columns: entries of absolute value
at most H yield a nonzero integer kernel vector whose coordinates have
absolute value at most (3(t+1)H)^t. This extends the existing explicit
pigeonhole proof to the codimension-one regime needed for interpolation.

For 2a+1 integer grid points with distinct abscissae and both coordinates
of absolute value at most B, B at least one, the actual interpolation
matrix has 2a+2 columns and entry height at most B^(a+1). Its bounded
integer kernel gives actual integral polynomials P,Q, Q nonzero, of
degrees at most a, with every coefficient bounded by
(3(2a+2))^(2a+1) B^((a+1)(2a+1)). If a reduced rational pair of exact
degree a fits that grid, these integral polynomials map to a common
nonzero rational scalar multiple of that pair. Their rational images
are proved coprime and retain exact maximum degree a. The coefficient
bound therefore depends on the grid and degree alone, independently
of the original rational coefficients or auxiliary radical coefficients.

This supplies an explicit alternative proof of the coefficient-uniform
interpolation step in Step 6. It does not establish the preceding
normalization, genus, branching, reduced-fibre or rational-graph
conclusions. The remaining geometric dimension/prime-height and any
intrinsic line-bundle degree interpretation are separate; external
uniform point counts also remain open. T1.7 stays in_progress, numbered
coverage stays 79/167, confirmed mathematical improvements become 108,
and Palomar remains deferred. Original sources are unchanged.

Verified with Lean v4.36.0-rc2: full build 12373 jobs, direct axiom audit of 8673 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 6561 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 15.06 GiB.


## Grid-uniform rational-graph exclusion after interpolation

The arithmetic alternatives following rational interpolation in Step 6
are now proved for actual rational polynomial pairs and integral points.
For integral numerator and denominator polynomials whose rational images
are coprime, the denominator value at an integral graph point divides
the actual nonzero resultant. The existing determinant height bound
therefore bounds that value uniformly. A nonconstant integer polynomial
of coefficient height M taking a value of absolute value at most K has
its integer input bounded by M+K, via the verified integral-root bound.
Consequently a nonconstant rational denominator gives an explicit
abscissa bound M+(2a)! M^(2a).

For a polynomial graph of exact degree a at least two, the nonzero
integral leading coefficient and a bounded coefficient tail prove
|X|^a <= |P(X)|+a M |X|^(a-1). At an integral graph point with
|Y| <= 2|X| and constant denominator of height at most M this gives
|X| <= (a+2)M. The actual integral presentation from the grid is proved
to preserve both degrees and every original integral graph equation.

The remaining linear graph is treated directly from two actual offset
grid matches. They give proportional positive selected values at the
host; independence and direct sum contradict this. This argument takes
no functional-square premise and no degree-one curve-field assumption.

All cases are combined: for every positive exact rational-function
degree a and 2a+1 distinct offset abscissae, the actual reduced rational
graph fitting the grid has no admissible comparable integral host with
abscissa larger than an explicit polynomial in the offset height B.
Writing C=(3(2a+2))^(2a+1), its bound is at most
[C+(2a)! C^(2a)+(a+2)C] B^(2a(a+1)(2a+1)). This is uniform in the
original rational coefficients and all auxiliary radical coefficients.

Thus the elementary interpolation and subsequent arithmetic rational-
graph exclusion in Step 6 are checked. The geometric work producing
that reduced rational graph and its offset-grid matches from a general
low-degree source curve, including genus, branching and reduced-fibre
arguments, remains open. Geometric curve dimension/source prime height,
any intrinsic line-bundle intersection degree interpretation, and the
external surface/curve point counts also remain open. T1.7 stays
in_progress, coverage stays 79/167, confirmed improvements stay 108,
and Palomar remains deferred. Original sources are unchanged.

Verified with Lean v4.36.0-rc2: full build 12391 jobs, direct axiom audit of 8691 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 6581 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 15.04 GiB.


## Rational descent, surviving equation grids, and uniform critical exclusion

The arithmetic graph cutoff is now converted to an actual uniform
large-scale exclusion in the critical band. If the offset height is
at most (L+1)^J and L differs from log(N)/log(2) by at most C, then
one threshold, chosen before all coefficients, grids and hosts,
excludes admissible graph points with X>=N and |Y|<=2N.

The interpolation also descends coefficients: over every field F of
characteristic zero, a reduced rational polynomial pair of exact
maximum degree a fitting 2a+1 bounded integer grid points is a common
nonzero F-scalar multiple of an actual bounded integral pair. The
rational images of that integral pair are proved coprime. This gives
an actual reduced pair over the rationals with the same exact degree,
whose images under the rational embedding into F are the stated
scalar multiples. Its integral graph-point condition is proved
exactly equivalent to the original one. Rationality of the initial
graph's coefficients is therefore not a separate input.

The finite selection of the interpolation grid is also constructed.
Three disjoint root families of cardinality a>=1 give at least 3a
grid points with distinct first coordinates; an actual 2a+1-point
subfamily is selected. If the initial number of equations is at least
4(E+1)^2 and at most 2e^2 are excluded, e<=E, the actual surviving
set has at least three equations. No assumed grid-selection map or
survivor-count witness remains.

These results are combined for the actual disjoint equation-root
families and their actual exceptional set. A single large-scale
threshold excludes the resulting graph host, uniformly over all
characteristic-zero coefficient fields, equation families, excluded
sets, numerator/denominator coefficients, and admissible hosts. It
retains the exact root-family disjointness, cardinalities, positivity,
selected-value independence, direct sum, critical band and offset
height hypotheses. The numeric exceptional-set bound and the reduced
graph with its actual root matches are explicit hypotheses: the
preceding genus, branching, reduced-fibre, and graph-construction
geometry has not been supplied or counted as complete.

T1.7 stays in_progress, numbered coverage stays 79/167, confirmed
mathematical improvements stay 108, and Palomar remains deferred.
Geometric curve dimension/source prime height, any intrinsic
line-bundle degree interpretation, and the external uniform
surface/curve point counts also remain open. Original sources and
the Lean/Mathlib pins are unchanged.

Verified with Lean v4.36.0-rc2: full build 12403 jobs, direct axiom audit of 8708 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 6601 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 15.02 GiB.


## Actual field-degree tower and direct common-quotient graph construction

The rational-function degree tower in Step 5 is now proved for
actual intermediate fields. For a reduced pair p,q over any field F,
q nonzero, the degree of F(T) over F(p/q) is max(deg p,deg q), using
the proved Mathlib rational-function degree theorem and an explicit
comparison with the supplied reduced pair. Evaluating at an actual
transcendental x in an extension K transports this to F(x)/F(p(x)/q(x)).
The tower identity for the actual extension K follows; positive degree
of K/F(x) permits exact cancellation in the manuscript's mY=a*mX.

A more direct algebraic construction is also proved. Write
A_nu=b_nu product_{i in I_nu}(T+i), with nonzero b_nu in F, disjoint
root sets of the same positive cardinality a, and actual identities
A_nu(x)=t*(y+j_nu). Two equations suffice to construct
q=A_0-A_1 and p=j_0*A_1-j_1*A_0. The denominator is nonzero;
j_0 and j_1 are proved distinct, rather than assumed distinct.
The pair p,q is coprime and has exact maximum degree a. Every further
equation gives the actual polynomial identity
p+j_nu*q=(j_0-j_1)*A_nu. Thus all selected offsets give the required
grid matches, and coprimality proves the denominator nonzero there.
The natural input in which the original quotients differ by nonzero
F-constants is converted to these identities as well. Exact graph
degree and all root matches therefore follow algebraically after
the common-quotient step, without a separate curve-degree cancellation.

The graph relation C(p)-Y*C(q) is proved to lie in the actual kernel
of evaluation at the function-field coordinates. Every integral
point whose evaluation kernel contains that actual coordinate ideal
satisfies the graph equation. Combining the constructed reduced graph,
all its constructed matches, actual survivor/grid selection, rational
descent and the preceding arithmetic bounds gives an explicit offset-
only bound on admissible integral curve points. Its critical-band
large-scale exclusion chooses one threshold before both fields F,K,
the equations, constants, exceptional set, coordinates and hosts.
There is no assumed reduced graph, exact graph degree, grid-match map,
or graph-point equation in this final common-quotient exclusion.

This is recorded as improvement P1-MATH-0109, a simplification of the
transition between Steps 5 and 6. The geometric arguments providing
nonconstant/transcendental x, the common-quotient constants from equal
divisors, and the exceptional-equation bound remain explicit open
work. Genus, Riemann--Hurwitz, reduced-fibre/divisor arguments,
geometric dimension versus source prime height, intrinsic line-bundle
degrees and the external uniform point counts are not claimed proved.
T1.7 stays in_progress, coverage stays 79/167, confirmed improvements
become 109, and Palomar remains deferred. Original manuscript bytes
and the Lean/Mathlib pins are unchanged.

Verified with Lean v4.36.0-rc2: full build 12421 jobs, direct axiom audit of 8740 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 6639 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 14.99 GiB.


## Actual affine-curve equation, fraction field, and common-quotient exclusion

The common-quotient exclusion now applies to the actual coordinate
domain F[X,Y]/(C) and its actual fraction field, for an irreducible
plane equation C over any characteristic-zero field. The generic
coordinates are constructed from the quotient and fraction maps;
their actual evaluation kernel is proved to be the principal ideal
(C). Positive degree in Y proves the first coordinate transcendental.
Every actual integral point satisfying C(X,Y)=0 gives the exact kernel
containment needed to specialize the constructed graph equation.
Thus neither transcendence of an abstract coordinate nor an assumed
coordinate-ideal containment remains in the actual-curve cutoff.

The graph relation p(X)-Y*q(X) is proved irreducible when p,q are
coprime and q is nonzero. A relation in the actual curve function
field makes C divide this polynomial, so the actual irreducible C is
associated to the graph relation. Its degree in Y is proved exactly
one, and its points are proved exactly equivalent to the cross-
multiplied graph equation. This identifies the actual plane equation,
rather than only supplying a rational function with selected matches.

Both generic coordinates are proved to generate the entire actual
fraction field: every fraction is represented by quotient classes of
two actual bivariate polynomials. When the second coordinate satisfies
the graph relation, the first coordinate alone generates that field.
An actual F-algebra equivalence with RatFunc F is constructed, sending
the rational indeterminate to the actual first coordinate.

The explicit admissible-integral-point bound and the critical-band
exclusion are assembled for this actual curve equation and actual
fraction field. The large-scale threshold precedes the coefficient
field, the curve equation, all equation data, constants and hosts.
Curve-coefficient height and auxiliary coefficient height do not
enter it. The remaining geometric input is still the common-quotient
identities and the bounded exceptional set. Their derivation from the
original radical source curve, its genus/branching/divisor theory,
and the final uniform point counts remain open. Rationality here
concerns the plane image's function field, not the function field
of the radical source cover. This extends P1-MATH-0109; it adds no
new numbered coverage or separate finding. Coverage stays 79/167,
confirmed improvements stay 109, T1.7 stays in_progress, and Palomar
remains deferred. Original sources and compiler/dependency pins are
unchanged.

Verified with Lean v4.36.0-rc2: full build 12431 jobs, direct axiom audit of 8759 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 6665 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 14.97 GiB.


## Quantitative square-class descent and even actual line-projection degree

A quantitative square-class descent theorem is now proved. For
independent nonzero square classes over a characteristic-zero field
K whose images become squares in E, the actual independent radical
tower embeds in E. Therefore 2^r divides the actual degree [E:K],
where r is the number of independent classes. The actual linear map
on field square classes is constructed from the unit map and the
quotient by doubles. Its entire kernel is proved finite-dimensional
for every finite extension, and 2^(dimension of that kernel) divides
[E:K]. In particular its dimension is at most floor(log_2 [E:K]).
Finiteness of the kernel is proved, not assumed as an extra input.

The odd-degree consequence is proved separately in every
characteristic: a nonsquare acquiring a square root forces 2 to
divide the actual field degree, by the actual two-dimensional
quadratic algebra and the tower law. Hence every odd-degree field
extension reflects squares. This assertion needs no characteristic-
zero assumption and no asserted field isomorphism.

The odd-degree reflection is transported through the actual graded
projective function-field degree comparison and actual chart maps.
The literal radical equations consequently descend on graph-line
and vertical-line charts whenever the actual source-to-image field
degree is odd. Their actual polynomial restrictions are squares in
the corresponding rational-function fields. The selected-value
independence and direct-sum obstruction excludes both cases at the
actual admissible integral host. Exhaustive classification of the
actual homogeneous linear image then proves that every source
projection onto a line through such a host has even actual field
degree. The line, host, nonzero coefficients, selected nonempty
disjoint root families, positivity and both injectivity assumptions
remain explicit. The former degree-one theorems are corollaries
of these stronger results and retain their existing statements.

This is improvement P1-MATH-0110: Step 3's degree-one obstruction
extends to every odd projection degree, and the general square-class
kernel receives a quantitative degree bound. It does not replace the
remaining higher-curve genus/branching/divisor arguments, exceptional-
equation estimates or external uniform point counts. T1.7 remains
in_progress, numbered coverage stays 79/167, confirmed improvements
become 110, and Palomar remains deferred. Original manuscript bytes
and the Lean/Mathlib pins are unchanged.

Verified with Lean v4.36.0-rc2: full build 12445 jobs, direct axiom audit of 8787 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 6695 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 14.95 GiB.


## Rational square graphs: actual pole deletion, arbitrary-degree interpolation, and odd-extension exclusion

The odd-degree descent now also gives a checked arithmetic
exclusion for every bounded-degree rational graph. This route takes
the actual split-product radical equations in an actual field
extension of F(T), whose degree is odd; it does not assume common
quotients, an exceptional-equation budget or interpolation matches.
Odd-degree reflection makes the literal rational functions
c_nu product(T+i)*(p/q+j_nu) squares in the actual fraction field.

Clearing the actual nonzero denominator squared and reflecting
squares to F[T] yields a polynomial square. Its derivative vanishes
at each selected root. The split root is proved simple, so whenever
q(-i) is nonzero this forces p(-i)=-j_nu*q(-i). The actual equations
whose selected root sets meet a denominator zero are constructed;
disjointness gives an injection into the actual roots of q and
proves that at most deg(q) equations are lost. No assumed pole-
exclusion set or assumed cardinal estimate is used.

If d=max(deg p,deg q) is at most E and there are at least 3E+1
equations with disjoint nonempty root sets of a common cardinality,
the actual survivors supply 2d+1 distinct offset abscissae. The
requested grid selection is constructed for arbitrary grid size,
so the root-family cardinality need not equal d. The constant graph
case is itself excluded by one radical equation and positivity at
the actual host; positive graph degree is derived, not assumed.
Actual rational descent then gives the preceding explicit offset-
only abscissa bound. One critical-band threshold works for every
d<=E, and is chosen before both coefficient/extension fields, the
root-family degree, the graph coefficients, all radical coefficients,
all selected data, the odd extension degree and all hosts.

The final statement uses actual radical roots in the specified odd-
degree extension and the actual integral graph-point equation. The
transport from a general source curve to such a rational image is
not assumed established. Even-degree extensions and nonrational
images still require further geometry. This extends P1-MATH-0110;
it adds no numbered coverage or separate finding. T1.7 remains
in_progress, coverage stays 79/167, confirmed improvements stay 110,
and Palomar remains deferred. Original source bytes and pins are
unchanged.

Verified with Lean v4.36.0-rc2: full build 12461 jobs, direct axiom audit of 8804 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 6714 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 14.93 GiB.


## Actual curve radical transport and eventual even rational-image cover degree

The odd-degree rational-image exclusion is now transported from
the rational-function presentation to an actual irreducible plane
curve equation and its actual fraction field. An explicit F-algebra
equivalence from FractionRing F[T] to that curve field is constructed
for a supplied reduced graph presentation in its actual generic
coordinates. Its value on every polynomial is proved to be actual
evaluation at the generic first coordinate. The actual rational
quotient is proved to equal the generic second coordinate.

The literal scaled split-radical polynomial c*P_I(X)*(Y+j) is
transported exactly to the rational-graph function used in the
preceding pole-deletion argument. Squarehood is equivalent under
this actual field equivalence. Thus actual radical roots in an
actual odd-degree extension of the curve field provide the precise
functional squares; no unidentified scalar map or separately assumed
functional-square premise remains. The host graph equation follows
from the actual point condition C(X,Y)=0 by the proved identification
of C with its reduced graph relation.

The final uniform statement excludes actual integral curve points
under the literal radical equations in that odd-degree cover. Its
threshold precedes the curve equation, both fields, all reduced
graph coefficients, the radical roots and coefficients, the common
root-family degree and the host data. The graph's maximum degree
is bounded by E; it is not required equal to the root-family degree.
A corresponding theorem states the actual finite cover degree must
be even at every such sufficiently large admissible host.

This extends P1-MATH-0110 without a new finding or numbered result.
It does not assert that a general source curve has a graph image,
nor identify all source-scheme cover maps with this affine fraction-
field presentation. The even-degree and non-graph image geometry,
general degree comparisons and external uniform point counts remain
open. T1.7 stays in_progress, coverage stays 79/167, confirmed
improvements stay 110 and Palomar remains deferred. Original sources
and the compiler/dependency pins remain unchanged.

Verified with Lean v4.36.0-rc2: full build 12467 jobs, direct axiom audit of 8811 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 6722 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 14.91 GiB.


## Bounded radical covers force graph images through actual square-class kernels

A new algebraic route proves the graph-image conclusion in the
nonconstant-coordinate branch of Step 5, including even cover degrees.
Let C be an actual irreducible integer plane equation of positive
degree in both coordinates, K its actual quotient fraction field,
and L an actual finite extension containing the literal scaled
radical roots d_nu*P_I_nu(X)*(Y+j_nu). The integer coefficients are
nonzero, the selected first-root sets are disjoint and nonempty,
and the singleton second offsets j_nu are distinct.

The actual square-class map from binary equation selectors is
constructed. Its image lies in the actual square-class kernel for
L/K, so its rank is at most log_2[L:K]. A finite linear argument
proves that on a subspace of codimension s, at most 2s coordinate
forms vanish or coincide with another coordinate form. The actual
remaining nonzero distinct coordinate forms separate one selected
equation from every other equation by a kernel word.

The formal-branch matching argument is extended to every actual
nonzero integer scalar multiplying a word. For a good coordinate,
every root of every regular selected first fibre must equal that
equation's own second offset: one kernel word gives an offset match,
and a second word selecting this equation while omitting a proposed
different equation rules out every other match. The existing actual
separability and exact fibre-root count then prove deg_Y(C)=1.
No genus, Riemann--Hurwitz, divisor-constant or common-quotient
hypothesis is used in this conclusion.

The exceptional equation sets are constructed. Disjoint first-root
sets give an actual injection of equations meeting bad first fibres
into the actual critical-offset set. The total loss is at most
2 floor(log_2[L:K]) plus the cardinality of that critical set, bounded
by deg_X(C)+2 deg_X(C)deg_Y(C). If both partial degrees and the actual
cover degree are at most E and there are at least 4(E+1)^2 equations,
the actual good family has at least 2E+1 equations. Each selected
offset in every good equation is proved an actual integer point
C(-i,-j_nu)=0, and the plane image is proved a graph.

This is improvement P1-MATH-0111, an alternative to the genus and
common-quotient part of Step 5 for the stated nonconstant-coordinate
and bounded-degree presentation. It has not yet supplied the general
source-scheme identification, bounds comparing the actual ordinary
ambient curve degree to both image and extension degrees, the
constant-coordinate cases, or the complete subsequent graph
interpolation for arbitrary cover degree. Those and the external
uniform point counts remain open. T1.7 stays in_progress, numbered
coverage stays 79/167, confirmed improvements become 111 and Palomar
remains deferred. Original sources and pins remain unchanged.

Verified with Lean v4.36.0-rc2: full build 12483 jobs, direct axiom audit of 8845 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 6771 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 14.90 GiB.


## Actual reduced graph construction and complete nonconstant bounded-cover exclusion

The new bounded-cover argument is now connected through actual
reduced rational interpolation to a uniform large-scale exclusion.
For an actual irreducible integer plane equation C with deg_Y(C)=1,
the original rational numerator and denominator are constructed from
its actual coefficients. The denominator is proved nonzero at every
actual integer curve point: otherwise both coefficients vanish at
the integer first coordinate, forcing a forbidden vertical factor
of the irreducible equation. No coefficient-height bound is used.

The actual quotient is canonically reduced using its rational-
function numerator and denominator. Their coprimality and nonzero
denominator are supplied by the actual rational-function data.
Both degrees cannot increase under reduction, and the exact
cross-product identity transports every actual curve point and
selected offset match to the reduced pair. Thus its maximum degree
is bounded by deg_X(C), without separately assuming the original
integer coefficient polynomials coprime. One offset match and host
positivity exclude a constant reduced graph.

Combining this construction with the actual good equation family
proves an offset-only abscissa bound for every finite cover degree,
including even degrees. If both positive plane partial degrees and
the actual finite cover degree are at most E, there are at least
4(E+1)^2 literal radical equations, first-root families are disjoint
of a common positive cardinality and singleton second offsets are
distinct, the actual good families supply the reduced graph's
2n+1 interpolation points with 1<=n<=E. The root-family cardinality
is not required equal to n. The original radical coefficients are
arbitrary nonzero integers.

A single critical-band threshold, chosen before the integer curve
equation, all its coefficients, the actual extension field, the
literal radical roots and coefficients, all offsets and root-family
degrees, excludes every actual admissible comparable integral point
on that curve. This statement has no genus, Riemann--Hurwitz,
common-quotient, assumed graph, supplied grid, exceptional-set count,
odd-degree, or graph-coefficient-height premise. All those algebraic
and arithmetic constructions for the stated nonconstant-coordinate
presentation are proved internally.

This extends P1-MATH-0111. The constant-coordinate image cases,
general source-scheme identifications, comparisons between ordinary
ambient curve degree and the actual plane/field degree bounds, and
the external uniform point counts remain open. The numbered T1.7
geometric count is not marked complete. Coverage stays 79/167,
confirmed improvements stay 111 and Palomar remains deferred.
Original manuscript bytes and compiler/dependency pins are unchanged.

Verified with Lean v4.36.0-rc2: full build 12493 jobs, direct axiom audit of 8859 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 6788 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 14.88 GiB.


## Actual constant-coordinate charts and uniform exclusion of all bounded radical covers

The actual-plane/finite-cover exclusion now includes both
constant-coordinate image branches. Over every characteristic-zero
integrally closed domain, the actual fraction-field square classes
of nonzero scalar multiples of disjoint nonempty univariate split
products are proved independent. This includes the integer
coefficient polynomial ring itself. The corresponding literal
radical roots in an actual extension force 2^k to divide its actual
field degree; in a finite extension this gives 2^k <= [L:K].

For an actual irreducible integer plane equation with an integer
point, zero Y partial degree forces its ideal to be the actual
vertical line through that point; zero X partial degree similarly
forces the horizontal line. The actual quotient coordinate rings
are constructed as polynomial rings over Z by explicit kernel and
surjectivity proofs. Their fraction-field equivalences are
constructed and proved to transport every literal specialized
polynomial. No separately supplied rational parametrization or
square-class independence premise is used.

On the vertical line the scalar coefficient is the original
nonzero integer radical coefficient times the selected first split
product at the actual integer point. Host positivity proves it
nonzero, and the distinct singleton second offsets give independent
univariate classes. The horizontal line has the symmetric argument
using disjoint nonempty first-root families and positivity at the
second coordinate. Thus neither constant-coordinate image can
support the bounded actual cover when k >= E. Both positive partial
degrees are derived internally before invoking the nonconstant
graph/interpolation exclusion.

The combined theorem chooses one critical-band threshold before
the actual integer curve, its coefficients, extension field,
literal radical roots, offset families, root-family degree and
hosts, and excludes all actual bounded-plane/field presentations
under the previously explicit degree bounds. This includes every
finite cover degree, with no genus, Riemann--Hurwitz, odd-degree,
assumed graph, supplied grid, coefficient-height or constant-
coordinate restriction.

This extends P1-MATH-0111. General source-scheme identifications,
comparisons between ordinary ambient curve degree and the actual
plane/field degree bounds, and external uniform point counts remain
open. T1.7 stays in_progress, numbered coverage stays 79/167,
confirmed improvements stay 111 and Palomar remains deferred.
Original manuscript bytes and compiler/dependency pins are unchanged.

Verified with Lean v4.36.0-rc2: full build 12503 jobs, direct axiom audit of 8887 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 6822 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 14.86 GiB.


## P1-MATH-0112 — Actual ordinary-to-weighted curve Hilbert degree comparison

A literal homogeneous algebra comparison now connects the ordinary
affine-projective embedding in Step 5 to the weighted source used
in the existing degree formula. The substitution fixes X,Y,Z and
sends each weighted radical coordinate w to Z^(D-1)w. A polynomial
of weighted degree n maps to an ordinary homogeneous polynomial of
degree n. When 2<=g=|I|+|J|<=2D, each actual weighted radical
relation maps exactly to Z^(2D-g) times the ordinary homogeneous
relation w^2 Z^(g-2)-c P_I P_J.

An actual homogeneous prime ideal Q of the ordinary polynomial ring
containing these literal relations therefore constructs an actual
map from the weighted radical coordinate algebra. Restricting its
actual Veronese map and quotienting by its actual kernel constructs
the source prime P. Its primality and homogeneity are proved. The
actual quotient map is injective and sends every source piece n
into the ordinary quotient piece D*n. If Z is not in Q, its actual
nonvanishing D-th power constructs a relevant source projective
point with precisely this ideal P.

A numerical Hilbert-slope comparison is proved from the constructed
injections, not supplied as a degree inequality. If the ordinary
curve quotient has actual Hilbert polynomial E*n+beta, the actual
source slope is at most D*E. Combined with the proved finite-rank
projection slope, the extracted plane degree times the actual
cover rank is at most E. In particular each is at most E. For the
constructed source projective point with height(P)=1, its own
irreducible homogeneous plane equation is extracted internally,
and the bound is transported to the actual projective function-
field extension degree through the previously proved comparison.
No plane equation, cover rank inequality, supplied Hilbert-piece
dimension inequality, coordinate-degree comparison or coefficient
height bound is an input to this final extraction theorem.

The ordinary Hilbert polynomial and the height-one condition on
the constructed P remain explicit geometric hypotheses. Their
identification with every curve supplied by the external covering
theorem, the integer affine-equation/fraction-field identification,
and the external uniform point counts remain open. This is the
confirmed proof improvement P1-MATH-0112; it does not claim the full
ordinary-curve exclusion or T1.7. Numbered coverage stays 79/167,
confirmed improvements become 112 and Palomar remains deferred.
Original manuscript bytes and compiler/dependency pins are unchanged.

Verified with Lean v4.36.0-rc2: full build 12515 jobs, direct axiom audit of 8917 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 6864 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 14.84 GiB.


## Actual integer models, quotient-field equivalences and rational-plane radical-cover exclusion

The actual rational plane-curve presentation is now connected to
the integer plane/cover exclusion. A generic actual-localization
argument lifts an irreducible localized element to an irreducible
element of the original unique-factorization ring, up to actual
association. Applied to the two integer polynomial variables and
the explicit nonzero integer coefficient denominators, it constructs
an irreducible integer equation associated to any actual
irreducible rational plane equation. Its integer points agree
exactly, and its partial degrees are bounded by the rational
equation's corresponding partial degrees. No separately supplied
primitive integer model or coefficient-height estimate is used.

The actual localized prime-quotient fraction fields are proved
equivalent. The integer principal curve ideal maps to the rational
principal ideal, and the denominator set is proved disjoint from
the integer ideal because the rational ideal is proper. The
constructed integer/rational function-field equivalence preserves
every literal specialized integer polynomial. In particular square
status and the actual scaled radical functions are transported.

An explicit base-field equivalence transports the actual extension
algebra, preserves its actual finrank exactly, and preserves finite
dimension. The literal radical roots in the supplied rational-
curve extension therefore give the literal radical roots over the
constructed integer model, with exactly the same degree bound.
The final theorem chooses a single critical-band threshold before
the rational plane equation, all its coefficients, its actual
finite extension, radical roots and integer coefficients, offsets,
root-family cardinality and integer host. It excludes all admissible
comparable hosts under the explicit rational partial-degree and
actual finite-cover-degree bounds, including constant-coordinate
images and even cover degrees. Every model and scalar transport in
this rational-to-integer bridge is constructed internally.

This extends P1-MATH-0111 and P1-MATH-0112. Still open are the
actual projective-source/affine-curve field identification for the
extracted plane equation, its affine irreducibility and degree
comparison through the chosen chart, the ordinary geometric
curve-to-height-one/Hilbert identification, and the external
uniform counting inputs. T1.7 stays in_progress, numbered coverage
stays 79/167, confirmed improvements stay 112 and Palomar remains
deferred. Original manuscript bytes and pins are unchanged.

Verified with Lean v4.36.0-rc2: full build 12531 jobs, direct axiom audit of 8941 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 6896 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 14.82 GiB.


## Actual homogeneous charts, constructed projective field covers and source-curve exclusion

The alternative Step 5--6 exclusion is now proved on the actual
projective radical source, with no supplied affine presentation,
extension field, cover-degree bound or literal radical roots.
For a homogeneous irreducible plane equation, its actual nonempty
Z-chart quotient is constructed and proved a domain. Its literal
affine specialization is nonzero and irreducible. Both actual
affine partial degrees are bounded by the homogeneous degree;
the proof uses the actual coefficient specialization and variable
swap, with no coefficient-height hypothesis.

A generic finite graded projection and actual chart equivalence
construct a finite extension of the actual chart fraction field.
The extension carrier is the actual projective source function
field. Its degree is proved equal to the actual graded module
rank, and the supplied homogeneous quadratic relations construct
the literal roots in that field. Applying this to the actual
source prime quotient and actual native Veronese chart transports
every actual radical polynomial to the actual affine curve
quotient, not merely its abstract square class.

For an actual height-one projective source point with Hilbert
multiplicity at most D*E, its own irreducible homogeneous plane
equation is extracted and its plane degree and actual source cover
rank are at most E. Actual containment of the affine image ideal
in the host evaluation kernel proves the Z-chart nonempty, the
extracted equation not at infinity, and the literal affine host
equation. Thus all hypotheses of the rational-plane radical-cover
exclusion are derived from the actual source data.

The final theorem chooses a single critical-band threshold before
the actual radical-source equations and nonzero integer
coefficients, D, offsets, projective point, curve-height proof,
Hilbert bound, offset family degree and integer host. It excludes
all admissible comparable hosts on every actual height-one source
curve of Hilbert multiplicity <=D*E when k>=4(E+1)^2. Constant-
coordinate images and all finite cover degrees are included.
No genus, Riemann--Hurwitz, assumed graph, supplied affine equation,
supplied field presentation, assumed cover rank or supplied radical
root is a premise of this final actual-source statement.

This extends P1-MATH-0111 and P1-MATH-0112. The ordinary geometric
curve-to-height-one/Hilbert identification and the external uniform
surface and curve point counts remain open. The ordinary quotient
comparison has already been proved separately, and its final host
and multiplicity composition with this source theorem remains to
be completed. T1.7 stays in_progress; numbered coverage stays 79/167,
confirmed improvements stay 112 and Palomar remains deferred.
Original manuscript bytes and compiler/dependency pins are unchanged.

Verified with Lean v4.36.0-rc2: full build 12545 jobs, direct axiom audit of 8960 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 6920 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 14.79 GiB.


## Actual ordinary host and Hilbert comparison complete the source exclusion

The actual ordinary prime quotient now supplies the complete
input to the actual projective-source exclusion. Its ordinary
Hilbert polynomial E*n+beta bounds the induced source Hilbert
multiplicity by D*E, using the actual graded injection and the
actual plane-degree times cover-rank comparison. An actual
ordinary affine host evaluation, with Z=1 and Q in its kernel,
proves the source Z-coordinate nonzero and the actual source
image ideal contained in the host kernel.

The final ordinary-curve theorem chooses its critical-band
threshold before all radical equations, integer coefficients,
ordinary prime ideals, Hilbert constant terms and hosts. For
k>=4(E+1)^2 it excludes every admissible comparable host under
the explicit induced source-height-one and actual ordinary
linear-Hilbert hypotheses. It internally constructs the source
point, source degree cap, image containment, irreducible affine
equation and actual projective function-field radical cover.
Both constant-coordinate cases and all finite cover degrees
are included. No supplied source point, affine presentation,
cover, roots, degree cap or genus premise remains.

This completes the previously open ordinary host/multiplicity
composition in P1-MATH-0111 and P1-MATH-0112. The general geometric
curve-to-induced-source-height-one and ordinary linear-Hilbert
identification, and external uniform surface/curve counting
inputs, remain open. T1.7 stays in_progress, numbered coverage
stays 79/167, confirmed improvements stay 112 and Palomar remains
deferred. Original manuscript bytes and pinned dependencies are
unchanged.

Verified with Lean v4.36.0-rc2: full build 12551 jobs, direct axiom audit of 8964 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 6924 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 14.77 GiB.


## Actual inverse homogenization and ordinary/source quotient chart isomorphism

The actual ordinary and weighted radical equations are proved
to define exactly the same quotient after Z=1. The two defining
ideals plus the literal ideal (Z-1) are equal. The forward weighted
substitution is the identity after every Z=1 ring evaluation.

The literal inverse homogenization sends each base variable V
to Z^(D-1)*V and leaves each radical variable unchanged. It sends
ordinary homogeneous degree n to weighted degree D*n. Composing
with the forward substitution multiplies an actual homogeneous
ordinary polynomial by Z^((D-1)*n). The inverse homogenization
is also the identity after every Z=1 evaluation.

For every actual homogeneous ordinary ideal containing the radical
relations, its induced source quotient and its ordinary quotient
now have an explicitly constructed isomorphism of their actual
Z-coordinate charts. The map is the actual coordinate map on
dehomogenized elements; its inverse is built from the literal
inverse homogenization. Injectivity clears powers of Z using the
actual quotient-to-ordinary injection. No primality, domain,
dimension, curve-height, Hilbert or nonzero-coordinate premise
is required for this chart isomorphism. It includes nonreduced
quotients and empty charts.

This strengthens the ordinary-to-source identification supporting
P1-MATH-0112. It does not yet prove equality of ambient prime
heights: the full localized ambient-ring comparison and its prime
height transport remain to be established. The geometric linear
Hilbert identification and external uniform counting inputs also
remain open. T1.7 stays in_progress; numbered coverage stays
79/167, confirmed improvements stay 112 and Palomar is deferred.
Original manuscript bytes and pinned dependencies are unchanged.

Verified with Lean v4.36.0-rc2: full build 12559 jobs, direct axiom audit of 8986 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 6961 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 14.76 GiB.


## Actual ambient ordinary/source height equality and surface-curve exclusion

The ambient ordinary-to-source prime-height comparison is now
proved. A generic bijective homogeneous coordinate chart map
induces a bijection on the full localized rings, including rings
with zero divisors. The proof clears denominators of actual
homogeneous components. This comparison persists in every
positive Veronese ring: the clearing exponent is made divisible
by D while preserving the actual homogeneous preimage degree.
An actual ring isomorphism after inverting a coordinate preserves
the heights of all primes meeting that chart.

The actual ordinary radical surface is the quotient by the
literal ordinary radical relations. Its grading is constructed.
Equality of the weighted and ordinary defining ideals after
Z=1 proves that the actual forward coordinate map on the two
ambient charts is bijective. The generic localization and
Veronese results therefore apply to the actual ambient map,
not only to the previously compared curve quotients.

For an actual homogeneous ordinary prime Q containing the
radical relations, the prime in the actual ordinary surface
Veronese ring is constructed as the kernel of its actual curve
evaluation quotient map. Its contraction is proved equal to the
previously constructed source ideal. Whenever Z is outside Q,
the two actual ambient prime heights are equal.

The final uniform ordinary-surface-curve exclusion now assumes
height one only of the prime in the actual ordinary radical
surface. Height one of the induced source is derived internally.
Its actual ordinary Hilbert polynomial E*n+beta bounds all
required source, plane and cover degrees. The final statement
supplies neither an induced source-height hypothesis nor a
source point, affine equation, cover field, root or cover bound.
Its threshold is uniform before all actual ideals, equations,
integer coefficients and hosts. All coordinate cases and finite
cover degrees are included.

This closes the algebraic ambient height bridge in P1-MATH-0112
and strengthens the exclusion recorded in P1-MATH-0111. The
identification of exceptional curves from a geometric uniform
covering theorem with these actual prime/Hilbert data, and the
external uniform covering and point-counting inputs, remain
open. T1.7 stays in_progress; numbered coverage remains 79/167,
confirmed improvements remain 112 and Palomar is deferred.
Original manuscript bytes and pinned dependencies are unchanged.

Verified with Lean v4.36.0-rc2: full build 12575 jobs, direct axiom audit of 9012 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 6996 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 14.74 GiB.


## Actual simultaneous degree gap and conditional ordinary surface point counts

One coefficient-uniform critical threshold now excludes all
ordinary degrees up to a chosen cap E simultaneously. The actual
Hilbert slope e is arbitrary: every actual ordinary surface curve
through an admissible host has e>E. This follows from the actual
source multiplicity bound D*e and the previously proved uniform
source exclusion with cap E.

Normalized integral points are actual integer coordinate functions
on Fin 3 plus the radical indices, with Z=1. Their bounded box
and their actual ideal-kernel point subsets are finite sets.
Projection gives the integer host (X,Y); chosen literal radical
lifts inject hosts into the point set. An actual curve record
contains its prime homogeneous ideal, literal relations, actual
ordinary surface height one, positive degree and actual linear
Hilbert polynomial. The degree is proved unique for its ideal.

The geometric counting inputs are isolated as two unproved
properties, always explicit theorem arguments. The uniform curve
input bounds the actual normalized integer-point set by
A*H^(1/e+delta), uniformly over bounded ambient dimensions and
bounded actual degrees. Its literature source is
[Pila, Theorem A, Astérisque 228 (1995), pp. 183--187](https://www.numdam.org/item/AST_1995__228__183_0.pdf).
The uniform lifted-surface input produces actual finite exception
sets and actual ordinary curve records of bounded degree. Its
curve-number and exception exponents are 1/sqrt(2^k)+delta and
2/sqrt(2^k)+delta. It includes the unproved finite-projection
lifting and prime/Hilbert presentation needed to apply
[Salberger, arXiv:2311.05561v1, Lemma 2](https://arxiv.org/pdf/2311.05561v1).
Neither property is an axiom or a proved external counting theorem.

Given an actual finite covering of admissible point sets, the
proved degree gap discards every curve of degree <=E. The explicit
curve input bounds the remaining contributions by
#exceptions + #curves*A*H^(1/(E+1)+delta). Fixed choices of E, k
and delta are constructed before N so that both surface-cover
exponents, after the polynomial height H<=B0*N^q, are <=epsilon/2.

The resulting theorem proves N^epsilon bounds for the actual
normalized point sets and their actual projected integer hosts,
conditional only on the two stated uniform geometric properties.
It chooses the equation threshold before the ambient-size cap,
then its count constant and critical cutoff before all actual
equations, coefficients, offsets, point sets and heights. The
finite coverings, degree cut and actual point counts are composed;
the desired N^epsilon host bound is never an input.

The external properties themselves and their geometric translation
remain unproved. The literal dyadic square-equation host/height
composition, the general N^(1/2+epsilon) geometric bound and the
remaining graph consequences of T1.7 still need to be completed.
T1.7 stays in_progress; numbered coverage remains 79/167, confirmed
improvements remain 112 and Palomar is deferred. Original manuscript
bytes and pinned dependencies are unchanged.

Verified with Lean v4.36.0-rc2: full build 12593 jobs, direct axiom audit of 9032 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 7026 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 14.70 GiB.


## Literal integer square-equation hosts and equation-count-independent height

The literal integer square-equation host and point-height
composition is now proved. Evaluating the actual native linear
products and ordinary radical relations at (Y,X,Z,w)=(y,x,1,w)
gives exactly the original integer split-product equations.
Their integer roots therefore put the literal lift in the actual
ordinary radical surface ideal kernel.

For fixed D>=1 with A0+K<=2D, every ordinary coordinate of a
literal dyadic root lift is bounded by
(2^D+3^K)*N^D. This height constant is independent of the number
of equations. It uses the individual radical bounds rather than
the larger common constant needed for the sum-of-radicals
projection. The natural floor of this real height is proved >=1,
no larger than the real height, and contains the actual integer
lift in the actual finite normalized point set.

The final theorem starts with arbitrary nonzero integer
coefficients of height <=N^A0, disjoint offset sets of common
positive size a and distinct singleton offsets on the Y side.
It counts an arbitrary finite set of actual integer hosts for
which the literal square equations have integer roots. The hosts
have X in the dyadic range, |Y|<=2N, positive selected values,
an injective actual left even-selection map and actual left/right
square-class images in direct sum. The offset cap is any fixed
polynomial in the critical logarithmic window.

The proof derives the offset bound <=N from the critical scale,
constructs a choice of literal integer roots for each host, lifts
the actual host set to the actual bounded ordinary point set,
and proves that projection recovers exactly the original host
set. The preceding conditional point-count theorem then gives
the coefficient-uniform A*N^epsilon host bound. The equation
threshold is chosen before the ambient-size cap, and A and the
N cutoff before every actual system, coefficient and host set.
Choosing a suitable fixed D from A0 and K is also proved.

Only the two previously isolated uniform geometric properties
remain explicit unproved arguments in this literal per-system
degree-(a,1) result. No abstract host-count or point-height
conclusion is a premise. Coefficient smoothness is not used and
coefficient enumeration is not included. The general half-power
geometric bound, the graph applications with their own alignment
scope, and the external geometric input proofs remain open.
T1.7 stays in_progress; numbered coverage remains 79/167,
confirmed improvements remain 112 and Palomar is deferred.
Original manuscript bytes and pinned dependencies are unchanged.

Verified under Lean v4.36.0-rc2: full build passed (12599 jobs); direct axiom audit passed for 9043 declarations using only propext, Classical.choice and Quot.sound; all 7039 distinct ledger/evidence declaration references checked; source-integrity and whitespace checks passed; Ubuntu free space 14.68 GiB.


## Repeated left offsets remove host independence from the conditional count

For every fixed left size a>=2, the literal degree-(a,1)
coefficient-uniform N^epsilon host bound now requires no actual
square-class independence or direct-sum hypothesis on the host.
The two explicit unproved uniform geometric properties remain
arguments, with precisely the same quantifier order and scope.

The strengthened terminal graph argument first proves an
independence-free alternative: an integral point on a reduced
rational graph selected by a bounded offset grid either has the
existing offset-only bound, or the entire rational graph is an
actual affine line. For the latter alternative, one good family
contains two distinct left roots with the same right root.
Their affine equations force slope zero. The actual host would
then satisfy Y+j=0, contrary to positivity. Neither the actual
left even-selection map nor the actual left/right class spaces
is used in this contradiction.

This repeated-left argument is composed through the actual
integer and rational plane covers, including constant-coordinate
images, the actual projective source curve, ambient prime height,
ordinary Hilbert multiplicity and the simultaneous ordinary
degree gap. It then supplies the actual finite curve-cover count,
conditional surface point count and literal integer-root host
count with admissibility consisting only of the dyadic bounds
and positivity of the selected values. The proof covers even
finite radical-cover degrees and arbitrary nonzero integer
coefficients of bounded polynomial height. It does not assume
coefficient smoothness or include pattern enumeration.

This recovers the independence-free per-system scope needed
for the a>=2 part of the second graph consequence in T1.7.
The a=1 case with geometric nonalignment, the general half-power
bound, smooth coefficient-pattern enumeration and the two
external uniform geometric proofs remain open. T1.7 stays
in_progress; numbered coverage remains 79/167 and confirmed
mathematical improvements remain 112. This is a proof improvement,
not a confirmed manuscript-conclusion error. Palomar is deferred;
the original manuscript bytes and pinned dependencies are unchanged.

Verified under Lean v4.36.0-rc2: full build passed (12619 jobs); direct axiom audit passed for 9053 declarations using only propext, Classical.choice and Quot.sound; all 7051 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 14.64 GiB.


## The affine exception gives the actual source alignment

The positive-left-size degree-(a,1) host count now has an
independence-free nonaligned version, including a=1. It uses
actual integer hosts with both coordinates in the positive
dyadic range and excludes only a concrete bounded positive
coprime alignment. No even-selection injectivity or left/right
square-class directness is assumed.

The affine exceptional graph is handled constructively. Two
distinct bounded integer grid points and the actual host on the
same rational affine graph give an exact rational cross-product
identity, then its exact integer counterpart. The existing
bounded collinearity argument constructs positive coprime a,b
with a,b<=2B and |bX-aY|<=(a+b)B. The critical-window cutoff
ensures that both host coordinates exceed the offset cap B.
This discharges the affine alternative for every positive common
left size; the other graph cases retain the same offset-only
polynomial bound.

For the paper's offset cap B=L+1 and L>=1, the constructed
alignment is proved to imply the literal
CompressedTargetAlignment.Aligned 1 X.natAbs Y.natAbs L.
The final source_uniform_hosts theorem therefore assumes the
paper's actual nonalignment predicate, rather than a supplied
line-exclusion or graph-bound conclusion.

The argument is composed through the actual integer/rational
plane covers, projective source, ambient prime height and
ordinary Hilbert multiplicity, simultaneous degree gap, actual
finite curve-cover count, conditional surface point count and
literal integer-root lift. One cutoff is uniform before all
actual equations, coefficients, curves, covers and hosts.
The two previously isolated uniform geometric properties remain
explicit unproved arguments; the host-count target is not a
premise. Constant-coordinate images and even finite cover
degrees remain included.

Together with the repeated-left a>=2 version, this recovers
the per-system alignment scope needed by the second graph
consequence of T1.7. Smooth coefficient-pattern enumeration,
the general half-power geometric bound, and the external
uniform geometric proofs remain open. T1.7 stays in_progress,
numbered coverage remains 79/167, confirmed improvements remain
112, and Palomar is deferred. This is a proof improvement,
not a confirmed manuscript-conclusion error. Original manuscript
bytes and pinned dependencies are unchanged.

Verified under Lean v4.36.0-rc2: full build passed (12639 jobs); direct axiom audit passed for 9067 declarations using only propext, Classical.choice and Quot.sound; all 7069 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 14.60 GiB.


## Direct integer systems and a uniform fixed-subsystem reduction

The literal degree-(a,1) per-system host bound now has a
single direct statement with exactly the paper's alignment
scope. It starts only with finite integer systems d_i,I_i,j_i,
common positive left size a, disjoint left root sets, distinct
right offsets, coefficients of height <=N^A0, offsets <=L+1,
positive dyadic hosts and actual integer roots of
w_i^2=d_i*product_(z in I_i)(X+z)*(Y+j_i).
For a>=2 aligned hosts are permitted; only when a=1 does the
statement exclude the actual source alignment predicate.
Neither host square-class injectivity nor directness is assumed.

The proof chooses the homogenization degree from A0,K,
constructs the actual homogeneous radicand list and its index
equivalence, and constructs both selected-value sets. Positivity
of all selected values and L>=1 are deduced uniformly from the
critical scale and offset bounds. They are no longer supplied
premises. The two alignment cases share one equation threshold,
one host constant and one scale cutoff.

The stronger uniform_hosts_of_many statement selects the first
k equations from every larger finite system. Its host constant
and cutoff are therefore independent of the actual number of
equations. The two explicit unproved uniform geometric input
properties are needed only at the chosen fixed equation count
k, with arbitrary curve degree cap for the curve-count property.
The equation threshold is chosen before these properties; the
host constant and scale cutoff precede every actual system,
coefficient and finite host set. There is no supplied homogeneous
list, projective curve, field, cover, Hilbert polynomial,
height bound or target count in the final statement.

Only the two isolated uniform geometric properties remain
unproved explicit arguments in this direct per-system theorem.
Coefficient smoothness is unnecessary; summing smooth patterns,
the actual graph component-to-system reduction, the general
half-power bound and the external geometric proofs remain open.
T1.7 stays in_progress; numbered coverage remains 79/167 and
confirmed improvements remain 112. This strengthens the proof,
without a confirmed manuscript-conclusion error. Palomar is
deferred; original manuscript bytes and dependencies are unchanged.

Verified under Lean v4.36.0-rc2: full build passed (12643 jobs); direct axiom audit passed for 9072 declarations using only propext, Classical.choice and Quot.sound; all 7076 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 14.58 GiB.


## Actual smooth-pattern summation for degree-one systems

The actual offset and smooth coefficient-pattern summation
for degree-(a,1) systems is now proved. The finite pool consists
of k bounded-cardinality subsets of the integer offset interval,
k right offsets, and k subsets of the literal primes <=H.
Each coefficient is the positive product of its actual prime
support. Pool membership, positivity, offset bounds and the
coefficient bound <=4^H are proved directly.

The offset-pattern count is at most
(((K+1)*4^K*3)^k)*(L+1)^((K+1)*k).
The existing elementary Chebyshev support bound gives at most
N^epsilon prime-support patterns for every fixed k and every
H<=D*(L+1) in the critical band. Combining these proves the
unconditional N^epsilon bound for the entire actual finite pool.
No PNT assumption or new external estimate is used.
A fixed polynomial coefficient-height exponent is constructed
from D and the critical-band constant, uniformly before all
N,L,H,k,K and every actual support pattern.

SmoothDegreeOneHostCount.uniform_hosts sums the literal integer
host counts over the valid actual patterns. It chooses one fixed
k, then takes the two explicit unproved uniform geometric
properties only at that k. The constant and scale cutoff precede
a, N,L,H, every actual pattern and every finite host set. A host
need only admit some valid smooth split-product square system;
the witness pattern may vary with the host. Disjoint left sets,
distinct right offsets, common positive left size, actual integer
roots and the dyadic host bounds are checked in that witness.
Aligned hosts are permitted for a>=2; for a=1 only the literal
source alignment is excluded. No host independence or direct-sum
hypothesis is present, and no target count is a premise.

This closes the explicit smooth-pattern summation in the second
T1.7 graph consequence, conditional only on the two isolated
uniform geometric inputs. Extraction of these actual systems
from the literal graph components, the general half-power bound
and the external geometric proofs remain open. T1.7 stays
in_progress; numbered coverage remains 79/167 and confirmed
improvements remain 112. This is a proof improvement without a
confirmed manuscript-conclusion error. Palomar is deferred;
original manuscript bytes and pinned dependencies are unchanged.

Verified under Lean v4.36.0-rc2: full build passed (12649 jobs); direct axiom audit passed for 9085 declarations using only propext, Classical.choice and Quot.sound; all 7097 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 14.57 GiB.


## Actual degree-one graph components construct the counted integer systems

The literal two-window graph component-to-system extraction
is now proved. The graph is the actual largePrimeGraph with
cutoff 10*(L+1), and unpinned means the actual ComponentPinned
predicate. Its component indicator is proved to satisfy the
actual large-prime equations. The component product therefore
has no odd prime support above the cutoff. Its actual support
product is a positive smooth coefficient giving an integer
square prescription.

The component's two sets of integer offsets are constructed
from its literal left/right vertices using u.val-1. Their
cardinalities equal the actual numbers of vertices in each
window. Distinct components give disjoint offset sets on each
side. The actual component product is proved to be exactly
the product of the two offset polynomials at the actual starts.
When the right side has one vertex, this yields the literal
integer square equation with an actual integer root.

An injective choice of k actual unpinned components with left
size a and right size one constructs the full valid smooth
pattern witness. Selection from the actual finite component
set is proved internally; no system-extraction premise is used.
DegreeOneGraphHostCount.uniform_hosts then proves the actual
N^epsilon dyadic host bound, conditional only on the two explicit
uniform geometric properties at a fixed k. It assumes no actual
square-class independence, directness, supplied coefficient
height, square roots, curve, field or abstract host-count bound.
For a>=2 aligned hosts are included; for a=1 only the actual
source alignment is excluded.

The two ordered windows are both counted explicitly. The source
alignment is proved symmetric. A second theorem counts either
window order, and a pigeonhole version accepts a total of at
least 2k typed components across those two orders. All constants
and cutoffs precede actual dyadic starts, window lengths,
components and finite host sets. Formal vertex copies are kept
when the physical windows overlap.

This completes the actual degree-(a,1) graph-count composition
under the two isolated uniform geometric inputs, including the
previously proved finite smooth-pattern enumeration. The general
half-power geometric count and the proofs of the two external
uniform geometric inputs remain open. T1.7 stays in_progress;
numbered coverage remains 79/167 and confirmed improvements
remain 112. This is a proof improvement without a confirmed
manuscript-conclusion error. Palomar is deferred; original
manuscript bytes and pinned dependencies are unchanged.

Verified under Lean v4.36.0-rc2: full build passed (12657 jobs); direct axiom audit passed for 9109 declarations using only propext, Classical.choice and Quot.sound; all 7127 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 14.55 GiB.


## Literal integer points in the chosen weighted-source embedding

The general split-product integer-root system now constructs
an actual point of the weighted source and of its chosen
projective coordinate embedding. The construction permits
arbitrary disjoint nonempty left and right root sets; it is
not restricted to singleton right sets.

Literal integer square equations annihilate the actual weighted
relation ideal at Z=1. Quotient evaluation and its restriction
to the actual source Veronese are constructed. The chosen
projective generator index is identified with the actual degree-D
base monomials plus radical variables. Their point coordinates
are the literal integers X^u*Y^v and w_i. Polynomial evaluation
at those integers is proved equal to the actual source evaluation
composed with the chosen embedding presentation.

The Z^D coordinate is proved to be one. The X*Z^(D-1) and
Y*Z^(D-1) coordinates recover the exact original integer host.
The actual finite bounded normalized coordinate point sets and
their ideal-kernel membership characterization are constructed.
Every literal coordinate is bounded by (2^D+3^K)*N^D; this
constant is independent of the equation count. The floor of
this real height is proved >=1 and contains the actual point.

Embedded curve-ideal containment is proved equivalent to actual
source-ideal containment, using surjectivity of the actual
embedding presentation. It supplies the actual affine plane
host-image kernel. Thus the already proved source low-degree
exclusion applies directly to the literal embedded integer point
and gives chosen-coordinate Hilbert multiplicity at least 2D.
This includes constant-coordinate images, with both actual
selected-set even-selection maps injective and their actual
images in direct sum. No host-image or degree-bound conclusion
is assumed in this new point-containment composition.

These are unconditional algebraic and height bridges for the
general half-power count. That count itself remains open: its
finite surface-cover and uniform curve-count applications must
be made in this chosen weighted-source embedding, with their
exact uniformity. The two previously isolated ordinary-embedding
input properties alone have not been asserted to cover this
new setting. The degree-(a,1) graph composition remains proved
under those two explicit ordinary geometric inputs. T1.7 stays
in_progress; numbered coverage remains 79/167, confirmed
improvements remain 112 and Palomar is deferred. No manuscript
conclusion error is confirmed; source bytes and dependencies
are unchanged.

Verified under Lean v4.36.0-rc2: full build passed (12667 jobs); direct axiom audit passed for 9127 declarations using only propext, Classical.choice and Quot.sound; all 7154 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 14.53 GiB.


## One generic curve input and the actual source finite-cover count

A single explicit generic curve-count property now covers
both actual ordinary curves and actual curves in the chosen
weighted-source embedding. Its input data are a homogeneous
prime ideal, a positive rational degree, the actual linear
Hilbert polynomial, a normalized coordinate chart and an
integer height box. The ambient coordinate count and degree cap
are fixed before all curves, coefficients, charts and heights.

This generic UniformNormalizedCurvePointCount.UniformBound is
an UNPROVED ARGUMENT, not an axiom or a newly proved version of
Pila. It includes the primary curve theorem and its translation
to actual prime/Hilbert data, non-geometrically-integral curves
over Q and the normalized chart, including the height-one case.
Primary sources are Pila, Theorem A, Astérisque 228 (1995),
https://www.numdam.org/item/AST_1995__228__183_0.pdf , and the
integral projective curve formulation in P3 in Salberger,
https://arxiv.org/pdf/2311.05561v1 , Lemma 3. The higher-dimensional
ambient/prime-presentation translation is not claimed proved.

The specialization of this one property to the previous actual
ordinary curve-count property is proved. Its specialization to
the actual chosen source-embedding point sets is also proved.
The two applications are therefore derived from a single generic
curve input, rather than silently identifying incompatible
embeddings or introducing an unexplained new source count.

To construct the source curve data, actual finite graded module
rank gives the actual source Hilbert slope. Existence of its
Hilbert polynomial then gives an actual affine polynomial with
slope equal to its actual multiplicity. This is transported to
the chosen embedding by equality of actual piece dimensions.
The resulting chosen-coordinate degree is proved positive for
every actual height-one source projective curve. No degree,
Hilbert polynomial or positivity assumption is added to that
curve data: they are constructed from the actual point and its
height-one property.

SourceCurvePointCover.finite_cover_bound now counts literal
integer hosts from an actual finite collection of such curves.
Every curve meeting a covered admissible literal root point has
actual degree at least 2D, by the proved source-degree bridge.
Filtering to these curves and applying the generic curve input
gives #hosts <= #exceptional_points + #curves*A*H^(1/(2D)+delta).
Exact host recovery proves injectivity of the actual lift.
Both selected-set even-selection injectivities and their actual
direct sum remain explicit in this general source argument.

The covering collection and its exceptional set are actual data
in this intermediate theorem; a surface-cover theorem is not
assumed proved. The final general half-power estimate still
requires a uniform surface-cover application in the chosen
source embedding and the numerical/height composition. The
primary geometric input proofs remain open. The degree-(a,1)
graph composition remains valid under its explicit curve and
ordinary surface-cover inputs. T1.7 stays in_progress; numbered
coverage remains 79/167, confirmed improvements remain 112,
and Palomar is deferred. No manuscript-conclusion error is
confirmed; original source bytes and dependencies are unchanged.

Verified under Lean v4.36.0-rc2: full build passed (12683 jobs); direct axiom audit passed for 9144 declarations using only propext, Classical.choice and Quot.sound; all 7183 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 14.50 GiB.


## The general literal half-power composition under its exact geometric inputs

The general coefficient-uniform N^(1/2+epsilon) literal
integer host count is now proved under two explicit geometric
properties: the generic normalized curve-count property and a
new chosen-source uniform surface-cover property. The latter
is an UNPROVED ARGUMENT, not an axiom or an asserted Salberger
theorem. It includes the primary P3 surface covering and the
bounded projection, lifting, geometric-integrality, degree and
actual prime/Hilbert presentation translation for this chosen
higher-dimensional weighted-source embedding. It is kept
distinct from the previous ordinary-embedding cover property.
Its data are an actual finite exceptional point set and actual
height-one source curves of bounded degree; the desired host
count is not part of the property.

The proof constructs literal root lifts in the actual normalized
source point set, with height floor((2^D+3^K)*N^D), and proves
that they annihilate the actual global embedding ideal. The
actual source cover yields finite exceptional points and curves.
Every curve meeting a covered admissible host has actual chosen
coordinate degree at least 2D. The proved finite-cover count
therefore gives curve exponent 1/(2D)+delta. Choosing k large
and delta small before the systems makes the covering decay
and height conversion yield N^(1/2+epsilon). All numerical
exponent choices and cardinality compositions are proved.

GeneralRootHostCount.uniform_hosts constructs D and the actual
homogeneous radicand list directly from the raw integer data.
The stronger uniform_hosts_of_many selects a fixed first k
equations from every larger finite system. The constant and
scale cutoff are independent of the actual equation count and
precede every coefficient, root set and finite host set. Only
the geometric properties at that fixed k and chosen D are used.
The root sets on both sides may have different positive sizes;
only their common total-degree cap K is used. No equal-degree
pigeonhole assumption is needed. Coefficients are arbitrary
nonzero integers of height <=N^A0; smoothness is unnecessary.
Offsets may lie in any fixed polynomial enlargement of the
critical window. The actual two selected-set even-selection
maps, their direct sum and positivity are explicit host
hypotheses, as in the general per-system manuscript assertion.
No homogeneous list, height, source point, curve, field, degree
bound or target host count is supplied in the final statement.

The per-system general half-power composition is therefore
closed under its exact generic-curve and chosen-source-cover
arguments. The degree-(a,1) and actual graph compositions retain
their stronger proved N^epsilon bounds under the generic curve
input and the distinct ordinary surface-cover input. The
primary geometric input proofs and the remaining full graph
consequence of the general half-power estimate remain open.
T1.7 stays in_progress; numbered coverage remains 79/167,
confirmed improvements remain 112 and Palomar is deferred.
This is a proof improvement without a confirmed manuscript
conclusion error; source bytes and dependencies are unchanged.

Verified under Lean v4.36.0-rc2: full build passed (12693 jobs); direct axiom audit passed for 9151 declarations using only propext, Classical.choice and Quot.sound; all 7193 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 14.48 GiB.


## General nonaligned literal hosts and the actual degree gap

The general nonaligned half-power composition is now proved
without either actual even-selection injectivity or the direct-sum
hypothesis. The proof excludes the actual source curves of degree D
using precisely the source's geometric nonalignment alternative.
Two functional square equations with disjoint nonempty left root
sets match two distinct integer roots to right roots. Their two
bounded grid points and the actual host lie on the same rational
affine graph. The previously proved exact grid-alignment theorem
constructs positive coprime slope data with the required bound.
A vertical degree-one image is impossible already from one
nonempty right root set: square matching forces X+i=0, contrary
to the far-positive host and bounded offsets. No square-class
independence premise enters either argument.

The actual height-one source curve small-degree theorem and
Hilbert multiplicity comparison now yield degree >=2D through
every such nonaligned integer root lift. A separately proved
finite-cover lemma accepts only a per-curve degree lower bound,
then performs the actual point lifting, injectivity, exceptional
set and finite curve cardinality composition. It does not assume
a host count. Substitution of the proved nonalignment degree gap
and the existing height/exponent calculations gives the full
general N^(1/2+epsilon) coefficient-uniform host count.

GeneralNonalignedRootHostCount constructs the homogeneous data
and selects a fixed subsystem, with constants independent of the
larger equation count. Its source_uniform_hosts_of_many starts
from literal dyadic integer hosts and the paper's exact
CompressedTargetAlignment.Aligned 1 nonalignment condition.
Critical-window positivity and the offset-to-scale comparison
are derived internally. The two root-set sizes can vary freely
subject to positivity and the common total-degree cap. Both
families are disjoint as required by the source-cover property.
There are no supplied fields, curves, Hilbert degrees, heights,
square-class maps, direct-sum facts or target count bounds.

The exact unproved inputs remain the generic normalized curve
count and chosen-source uniform surface-cover properties, each
explicit theorem arguments. Neither primary determinant theorem
nor its chosen-embedding translation is claimed proved. The
general actual graph population count and these geometric inputs
remain open. T1.7 stays in_progress, coverage remains 79/167,
confirmed improvements remain 112 and Palomar is deferred.
This verifies the source's nonalignment alternative and introduces
no new confirmed manuscript-conclusion error or source change.

Verified under Lean v4.36.0-rc2: full build passed (12705 jobs); direct axiom audit passed for 9161 declarations using only propext, Classical.choice and Quot.sound; all 7203 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 14.45 GiB.


## The actual general graph half-power consequence

The first actual graph consequence of companion T1.7 is now
proved under exactly the generic normalized curve-count and
chosen-source uniform surface-cover properties. For every fixed
eta,epsilon>0, actual dyadic pairs with literal source nonalignment
and at least eta*(L+1) nontrivial unpinned components have
O(N^(1/2+epsilon)) hosts. The graph and component count are the
paper's actual arithmetic objects. The theorem even includes
overlapping physical windows; the two indexed copies of their
vertices are retained throughout. No component, polynomial
system, degree lower bound or target host count is assumed.

The construction enumerates bounded root subsets on BOTH sides,
including unequal positive sizes. Its exact finite pool consists
of two families of bounded offset sets and one family of actual
small-prime supports. Elementary Chebyshev bounds already proved
in the project give N^epsilon patterns, and the product of each
actual support has uniform polynomial coefficient height. No
prime-number theorem or smooth-number asymptotic is added.
The general nonaligned per-system estimate is summed over this
pool, with an explicit split of the epsilon margin.

Every actual nontrivial unpinned component meets both window
copies. Its two literal offset sets have total cardinality equal
to its vertex count; distinct components give disjoint root sets.
The product of the component labels has odd-prime support below
10*(L+1), and its actual squarefree prescription gives an integer
root for the corresponding equation. A chosen finite family of
components therefore constructs every pattern and root witness
required by the uniform smooth-system theorem.

For a population c>=eta*(L+1), the actual disjoint-vertex budget
and size cap ceil(4/eta) give at least eta*(L+1)/2 small components.
The logarithmic critical window eventually supplies any fixed
required number k. The fixed system size, chosen homogeneous
embedding degree, coefficient and pattern bounds all precede the
hosts and component choices. The final graph count is obtained
internally by injective host conversion and finite covering.

The first and degree-(a,1) graph consequences are thus composed
from the actual arithmetic graph under their respective explicit
geometric properties. The primary determinant theorems and their
translation/lifting statements remain unproved arguments; the
full T1.7 statement and later weighted sectors are not declared
complete. Coverage remains 79/167, confirmed improvements remain
112 and Palomar is deferred. No source bytes are changed and no
new error in a manuscript conclusion is confirmed.

Verified under Lean v4.36.0-rc2: full build passed (12715 jobs); direct axiom audit passed for 9183 declarations using only propext, Classical.choice and Quot.sound; all 7235 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 14.42 GiB.


## The actual dense weighted sector, conditional on the exact geometric properties

Companion T1.8, the dense weighted sector, now has its full
finite-sum and asymptotic composition under explicitly listed
geometric properties. Its status is CONDITIONAL, not proved.
For arbitrary actual dyadic host sets F, literal nonalignment and
c(x,y)>=eta*(L+1) imply sum_F(2^rho-1)=O(N^(1+epsilon)).
The same bound is proved for the full value kernel with the
separate block-parity equations omitted. In fact the theorem
bounds the larger sum_F 2^r where r is the actual dimension of
the kernel of the two-window value parity map, including local
relations. The effective pair nullity is proved <= this actual
full kernel rank. No compatibility, regularity or separation
hypothesis is needed, so overlapping physical windows are included.

The unconditional graph foundations are now literal. Swapping
the two start windows gives a graph isomorphism, a connected-
component equivalence and exact pin preservation. It exchanges
the two vertex projections. A general disjoint-block argument
proves 4*c<=2*B+2*t2+t3, and the actual component construction
identifies each size-two component with type (1,1). Every size-
three component has type (2,1), either in the original graph or
under the actual swap equivalence. The resulting cardinality
bounds justify the precise two-orientation split used by T1.8.

The actual raw value kernel is contained in the large-prime
solution space and therefore has dimension <=D_defect+c.
Previously proved critical defect estimates yield uniformly
D_defect=o(B). Exact binary-power conversion gives weight
<=N^(1+delta) globally and <=N^(1/2+delta) whenever the two-
and three-vertex populations are bounded. The proof partitions
the finite host set into many (1,1) components, many oriented
(2,1) components, and the remainder. The two subpower actual
graph counts bound the first populations, and the actual general
half-power graph count bounds the remainder. All partitions,
weights, epsilon margins, sums and constant orders are proved.

Only the exact generic normalized curve property and the
ordinary/chosen-source surface-cover properties remain inputs.
Their uses are limited to the fixed dimensions and degree caps
selected before the hosts. The generic property supplies the
ordinary Pila specialization internally. These properties still
include unproved primary determinant estimates and their exact
projection, lifting, integrality and prime/Hilbert translations.
No target weighted bound or arithmetic graph count is supplied
as an assumption. Thus T1.8 moves from not_started to conditional;
proved numbered coverage stays 79/167. T1.7 and the full papers
remain incomplete, confirmed improvements stay 112, and Palomar
is deferred. Original manuscript bytes are unchanged and no
manuscript-conclusion error is newly confirmed.

Verified under Lean v4.36.0-rc2: full build passed (12727 jobs); direct axiom audit passed for 9215 declarations using only propext, Classical.choice and Quot.sound; all 7271 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 14.38 GiB.


## Actual second-cumulant and two-channel approximations under the geometric inputs

The conditional geometric graph bounds are now connected to
the actual infinite-model second factorial cumulant. The dense
nonaligned coefficient family used by the existing pair-profile
reduction has absolute activity <=N^(-1+epsilon), uniformly in
the critical window, under the same explicit generic curve and
ordinary/chosen-source cover properties. Every actual pair in
this family has positive joint mass and relative nullity >L/10.
Raw-kernel domination and the unconditional defect bound imply
an actual nontrivial-component population >=(L+1)/100. Thus the
proved weighted graph sector applies to the precise family
remaining in the probabilistic reduction, not an assumed count.

A new exact finite identity converts any selected family of
two-element subsets to its actual ordered pair hosts, giving
exactly twice the original weighted sum. Literal source
nonalignment is recovered in both orientations from exclusion
of the actual aligned family. The compatible centered-moment
bound, positive exact marginals, dyadic marginal cap, full
kernel domination and finite weighted sum give the stated
dense-activity rate. No compatibility probability, marginal,
rank, host count or dense-activity estimate is supplied as an
extra theorem premise. All are recovered from the existing
actual model and membership in its defined dense family.

PairProfilesUnderGeometricInputs.uniform_profiles then proves
both |kappa2-2*beta|<=N^(-4/5+epsilon) and the exact two-channel
approximation with mainTerm(2,3)+mainTerm(3,4), for the actual
second factorial cumulant of the full dyadic count. Fixed
threshold multipliers satisfy the original 8*(L+1)<=H<=D*(L+1)
scope. The nonaligned dense remainder is completely eliminated
in these two conditional conclusions. The already proved aligned,
weak, irregular, diagonal and channel comparison estimates
supply all other terms, with explicit epsilon absorption.

The exact unproved inputs remain solely the generic normalized
curve and the two distinct surface-cover properties, at the
fixed dimensions/caps exposed before the hosts. In particular
this composition does not add a BCN or target-profile argument.
The raw positive/signed relation-count displays and the full
phase-asymptotic alignment in article Theorem 3.3 are not newly
claimed complete. That row stays in_progress. T1.8 remains
conditional; T1.7 and the whole project remain incomplete.
Proved numbered coverage stays 79/167 and confirmed improvements
stay 112. No source bytes, compiler or dependencies are changed;
Palomar remains deferred and no manuscript-conclusion error is
newly confirmed.

Verified under Lean v4.36.0-rc2: full build passed (12733 jobs); direct axiom audit passed for 9222 declarations using only propext, Classical.choice and Quot.sound; all 7279 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 14.36 GiB.


## The complete actual principal-edge input under the geometric properties

Article Corollary 3.4 now has all its actual principal-edge
inputs under the explicit geometric properties. Its ledger
status is CONDITIONAL, not proved. The new uniform_edge_input
packages one common set of geometric dimensions and caps,
positive beta comparison constants and one scale cutoff before
all windows and prime thresholds. It gives the exact edge-card
bound 26*(L+1)*N, beta comparable to L*N^(-2/3), the actual
second-cumulant comparison |kappa2-2*beta|<=N^(-4/5+epsilon),
and the actual ordered covariance sum outside these edges.
The per-channel actual rank, regularity and joint-mass caps
were already proved by CompatibleChannelEdges.edge_data;
these retain the separate denominators 3 and 4 and nominal
marginal (2^L)^(-1). Together they give the complete source
corollary, with a stronger remainder than its additional B/N.

The new finite argument uses the exact positive gap between
absolute pair activity and half the actual second factorial
cumulant, and the exact nonnegative beta-minus-edge-activity
gap. Subtracting the actual edge population from all two-element
subsets gives the off-edge absolute activity. The conditional
cumulant profile therefore bounds the whole off-edge activity
by N^(-4/5+epsilon). An exact ordered-host identity gives the
same rate for every subset G of the full dyadic ground set,
with no regularity or separation premise on that actual-
marginal statement.

For the original source formula, the regular-set marginal
identity is applied inside the actual Bochner integral.
regular_nominal_coefficient proves the coefficient is precisely
the expectation of (J_x-p)*(J_y-p), with p=(2^L)^(-1), rather
than leaving a change of centering implicit. The final ordered
sum is over the actual regular set and excludes exactly the
literal PrincipalChannelEdges.edges. Its bound is
N^(-4/5+epsilon), which also implies the printed bound with
an additional B/N term. All arithmetic, probability, centering,
set partitions, orientation factors and exponent absorption
are internally proved. The nominal covariance count is not
provided as a theorem argument.

The exact unproved inputs remain the generic normalized curve
property and the ordinary/chosen-source surface-cover properties
at the exposed fixed dimensions and caps. No BCN input, target
cumulant bound, covariance remainder or opaque arithmetic input
is added. Primary determinant/translation proofs remain open.
Main 3.4 moves from in_progress to conditional, T1.8 remains
conditional, main 3.3 and T1.7 remain in_progress, and proved
coverage stays 79/167. Confirmed improvements stay 112, original
source bytes are preserved, and Palomar remains deferred.
No new manuscript-conclusion error is confirmed.

Verified under Lean v4.36.0-rc2: full build passed (12735 jobs); direct axiom audit passed for 9226 declarations using only propext, Classical.choice and Quot.sound; all 7283 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 14.35 GiB.


## P1-MATH-0113 — A conditional near-linear literal arithmetic residual

The literal arithmetic rank in the manuscript is now connected
explicitly to the full value-kernel bound. It is pairLoss=2L minus
the dimension of the joint square-class image, INCLUDING local
kernels, whereas the exact-marginal probabilistic development
uses the effective relative nullity. A rank-nullity computation
on the actual even-selection domains proves, for all x,y,L,
pairLoss=finrank(completeRelationCode). The inclusion of that
actual code in the raw value kernel then proves pairLoss<=fullRank.
No regularity, positivity or independence premise is needed for
these exact algebraic comparisons. T1.8's dense estimate is now
specialized explicitly to the source's full arithmetic rank;
the earlier full raw-kernel theorem was the stronger input.
This closes a source-translation obligation, without an error
in the manuscript or an identification of the two ranks.

The weighted nonaligned residual in article Proposition 3.2
is now proved under exactly the same explicit generic normalized
curve and ordinary/chosen-source surface-cover properties.
The proved exponent is 1+epsilon, improving the printed
6/5+epsilon. This is recorded separately as P1-MATH-0113,
a confirmed implication CONDITIONAL on those exact geometric
properties; the external determinant and translation proofs
remain unformalized. It is not an unconditional exponent claim.

The proof removes the zero-pairLoss terms and partitions the
actual remaining host set by whether c>=epsilon*(L+1)/16.
The dense part has its already proved O(N^(1+epsilon/2))
source-kernel weighted bound. In the sparse part, the actual
raw kernel rank is at most the defective count plus c; the
unconditional defect estimate and binary-power conversion
bound each weight by N^(epsilon/4). The positive-pairLoss
support is literally a subset of PairHostCover.hosts, whose
stronger unconditional count is N^(1+epsilon/4). Multiplying
and summing proves the improved weighted bound, with all
constants and geometric caps fixed before the host data.
Local kernels, zero compatibility, irregular windows, contacts
and overlapping windows are all retained; no effective-rank
replacement or supplied support/count estimate is used.

NonalignedSourceResidualUnderInputs.uniform_source_bounds
packages both separated support and weighted residual counts
with exponent 1+epsilon. article_3_2 specializes these to both
literal printed 6/5+epsilon conclusions. Hence main 3.2 moves
to CONDITIONAL, not proved. T1.8 and main 3.4 remain conditional,
main 3.3 and T1.7 remain in_progress, and proved numbered
coverage stays 79/167. Confirmed improvements become 113,
including the explicitly conditional improvement just stated.
No manuscript conclusion error is confirmed. Original source
bytes, compiler and dependencies are unchanged; Palomar remains
deferred until completed coverage and actual input proofs.

Verified under Lean v4.36.0-rc2: full build passed (12741 jobs); direct axiom audit passed for 9234 declarations using only propext, Classical.choice and Quot.sound; all 7292 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 14.33 GiB.


## The actual all-ordered signed arithmetic pair profile

The signed arithmetic pair Fourier weight is now connected
literally to actual probabilities, nominal centering and the
second factorial cumulant. SourcePairAffineWeight constructs
eta as an actual zero/one compatibility indicator and proves
its equality to compatibility of the literal finite family
start system at every adequate cutoff. The exact identity is
q_xy=p^2*eta_xy*2^pairLoss, with p=(2^L)^(-1), including every
local kernel and incompatible pair. The scaled signed weight
is therefore q_xy-p^2. No regularity, positive probability or
effective-relative-rank replacement is assumed in this identity.

An exact finite sum over all ordered DISTINCT pairs proves
p^2*sum(eta*2^pairLoss-1)=kappa2+mu^2-(|G|p)^2+|G|p^2.
The actual diagonal is retained. The identity uses the literal
ordered/unordered multiplicity and actual falling factorial
moment. It applies to arbitrary dyadic subfamilies. The proved
mean bias, actual mean cap and nominal square bound then give
an UNCONDITIONAL error <=N^(-1+epsilon) between the scaled full
dyadic signed sum and the actual second factorial cumulant.
All centering and diagonal terms are recovered internally.

SignedSourceProfileUnderInputs.uniform_all_ordered combines
this identity with the conditional actual two-channel cumulant
profile. It proves, for ALL ordered distinct dyadic pairs,
|sum(eta*2^pairLoss-1)-N/3*(S_23(L)+S_34(L))|
<=N^(6/5+epsilon). The finite signed channel polynomials are
exact, including all lower-order terms. The two actual rational
translation coefficients are each exactly 1/3. The proof derives
the nominal unscaling estimate from the critical binary word
bound and composes all exponent and constant margins explicitly.
Only the previously identified generic normalized curve and
ordinary/chosen-source surface-cover properties remain inputs.
A fixed admissible prime threshold 8*(L+1) is selected internally;
the final source statement has no extra threshold parameter.

This is the ALL-distinct-pair variant, not yet the manuscript's
separated-pair display. Removing the close pairs still requires
its explicit contact comparison. The raw positive profile and
full phase-asymptotic alignment also remain open. Main 3.3 stays
in_progress and no complete raw pair-profile claim is made.
Main 3.2, main 3.4 and T1.8 remain conditional on the exact
geometric properties. Proved coverage stays 79/167, confirmed
improvements stay 113, and no new improvement identifier is
assigned to these source identities and proof compositions.
Original source bytes, compiler and dependencies are unchanged;
Palomar remains deferred and no manuscript-conclusion error
is newly confirmed.

Verified under Lean v4.36.0-rc2: full build passed (12749 jobs); direct axiom audit passed for 9247 declarations using only propext, Classical.choice and Quot.sound; all 7308 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 14.30 GiB.


## The literal separated signed arithmetic pair profile

The signed raw relation-count display of article Theorem 3.3
is now proved literally on separated ordered dyadic hosts under
the explicit geometric properties already identified. The new
article_3_3_signed theorem gives
|sum_(separated)(eta*2^pairLoss-1)-N/3*(S_23(L)+S_34(L))|
<=N^(6/5+epsilon). The source full arithmetic rank includes the
local kernels, eta is the actual affine compatibility indicator,
and both finite signed channel polynomials are retained whole.
There is no supplied separated host count or profile remainder.

The new contact comparison is unconditional. Exact finite
membership lemmas identify the ordered close hosts with distinct
pairs whose distance is at most L, and the complementary hosts
with precisely x+L<y or y+L<x. An exact partition identity
preserves both orientations and the actual multiplicity two.
The nominal squared mass of close pairs is bounded by
L*|G|*p^2 using a constant-weight disjoint-pair estimate.
The existing actual contact joint-mass bound handles every
positive close event, including compatible exact contacts.
No assertion that all close joint probabilities vanish is used.

The exact source Fourier identity converts p^2 times the absolute
signed source weight to |q_xy-p^2|. Sum the actual joint mass and
nominal close mass, retain the ordered multiplicity, and use the
proved critical-window word bound to remove p^2. This gives an
UNCONDITIONAL O(N^(1+epsilon)) total absolute signed weight on
all close hosts. It retains irregular windows, local kernels and
incompatible pairs. Subtracting this exact close population from
the previously proved all-ordered signed profile gives the
literal separated display. All finite partitions, powers,
constants and epsilon margins are internally proved.

Only the generic normalized curve property and the distinct
ordinary/chosen-source surface covers remain explicit unproved
arguments in the resulting signed-profile theorem. The contact
bridge itself uses no BCN or determinant argument. The positive
raw profile and the full source phase-asymptotic conclusions
remain open, so main 3.3 stays in_progress. Main 3.2, main 3.4
and T1.8 remain conditional. Proved numbered coverage stays
79/167 and confirmed improvements stay 113. These are source
translation and proof-composition advances, with no new
improvement identifier or manuscript-conclusion error.
Original source bytes, compiler and dependencies are unchanged,
and Palomar remains deferred.

Verified under Lean v4.36.0-rc2: full build passed (12755 jobs); direct axiom audit passed for 9257 declarations using only propext, Classical.choice and Quot.sound; all 7320 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 14.65 GiB.


## Positive arithmetic weights and actual unsigned private channels

The positive arithmetic profile now has an actual unsigned
unit enumeration and an unconditional private-channel theorem.
SourcePairPositiveWeight retains the literal source rank
pairLoss=2L-dim(S_x+S_y), including both local kernels, and
identifies its positive weight with the dimension of the actual
even unit relation space on private normalized pairs. There is
no affine-compatibility or positive-probability restriction.
A separate setWeight uses the full arithmetic rank on finite
families; its pair specialization is proved exactly.

The existing canonical selected-word equivalence is used to
count every nonzero even unit relation. Its literal finite
cardinality is 2^(number of units-1)-1. Reindexing by actual
source pairs and endpoint placements gives both orientations
of the unsigned host aggregate, with the actual coefficient
2*(2a-b)/(ab) and the finite U_ab(L), with endpoint error at
most 6*(L+1)*U_ab(L). No signed probability estimate is used
to infer this positive count, so incompatible principal pairs
are fully retained.

PrivateChannelPositiveMass.channelWeight is the sum of the
actual 2^pairLoss-1 over the actual private channelSources.
Its exact deletion identity subtracts precisely the nonprivate
unit aggregate. One-unit or zero-unit terms vanish by their
proved even-kernel dimension. The finite error is bounded by
6*(L+1)*U_ab(L) plus twice the actual nonprivate source count
times 2^((L+1)/b). Combining the proved square-root nonprivate
count, critical word bound and polynomial absorption yields
PrivateChannelPositiveProfile.uniform_error:
|channelWeight-N*coefficient(a,b)*U_ab(L)|
<=N^(1/2+1/b+epsilon), uniformly for fixed positive coprime
interior a<b<2a and 2b(L+1)<=H<=D(L+1). The coefficient is
therefore literally 1/3 in both principal channels. All these
results are unconditional.

A separate unconditional uniform source-power theorem on the
literal enlarged alignments gives 2^pairLoss<=N^(1/b0+epsilon)
for every height at least b0, up to (L+1)^3. The zero-exact-unit
version gives N^epsilon. The derivation uses the already proved
full source rank bounds and keeps local kernels. It introduces
no determinant or point-count assumption.

The remaining aligned residual populations, strict separated
source placement, disjoint principal-channel decomposition and
full phase-asymptotic conclusions are still to be assembled.
Thus these auxiliary theorems do not complete main 3.3; its
signed separated profile remains conditional on the explicit
geometric properties. Proved numbered coverage stays 79/167
and confirmed mathematical improvements stay 113. No new
external input, manuscript correction or improvement identifier
is introduced. Original source bytes, compiler and dependency
pins are unchanged; Palomar remains deferred.

Verified under Lean v4.36.0-rc2: full build passed (12767 jobs); direct axiom audit passed for 9284 declarations using only propext, Classical.choice and Quot.sound; all 7354 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 14.62 GiB.


## The literal positive separated source profile

The first display of article Theorem 3.3 is now proved literally:
|sum_(ordered separated)(2^pairLoss-1)-N/3*(U_23(L)+U_34(L))|
<=N^(6/5+epsilon). The source rank is exactly 2L-dim(S_x+S_y),
with local kernels retained. There is no compatibility filter.
PositiveSeparatedSourceProfileUnderInputs.article_3_3_positive
uses only the explicit normalized-curve and ordinary/chosen-source
surface-cover properties already recorded. For this positive
display the chosen-source component cap is sizeCap(epsilon/64),
with the embedding degree and all other caps selected before
those geometric arguments. The signed display has its separately
recorded fixed cap. No target mass or remainder is an input.

The entire aligned positive residual is unconditional. The proved
O(N^(1+delta)) support count for actual full-rank-loss pairs,
including irregular windows, combines with the proved enlarged
alignment power bounds to give O(N^(1+1/b0+epsilon)) mass on
all channels of height at least b0. Thus the height-five tail is
O(N^(6/5+epsilon)), without any additional point-count theorem.
Zero-unit alignments have O(N^(1+epsilon)) positive source mass.
The separated height-one boundary is contained in that actual
zero-unit population. The height-two boundary has O(N^(1/2+
epsilon)) mass, by its literal endpoint rectangle and full
source rank bound. Nonprivate fixed-channel sources have
O(N^(1/2+1/b+epsilon)) positive source mass, including incompatible
events; the actual unordered image is bounded as well.

StrictChannelSourceSeparation strengthens the existing weak
separation conclusion to x+L<y, under the same source-parameter
and size hypotheses. Its proof uses the actual exact-unit
translation and endpoint bounds; it does not discard contacts
by a probability assertion. Consequently both private principal
channels lie inside the actual separated-pair family. Their
unordered families are disjoint by the already proved slope
separation. The exact ordered multiplicity two and their actual
positive masses are proved, with both orientations retained.

A finite nonzero-weight cover classifies the aligned residual
outside the principal families into six actual populations:
separated height one, height two, the two nonprivate principal
channels, zero-unit alignments and the high tail. Private
one-unit terms vanish by their actual source kernel dimension.
Their unconditional bounds give the full aligned residual.
The conditional nonaligned mass bound applies to the actual
ordered host family, with no regularity or compatibility premise.
An exact positive decomposition then combines both complete
unsigned principal polynomials with the aligned and nonaligned
remainders. All constants and epsilon margins are internally
absorbed; a fixed threshold H=8*(L+1) is selected in the final
statement, which has no extra threshold parameter.

This completes the literal positive profile while preserving the
already proved literal signed profile. The final leading and
second-phase equivalents for the actual cumulant remain to be
assembled, so main 3.3 stays in_progress. Completed numbered
coverage stays 79/167 and confirmed improvements stay 113.
These are proof and statement-alignment advances; no new
correction identifier or external input is added. Compiler,
dependency pins and original manuscript bytes are unchanged.
Palomar remains deferred.

Verified under Lean v4.36.0-rc2: full build passed (12779 jobs); direct axiom audit passed for 9307 declarations using only propext, Classical.choice and Quot.sound; all 7382 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 14.59 GiB.


## Actual variance and both principal phases: conditional completion of theorem 3.3

All five conclusions of article Theorem 3.3 are now aligned
and proved under explicit geometric inputs, so its ledger status
is conditional rather than in_progress. This does not discharge
those geometric properties or increase unconditional numbered
coverage. The positive and signed ordered separated profiles
retain their exact finite U_23/U_34 and S_23/S_34 polynomials.
The existing P1-GEO-NORMALIZED-CURVE-UNIFORM,
P1-GEO-ORDINARY-SURFACE-COVER and
P1-GEO-CHOSEN-SOURCE-SURFACE-COVER properties remain unproved
ordinary theorem arguments, with the precise finite caps exposed
in the component declarations. The positive profile uses its
epsilon-dependent source component cap; the signed, cumulant
and phase declarations expose their fixed-density caps. No
common supplied target remainder or hidden axiom is introduced.

CountVariance proves that every actual finite infinite-model
start count is in L2, using its actual measurability and the
pointwise bound by the number of starts. Its Mathlib variance
is exactly E[Z^2]-(E[Z])^2. Hence the existing full second
factorial cumulant is literally Var(Z)-E[Z], with the diagonal
mean term retained. ActualPairPhaseUnderInputs.alpha uses that
actual variance and actual Bochner expectation, not a newly
postulated scalar. These identities are unconditional.

The principal height-three and height-four sums are identified
exactly with the actual 2:3 and 3:4 main terms. The nominal
parameter is literally lambda=N*2^(-L). The whole first-channel
term is exactly lambda^2/(3N)*S_23(L). The existing moving
height phases evaluate to the printed constants
(r3+2)/(18*2^(r3/3)) and (r4+3)/(24*2^(r4/4)), with powers
lambda^(5/3)*L*N^(-2/3) and lambda^(7/4)*L*N^(-3/4).
The identities hold for the actual residues L mod 3 and L mod 4.
No fixed-residue subsequence is substituted for the source claim.

Unconditional positive phase lower bounds show that every
strictly smaller power error is negligible uniformly in the
critical band. The entire finite 3:4 channel is negligible
relative to the 2:3 phase. The actual conditional cumulant
remainder is instantiated at the fixed exponent -31/40,
strictly below both phase exponents. Combining these facts
with the proved word-phase equivalents yields, for every
positive tolerance, a single threshold preceding every
critical L, and both relative errors at most that tolerance.
For the second phase, the entire finite S_23 is subtracted
before comparison; its lower-order internal terms are retained.
ActualPairPhaseUnderInputs.article_3_3_phases gives the two
literal source ratios and article_3_3_cumulant gives the
literal actual-variance-minus-mean expansion with error
N^(-4/5+epsilon). Positivity of both phase denominators is
proved inside uniform_phases.

The new COMPLETE_PAIR_PROFILE_ALIGNMENT note maps all five
displays and the actual probabilistic quantities to their Lean
declarations and records the residual external scope. Main 3.2,
3.3, 3.4 and companion T1.8 are conditional on the previously
identified geometric properties. Unconditionally proved
numbered coverage stays 79/167 and confirmed mathematical
improvements stay 113. No new correction identifier is needed:
these are the remaining exact translations and proof assemblies
of the source theorem. Original manuscript bytes, compiler and
dependency pins are unchanged. Palomar remains deferred until
the full development, external inputs and alignment are complete.

Verified under Lean v4.36.0-rc2: full build passed (12785 jobs); direct axiom audit passed for 9324 declarations using only propext, Classical.choice and Quot.sound; all 7400 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 14.57 GiB.


## Homogeneous dependent pairs outside the raw principal family

The outside-principal residual in the first numbered clause of
companion T1.12 is now proved under the already identified
geometric properties. HomogeneousPairResidualUnderInputs.
companion_T1_12_pair_residual gives the literal W-mass bound
N^(-4/5+epsilon) on all dependent, strictly separated pairs of
any regular dyadic subfamily, outside the actual raw principal
family. The affine-compatibility condition is absent. The exact
same bound is proved for the sum of the actual homogeneous
zero-target probabilities over that actual population. The
private cutoff satisfies 8(L+1)<=H<=D(L+1), with D fixed and
all subfamilies varying after the common threshold.

The new unconditional probability bridge uses the full source
pairLoss, including local kernels. The actual homogeneous pair
probability is exactly p^2*2^pairLoss even on irregular windows.
The full pair-span dimension plus pairLoss is proved equal to
2L. On regular distinct pairs, pairLoss equals the actual
effective relative nullity, by the exact two-space dimension
identity and the actual local ranks. The source W weight can
therefore be used on the regular set without silently asserting
a nominal relative-nullity formula on irregular windows.
For positive source loss, the elementary bound
2^rho<=2*(2^rho-1) is proved, with its full scaling.

The finite off-principal positive mass is bounded by the actual
positive profile error and the two actual private-channel errors,
using the exact ordered multiplicity and disjoint private
principal families. Combining the proved literal positive
profile with the unconditional private-channel errors gives
RawPairResidualUnderInputs.uniform_bound:
sum_(separated outside raw principal)(2^sourceLoss-1)
<=N^(6/5+epsilon), uniformly over the admissible private cutoffs.
No supplied off-principal count or mass is an input. The public
geometric component cap is sizeCap(epsilon/128), and all other
finite caps precede the explicit geometric arguments.

The actual regular dependent-pair population is defined and
proved to lie in that original separated off-principal family.
Its W weight is at most twice p^2 times the positive source
weight. The proved critical nominal-square upper bound and
constant absorption yield the printed N^(-4/5+epsilon) rate.
The final public component cap is sizeCap(epsilon/384), with
the exact normalized curve and ordinary/chosen-source cover
properties as explicit unproved arguments. This is a geometric
conditional proof, not an unconditional certification or a
postulate of the target residual bound.

Together with the previously proved unconditional raw principal
seed upper/lower scale, this closes clause (1) of T1.12 under
those geometric properties. Clauses (2) and (3), involving
dependent targets and two distinct good edges, remain open;
T1.12 stays in_progress. The asymmetric large-prime profile
T1.10 is not asserted proved by these pair results. Main 3.3
remains conditional with all five conclusions aligned. Coverage
stays 79/167 and confirmed improvements stay 113. These are
proof-composition advances without a new correction identifier.
Original manuscript bytes, dependencies, compiler and Palomar
state are unchanged.

Verified under Lean v4.36.0-rc2: full build passed (12791 jobs); direct axiom audit passed for 9337 declarations using only propext, Classical.choice and Quot.sound; all 7414 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 14.55 GiB.


## P1-MATH-0114 — Direct finite forcing of actual ternary group planes

The finite arithmetic and plane-forcing core of companion T1.16
is now proved for actual prime groups on three arbitrary finite
sets of positive integers. This is the source ternary group
budget, not the separate abstract ternary selection theorem T2.3.
The final CRT tail sums and fixed-k induction are still open,
so T1.16 moves from not_started to in_progress, not proved.

TernaryPrimeGroups constructs the actual finite value-triple
pool and, for each triple, the product of exactly the primes
above H with odd valuation in all three entries. Membership,
primality, positivity, squarefreeness and divisibility of every
entry are proved. A prime above the common diameter cannot
occur at two different values in a block. Consequently the
prime sets of distinct actual triples are disjoint, their
products are coprime, and all active group values greater than
one are distinct. The strict decreasing-order convention in
the source therefore causes no hidden tie issue. The literal
support-pool cardinality is the product of the three set sizes.

The arithmetic rigidity is proved for arbitrary finite sets.
Injectivity of an even-selection map implies injectivity of
its data vectors, by the two-coordinate zero-sum selection.
For the finite forcing argument it suffices that the parity
vectors of distinct local values are distinct, together with
pairwise disjoint even square-class images. Proportional
positive value pairs would give the same nonzero even class
in two disjoint images, which is impossible. The three-block
projection rigidity is derived from these actual arithmetic
hypotheses; it is not an assumed geometric exclusion.

Actual products of two groups divide every corresponding
2x2 integer minor. If values are at most A and within-block
diameters are at most H, the minor is at most 2AH. A shared
value is handled separately using coprimality and product
divisibility. This gives the uniform finite bound 2A(H+1).
The product of three actual groups divides their 3x3 determinant,
whose absolute value is at most 6AH^2. A group product greater
than this threshold forces the determinant to vanish.

The collinear exception is excluded without a primitive-direction
choice. Put d=v-u for the first two value triples. If u,v,w
are collinear, d cross u=d cross v=d cross w. Every actual
group therefore divides all coordinates of the same integer
cross vector. Pairwise coprimality makes their product divide
it, while each coordinate is at most 2AH. A larger product
forces the cross vector to vanish. The actual pairwise
square-class rigidity then forces u=v, contradicting distinct
supports. Thus, for H>=1, product>6AH^2 forces a genuine plane.
Every normal coordinate is proved nonzero, using the actual
positive projection rigidity and the vanishing determinant.
This unconditional finite simplification and weaker local
hypothesis are recorded as P1-MATH-0114. It is not an assertion
of the still open asymptotic counting bound.

For centers X and offsets bounded in absolute value by R,
the normal is identified with the cross product of offset
differences; it is independent of a common center translation.
Each normal coordinate has absolute value at most 8R^2 and
the plane constant is at most 24R^3. The centers satisfy the
actual resulting integer-plane equation. The actual plane
belongs to an explicitly defined pool depending only on R,
of cardinality (16R^2+1)^3*(48R^3+1). The plane is genuine and
all its normal coordinates are nonzero. No target plane,
primitive vector, rank premise or host count is postulated.

All these finite results are unconditional. The remaining
T1.16 obligation is the uniform tuple count
N^epsilon*(N^3/T^2+N^(6/5)), including actual CRT encoding,
hyperbolic reciprocal sums and the fixed-k induction. No new
external input is added. Coverage stays 79/167; main 3.3 stays
conditional and T1.12 clauses (2),(3) remain open. Confirmed
mathematical improvements total 114, with the exact finite
scope of the new finding retained. Original source bytes,
compiler and dependency pins are unchanged; no new Paper C
source is copied and Palomar remains deferred.

Verified under Lean v4.36.0-rc2: full build passed (12803 jobs); direct axiom audit passed for 9377 declarations using only propext, Classical.choice and Quot.sound; all 7463 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 14.52 GiB.


## P1-MATH-0115 — Two elementary shifted-power bounds simplify the CRT sums

The two CRT counting regimes in the proof of companion T1.16
are now proved on actual finite center populations, with the
three sets of values, their prime cutoff and their height cap
allowed to vary after the uniform threshold and with the center.
The sets themselves are never enumerated. The finite covers
enumerate only actual group products, their ordered positive
factorizations and bounded integer offsets.

IntegerOffsetCRT cancels arbitrary signed integer offsets in
two divisibility conditions and proves equality of the residue
classes. Pairwise coprimality combines all moduli. Each actual
coordinate in an interval of length N has at most N/Q+1 values;
an actual d-dimensional population has at most (N/Q+1)^d points.
No CRT solution is chosen, and no lower endpoint or offset
positivity is required. PlaneOffsetCRT proves that two actual
coordinates determine the third on an integer plane with
nonzero third normal coordinate. The corresponding count is
(N/Q+1)^2. The forced planes previously constructed have every
normal coordinate nonzero, so this condition is discharged.

ProductFactorizations constructs the actual finite pool of
ordered k-factor decompositions of Q, with cardinality at most
tau(Q)^k. The already proved elementary divisor estimate yields
a uniform subpower bound at every fixed polynomial product
height. CRTProductCover constructs the actual center cover,
including its coprimality and divisibility filters. Its offset
pool has exactly (2R+1)^(dk) members.

FiniteCRTTails transfers finite positive integer and positive
pair sums into the already proved summable p-series and
hyperbolic tails. The elementary inequalities
(a+1)^3<=4(a^3+1), a>=0, and (a+1)^2<=2(a^2+1)
remove all intermediate reciprocal terms. The finite cubic
sum is at most 8N^3*T^(-2)+4V for T<q<=V. The finite square
sum over positive pairs with ab>T is at most
2*C_2*N^2*T^(-1)*log(2T)+2*#pairs. Thus the source's separate
reciprocal-product logarithmic-square sum is unnecessary.
This checked proof simplification is P1-MATH-0115.

CRTProductRange proves the weak-regime count, retaining the
literal offset factor and uniformly paying for actual ordered
factorizations by M^epsilon. PlaneProductCover proves the
strong-regime count over any actual finite plane pool and only
two positive group sizes. The positive-product divisor count
pays for the latter size pool by V*M^epsilon. The third group
is not enumerated a second time.

TernaryTopProducts defines the actual maximum over products of
k distinct active groups, with value zero when too few exist.
The maximum is proved attained whenever positive, and every
selected product is bounded by it. Injective finite enumerations
give its actual group vectors. TernaryGroupCertificates proves
that these groups supply the actual offset-CRT certificates.
For a triple with product above 6AH^2 and whose squared product
exceeds T^3, an actual pair has product>T and <=2A(H+1), and the
center belongs to the actual two-group cover of the previously
constructed finite plane pool. No count or plane is postulated.

TernaryGroupCounts proves both uniform regimes for arbitrary
finite center populations with center-dependent arithmetic
sets. The weak bound is
M^epsilon*(2R+1)^(3k)*(8N^3/T^2+4V).
The strong bound is the exact plane-pool cardinality times
(2R+1)^6 times
(2*C_2*N^2*log(2T)/T+2V*M^epsilon).
All local data injectivity, disjointness, positive value and
diameter hypotheses in the strong bound are the actual
arithmetic predicates. The top-product height bound <=A^k is
also proved from actual group divisibility. These statements
have no new external input and no assumed target count.

The final critical-band absorption, the choice V=N^(6/5), and
the fixed-k induction remain open. Accordingly T1.16 stays
in_progress, numbered coverage stays 79/167, and main 3.3 stays
conditional. Confirmed improvements total 115. The compiler,
dependency pins and original manuscript bytes are unchanged;
no new Paper C source is copied and Palomar remains deferred.

Verified under Lean v4.36.0-rc2: full build passed (12823 jobs); direct axiom audit passed for 9421 declarations using only propext, Classical.choice and Quot.sound; all 7518 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 14.49 GiB.


## P1-MATH-0116 — One common cutoff for the complete fixed-k ternary budget

Companion Proposition T1.16 is now proved unconditionally,
including its actual tuple count, the final critical-band
absorption, the fixed-k induction, offset-pattern multiplicity,
and the source prime cutoff without an upper bound.
The public theorem is TernaryUnboundedCutoff.companion_T1_16;
actual_tuples_bound applies it to the literally defined finite
tuple population, not an abstract supplied count. The final
bound is N^epsilon*(N^3/T^2+N^(6/5)), for every fixed k>=3,
and in fact for every real T>=1, covering the printed range
1<=T<=N. The original common convention B=L+1 and critical
band is recorded in companion_sections/guide.tex:19-38.

One threshold, depending only on C,D,k,J,epsilon, precedes all
lengths and radii, the arbitrary type of offset-pattern labels,
their actual finite pool of size at most B^J, all actual center
populations, all assignments of the three arithmetic sets,
their cutoff choices, base intervals and the real threshold T.
The parameter J permits polynomially many actual pattern labels;
this includes the source's fixed number of offset patterns.
No regular-set, probability or affine-compatibility premise is
used. Values are actual positive integers of height at most DN,
within R<=DB of the centers. Center boxes have side length DN;
no lower center bound is required. A fixed natural D can enlarge
any fixed source height and width comparison constants.

TernaryGroupScales proves the exact polynomial bounds for the
offset and plane pools and their uniform critical-band absorption.
It proves 6(DN)H^2<N^(6/5) and 2(DN)(H+1)<=N^2 uniformly when
H<=DB, and bounds log(2N^(4/5)) by a fixed multiple of B.
The plane-pool and two-group-offset factor is bounded by
17^3*49*(2R+1)^15. All constants and fixed polynomial degrees
are paid for by positive power margins; no asymptotic factor
is inserted as an assumption.

TernaryWeakCritical proves the full weak count for any fixed k
and all T>=1, with product cutoff V arbitrary and nonnegative.
The actual group height <=DN proves topProduct<=N^(2k)
eventually, discharging the ordered-factorization height cap.
TernaryStrongCritical proves the actual three-group tail above
N^(6/5) is at most N^(6/5+epsilon). Its two-group threshold is
N^(4/5). The first term is N^2*N^(-4/5)*log(2N^(4/5)); the
second counts actual pairs of sizes with product O(NB), using
the already proved divisor estimate with a fixed margin 1/10.
The actual forced plane and finite offset pool are retained
throughout. Combining the weak and strong populations proves
the full three-group budget.

TernaryTopProductDrop deletes a smallest element of an actual
maximizing k-selection and proves
G_k^(k-1)<=G_(k-1)^k. Thus G_k>N^(6/5) forces
G_(k-1)>N^(6(k-1)/(5k)). For every k>=4 this exponent is at
least 9/10. The same preceding-order cutoff N^(9/10) therefore
works at every induction step, and N^3/N^(18/10)=N^(6/5).
This removes the source's separate k=4, k=5 and k>=6 cases.
The strong induction is fully proved in TernaryGroupBudget;
it does not accept a previous-order target bound as an external
argument. This simplification is recorded as P1-MATH-0116.

TernaryLargestSelection identifies an actual maximizing
k-selection with the k strictly largest active groups: every
outside group is strictly smaller than every selected group.
The previously proved active-value injectivity removes ties.
The canonical maximum product is zero when fewer than k active
groups exist. This aligns the finite maximum with the source's
decreasing-order convention without assuming a sorted list.

TernaryPatternBudget counts actual labeled tuples and absorbs
their B^J pattern multiplicity, with the threshold before the
label type. The source full even-map injectivity is explicitly
converted to the weaker local parity injectivity used by the
internal budget. Pairwise disjoint actual even images are
retained. No local kernel or directness condition is hidden.

The source only requires H to exceed the three diameters;
there is no upper bound on H in the final public statement.
TernaryCutoffMonotonicity proves actual prime-pool inclusion,
group divisibility and size monotonicity, active-support
inclusion and top-product monotonicity. Replace H internally
by min(H,2R+1): this still dominates the actual diameters and
has a fixed logarithmic ceiling, while every counted top
product can only increase. TernaryUnboundedCutoff proves this
reduction and the final actual finite-tuple theorem. The
source cutoff may vary both with the pattern and the center.

T1.16 moves from in_progress to proved. Numbered coverage is
now 80/167; confirmed mathematical improvements total 116.
Main 3.3 and the other identified geometric applications stay
conditional, and T1.12 clauses (2),(3) remain open. This result
adds no unproved external input, copies no further Paper C
source, and changes no original manuscript byte or dependency
pin. Palomar remains deferred until the full two-document
formalization and statement alignment are complete.

Verified under Lean v4.36.0-rc2: full build passed (12845 jobs); direct axiom audit passed for 9452 declarations using only propext, Classical.choice and Quot.sound; all 7557 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 14.44 GiB.


## T21.4: actual polylogarithmic group confinement in three dimensions

The full three-dimensional support-group branch of companion
T21.4 is now proved on actual finite tuple populations. The
individual-prime branch and the fixed-affine-plane variant
remain open, so the numbered proposition moves from not_started
to in_progress, not proved. Coverage stays 80/167 and confirmed
improvements stay 116; this is a proof-composition advance.

ProductConfinement proves the deterministic finite argument.
If all selected k-products of a finite factor set are <=N,
at most k-1 factors exceed N^(1/k). If the remaining product
exceeds N, a minimum-cardinality crossing subset has product
in (N,N^(1+1/k)] and all its factors are <=N^(1/k). Otherwise
the count of factors>Y is at most floor(log N/log Y), proved
by the actual finite logarithm-of-product identity. These
claims require neither primality nor an assumed stopping rule.

TernaryValueConfinement applies this to the actual group-value
pool. Group values and support labels have the same cardinality
by actual active-value injectivity. Their pairwise coprimality
is proved, every selected product is bounded by the actual top
product, and the crossing subset is shown to provide genuine
integer-offset CRT certificates for its actual centers.

CRTSupportCover canonically enumerates a finite set A of factor
sizes, rather than paying for all their orderings. The offset
cost is exactly (2R+1)^(3*card A). A certificate product Q>N
in a box of side DN has at most (D+1)^3 centers for each offset
assignment. The actual finite cover over all such A is bounded
by (D+1)^3 times the literal integer-factor weighted count of
T21.3. Coprimality is retained while applying CRT and only then
dropped in the positive Rankin sum. No target count is assumed.

RankinCertificateCritical combines that actual cover with the
already proved T21.3 integer-factor bound and the verified
sublinear-logarithmic exponential estimate. For any fixed
0<zeta<1 and k>=1 its count is at most
N^((1+1/k)*(1+(2+zeta)/c)+epsilon), uniformly over critical
lengths and bounded radii, all center base intervals and all
actual integer factor subsets. PolylogConfinementScales chooses
zeta and k before N so the extra exponent is arbitrarily small.
It also proves, uniformly in the critical band, that
k-1+floor(log N/(c log B))=o(L), with a literal statement for
every positive comparison constant and B=L+1.

TernaryGroupConfinement proves the actual exceptional-center
count N^(max(6/5,1+2/c)+epsilon). The first population has actual
topProduct>N and is counted by the completed T1.16. Every point
in the second population supplies an actual crossing certificate
and belongs to the Rankin cover. The two populations cover the
entire excessive-group family. The integer k depends only on
c,epsilon and precedes C,D, the actual sets and cutoff choices.
The source cutoff has no upper bound here.

LabeledPopulationCount proves a general finite label-fiber count.
TernaryConfinementMass uses it to include B^J actual offset-pattern
labels, with one threshold before the label type, all arithmetic
assignments and nonnegative weights. For point weights at most
N^(-beta+epsilon/2), the actual excessive-group population has
mass at most
N^(-min(beta-6/5,beta-1-2/c)+epsilon).
The remaining error margin pays for the count and labels. This
is the source's uniform N^(-beta+o(1)) weight regime made explicit;
it is not an assumed exceptional-count or exceptional-mass bound.
The actual exceptional finite set is defined, its mass is bounded,
and every retained tuple has at most
k-1+floor(log N/(c log B)) actual groups greater than B^c.

TernaryGroupNegligibility proves that c>6 makes
max(6/5,1+2/c)<4/3. It supplies a fixed positive point-weight
margin theta and a fixed k such that for every eta>0, eventually
the actual exceptional mass is <=eta*L*N^(-2/3), whenever each
host weight is in the beta=2 class, at most N^(-2+theta).
The retained count is the same literal source expression. This
is the sufficient c>6 assertion for the three-dimensional group
branch. No c>3 fixed-plane claim is made at this checkpoint.

The remaining T21.4 work is explicit: the individual-prime
fixed-k budget must account for repeated offset supports, and
the specified-plane CRT cover must enumerate only two free
offset coordinates to obtain the 1/c exponent and c>3 threshold.
No new literature input, Paper C copy, original source change,
dependency update or Palomar registration is introduced.

Verified under Lean v4.36.0-rc2: full build passed (12863 jobs); direct axiom audit passed for 9482 declarations using only propext, Classical.choice and Quot.sound; all 7597 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 14.40 GiB.


## P1-MATH-0117 and P1-MATH-0118 — Actual groups simplify individual-prime confinement

The individual-prime branch of companion T21.4 is now proved
in three dimensions, in addition to the previously completed
support-group branch. The remaining obligation is the specified
finite-family-of-affine-planes variant with its 1/c exponent
and sufficient c>3 threshold. T21.4 therefore stays in_progress;
numbered coverage stays 80/167. The two checked simplifications
below are P1-MATH-0117 and P1-MATH-0118, bringing the confirmed
improvement total to 118 without asserting a manuscript error.

TernaryIndividualPrimes constructs the actual finite pool of
primes above H with odd valuation in an actual value in every
block. Its membership is the literal existence of a support
triple in the actual pool. Each such prime is proved prime and
its support group active. A selected finite product of distinct
primes divides the product of its actual covering support groups.
If at most two support groups occur, the previously proved
one- and two-group bounds give a product <=2A(H+1). Thus three
selected primes above this threshold must occupy three supports,
and their product is at most the actual three-group top product.
This handles every repeated-support case without a new cross
product or collinearity proof. The large-prime tail reuses the
already proved actual three-group forced-plane count. This is
the unconditional proof simplification P1-MATH-0117.

FiniteFactorTopProducts proves the canonical largest k-product
for an arbitrary actual finite set of integer factors. It is
attained when positive, is zero when too few factors exist,
and a maximizing selection consists of the strictly largest
factors when they are positive. The smallest-factor deletion
inequality and its arbitrary real-exponent threshold consequence
are proved. No decreasing-order convention or induction target
is supplied as an input.

TernaryPrimeTopProducts constructs the actual individual-prime
top product, proves its height <=A^k and its monotonicity as the
prime cutoff increases, and constructs the actual offset-CRT
certificate of every positive maximizing selection. The prime
sizes are pairwise coprime because they are distinct actual
primes. Their offset supports may repeat. TernaryPrimeCounts
and TernaryPrimeWeakCritical prove the weak product count from
this literal certificate and the actual ordered-factorization
pool, with uniform critical-band absorption.

TernaryPrimeBudget proves the complete individual-prime fixed-k
budget N^epsilon*(N^3/T^2+N^(6/5)) for every fixed k>=3. Its
three-prime strong sector is bounded by the actual group sector
using the support-merging argument. The same N^(9/10) preceding
cutoff works throughout the strong induction. TernaryPrimeTheorem
retains arbitrary source cutoffs with no upper bound by the
already checked internal cap min(H,2R+1), and includes B^J
actual pattern labels with one threshold before the label type.
The source full even-map hypotheses are retained explicitly.

TernaryPrimeValueConfinement supplies the deterministic
confinement-or-certificate alternative for actual primes>B^c.
The crossing certificate belongs to the same integer-factor CRT
cover used for support groups. In particular, the separate
prime-only Euler product is unnecessary for the final T21.4
bound: use the proved integer-factor Rankin bound with any fixed
positive zeta, choose zeta small and k large before N, and absorb
the extra exponent in epsilon. The exponential in B^(1-zeta)
is uniformly subpolynomial. This is P1-MATH-0118; it simplifies
this application without replacing the sharper prime estimate
already proved in T21.3 or changing its statement.

TernaryPrimeConfinement proves the actual excessive-prime count
N^(max(6/5,1+2/c)+epsilon). TernaryPrimeConfinementMass counts
all actual pattern labels and proves the literal exceptional
mass N^(-min(beta-6/5,beta-1-2/c)+epsilon), for nonnegative
host weights in the source's uniform N^(-beta+o(1)) class.
The exact point-weight margin epsilon/2 is exposed. The actual
exceptional finite set is defined, its mass is bounded and every
retained tuple has at most k-1+floor(log N/(c log B)) individual
primes above B^c. The uniform o(L) conclusion follows from the
previously checked logarithmic-count scale theorem.

TernaryPrimeNegligibility proves the sufficient c>6 assertion
for beta=2, with a fixed positive point-weight margin and a
fixed k chosen before N. For every eta>0 the actual exceptional
mass is eventually <=eta*L*N^(-2/3). The argument is unconditional
within the explicitly stated positive-host-weight regime; it
assumes neither the exceptional population count nor its mass.

Only the fixed-plane 1/c and c>3 branch of T21.4 remains open.
No unproved geometric or analytic input is introduced by these
prime results, no further Paper C source is copied, and the
original manuscript and dependency pins remain unchanged.
Palomar remains deferred until the full work is complete.

Verified under Lean v4.36.0-rc2: full build passed (12885 jobs); direct axiom audit passed for 9515 declarations using only propext, Classical.choice and Quot.sound; all 7635 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 14.36 GiB.


## Complete companion T21.4: polylogarithmic confinement

Companion Proposition T21.4 is now complete, including both
actual support groups and actual individual primes, all ordinary
three-dimensional and specified-affine-plane mass estimates,
the literal retained-count bound and its uniform o(L) consequence,
and the sufficient c>6 and c>3 thresholds. It moves from
in_progress to proved. Numbered coverage is now 81/167; confirmed
mathematical improvements stay 118. This checkpoint closes the
remaining source obligations without a new correction identifier.

FreePlaneCRT proves that only two congruence coordinates are
needed on any genuine real affine plane. Choose a coordinate
with nonzero normal entry and project onto its two complementary
coordinates. The finite sum identity isolates the omitted
coordinate, proving injectivity of this projection. The actual
integer-offset residue population therefore has at most
(width/Q+1)^2 points. Plane coefficients are arbitrary real
numbers: there is no rationality, height or quantitative lower
bound on the nonzero normal coefficient. One common threshold
precedes the actual choice of planes and coefficients.

PlaneSupportCover defines actual finite plane-restricted CRT
populations. The canonical enumeration of a factor set A costs
exactly (2R+1)^(2*card A) offset codes. The third offset is never
an enumeration label. All three possible omitted coordinates
are covered by a factor 3. For Q>N and width DN, summing over
the actual finite plane pool gives the finite bound
3*#planes*(D+1)^2*integerWeightedCount(Y,V,(2R+1)^2).
Actual three-coordinate certificates restricted to a genuine
plane are proved to belong to this new two-coordinate cover.
This transfers both previously constructed group and prime
crossing certificates without assuming a plane-count estimate.

PlaneRankinCritical applies the already proved integer-factor
Rankin bound with d=2. With at most B^K actual planes, its
critical-band certificate count is at most
N^((1+1/k)*(1+(1+zeta)/c)+epsilon).
The arbitrary plane family, all coefficients, center intervals,
lengths, offsets and factor sets vary after the common threshold.
The polynomial plane multiplicity and the sublinear-logarithmic
exponential are absorbed using proved estimates. There is no
new external geometric or analytic argument.

PlaneTernaryConfinement proves a single simultaneous exceptional
count for excessive support-group OR individual-prime populations.
The two actual top-product>N populations are bounded by the
completed fixed-k budgets. In the remaining population, either
excess supplies an actual crossing certificate; its genuine
plane places the point in the two-coordinate Rankin cover.
The resulting count is N^(max(6/5,1+1/c)+epsilon).
The same parameter choice k,zeta already used in three dimensions
suffices, because the d=2 excess exponent is smaller.

PlaneConfinementMass includes B^J actual offset-pattern labels
and up to B^K real planes for each label. A common threshold
precedes the label type, all actual assignments and all weights.
Its actual_plane_confinement theorem defines the actual common
exceptional finite set and proves its positive mass at most
N^(-min(beta-6/5,beta-1-1/c)+epsilon).
Outside it, BOTH the actual support-group and individual-prime
counts above B^c are bounded by the same
k-1+floor(log N/(c log B)). The source point-weight regime is
made explicit as 0<=w<=N^(-beta+epsilon/2). Uniform o(1) point
errors fit this regime eventually; neither an exceptional count
nor an exceptional mass is an input.

PolylogConfinementTheorem.companion_T21_4_three_dimensional
likewise provides ONE actual exceptional set and a common k for
both ordinary three-dimensional populations. It combines the
previously proved group and prime branches using the maximum
of their fixed k values, the monotonicity of the literal count
threshold and positivity of the actual finite union mass. Its
mass exponent is exactly the printed
-min(beta-6/5,beta-1-2/c)+epsilon.
The final point-weight margin epsilon/4 is explicit. The earlier
PolylogConfinementScales.logarithmic_count_sublinear gives the
uniform o(L) conclusion for every such fixed k.

The simultaneous three-dimensional sufficient-cutoff theorem
proves the beta=2 exceptional mass is o(L*N^(-2/3)) whenever
c>6. PlaneConfinementNegligibility.sufficient_cutoff proves the
same conclusion on the specified plane populations for c>3.
Both give a fixed positive point-weight margin and a fixed k,
then for every eta>0 a common threshold such that the actual
exceptional mass is <=eta*L*N^(-2/3). These are sufficient
thresholds, exactly as in the source, with no optimality claim.

PrimitiveTripleWeights also discharges the source beta=2 weight
regime for actual original primitive full-rank triples. For an
injective primitive triple, its first pair is a proper subfamily
and has zero relative nullity, hence disjoint actual square-class
spaces. The full local ranks identify its homogeneous pair
probability with p^2. Monotonicity bounds the full homogeneous
triple probability by p^2; the actual affine triple probability
is bounded by the already proved direct-pair formula. The
uniform critical nominal-square estimate and constant absorption
give both actual probabilities in the class
0<=w<=N^(-2+theta), for every fixed theta>0. Full local ranks,
primitive status and injective original starts are actual
predicates, not supplied probability bounds. This bridge keeps
affine incompatibility and zero actual probabilities intact.

All T21.4 branches are unconditional under the source arithmetic
and positive-host-weight hypotheses. No new literature input,
Paper C source, original manuscript edit, dependency change or
Palomar registration is introduced. Main 3.3 and its identified
geometric applications remain conditional, and the open dense
edge and target bounds are unchanged.

Verified under Lean v4.36.0-rc2: full build passed (12903 jobs); direct axiom audit passed for 9546 declarations using only propext, Classical.choice and Quot.sound; all 7674 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 14.32 GiB.


## Sharp heterogeneous conversion and complete finite pair partition, under explicit geometric inputs

The literal source-scale heterogeneous conversion in article 15.1
and the complete finite-channel pair partition in companion T7.1
are now proved CONDITIONALLY on the already inventoried normalized
curve and ordinary/chosen-source surface-cover properties. Both
ledger rows move from in_progress to conditional. No geometric
property is discharged here. Unconditionally proved numbered
coverage stays81/167; confirmed mathematical improvements stay118.
This checkpoint assembles actual source statements and consequences
of P1-MATH-0113 without claiming a new unconditional exponent.

SharpPairActivityUnderInputs first combines the actual full second
factorial cumulant profile with the unconditional nonnegative gap
between absolute pair activity and half that cumulant. The full
original dyadic activity therefore equals the actual principal
beta up to N^(-4/5+epsilon). Every covariance sign, affine
incompatibility, zero marginal and locally irregular window is
retained. The already proved aligned activity and principal gap
then give A2(G)<=N^(-2/3+epsilon) for every deterministic subset G
of the original dyadic block, with one threshold before G and L.
The geometric source component cap remains the fixed1/100 used
by the existing cumulant profile. No target A2 bound is assumed.

SharpRunConversionUnderInputs applies the already unconditional
finite heterogeneous signed-measure theorem. The exact independent
Bernoulli product and every actual covariance are retained in B2;
mu is the actual first moment, and alpha is the complete actual
second factorial cumulant including its marginal-square diagonal.
The mean and marginal caps and the new A2 estimate discharge every
term of the finite error bound. The actual infinite sum of absolute
singleton differences between B2 and Q(mu,alpha) is at most
N^(-5/3+epsilon), as printed in article15.1. The same development
gives |alpha(G)|<=N^(-2/3+epsilon) uniformly for all deterministic G.
No complete-count-law approximation is inferred from this finite
reference conversion. The earlier generic theorem supplies the
first displayed finite inequality in15.1 without a small-marginal
premise; only its arithmetic rate is conditional.

SourcePairActivityBound proves a separate unconditional finite
majorant for the actual nonaligned activity. Nonzero covariances
are represented by increasing actual full-loss hosts. Positive
full source loss gives2^loss<=2*(2^loss-1), so the actual joint
mass is bounded by twice the nominal-square-scaled full source
weight. Negative covariance is retained through the actual host
independent mass. The complete conditional nonaligned source
weight bound from P1-MATH-0113 and the unconditional host independent
mass imply that the ENTIRE original nonaligned activity is at most
N^(-1+epsilon), including contacts and locally irregular windows.
Its exposed source cap isepsilon/32, not the fixed-density cap of
the separate sharp conversion. These interfaces are kept distinct.

FiniteAlignedChannelCover constructs the actual fixed finite set
of reduced interior slopes3<=b<=Q. It proves the enlarged aligned
classification at arbitrary Q, including the exact1:1 and1:2
boundary channels, the fixed-height private and normalized-defect
populations, zero-unit alignments and the high-height tail. No
constant-channel enumeration or source rank estimate is an input.

FiniteGoodChannelPartition defines three actual disjoint classes
of dependent pairs: positive private pairs in those fixed channels,
the remaining high-height pairs, and the complementary exceptional
pairs. Their union is the actual dependent family. Its exact
absolute-activity decomposition is proved, not supplied as a
partition hypothesis. Every good pair has an actual source channel
and the full GoodEdgeCompression.Conclusion: injective even-selection
map, equality of the compressed space with the original pair sum,
its exact rank, the source lower rank and a finite logarithmic-width
translation motif. The conclusions hold at every fixed retained
height, not merely in the two principal channels.

FiniteChannelActivityBounds proves simultaneous finite-family
bounds for all actual private and defective channel populations.
The selected cutoff is H=2Q(L+1), which satisfies the individual
channel width requirements for every b<=Q. The defective union
costs N^(-1+epsilon), the private union costs N^(-2/3+epsilon),
and every private coefficient has the literal pointwise bound
N^(-2+1/b+epsilon). The common threshold precedes all actual
populations and all critical lengths.

FiniteGoodPartitionUnderInputs.companion_T7_1 chooses Q after
eta>0 and BEFORE C, epsilon, all geometric input data and N.
It proves the actual weak activity<=N^(-1+eta+epsilon), actual
exceptional activity<=N^(-1+epsilon), sharp total pair activity,
and the individual good-pair weight and exact compression. The
exceptional activity is bounded by the actual nonaligned, two
boundary, zero-unit, fixed-defect and incompatible populations.
The source cap is preciselyepsilon/128 in the final declaration,
with finite auxiliary caps and quantifier order exposed. It is
not a supplied pair-activity or pair/target-deficit assumption.
The three classes remain disjoint by their actual set definitions;
no uniqueness of an auxiliary representation is presumed.

The finite classification, partition, compression and finite
reference-conversion inequalities are unconditional. Only the
identified geometric counting arguments are external. No new
literature input, global axiom, Paper C source, dependency download,
original manuscript edit or Palomar registration is introduced.
The sharp pair/target deficit of11.1, incompatible-triple3/2 rate,
conditional Palm estimates and dense primitive triple estimates
remain open. The next step is to count actual dependent targets
after a compressed fixed-channel source.

Verified under Lean v4.36.0-rc2: full build passed (12919 jobs); direct axiom audit passed for 9567 declarations using only propext, Classical.choice and Quot.sound; all 7703 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 14.28 GiB.


## P1-MATH-0119 — Compressed source/target counting without private coordinates

The actual compressed source/target count only needs one exact
normalized source coincidence and a nonzero effective target intersection.
The coefficients may be any fixed0<a<=b, even equal or non-coprime.
No private-coordinate, local full-rank, positive-joint, pair separation
or injectivity premise is needed. Arbitrary finite effective-block
counting includes targets equal to the compressed anchor. The actual
number of source/target tuples remains N^(1+epsilon).

Evidence: `CompressedChannelTargetCount.uniform_count`; exact location, impact and proposed revision are in `mathematical-changes.json`.


## Sharp actual pair-target deficit and triple cancellation

Article Proposition11.1, Theorem11.2 and Proposition11.3 now
have every literal source conclusion proved CONDITIONALLY on the
already inventoried normalized-curve and ordinary/chosen-source
surface-cover properties. Their ledger status moves from
in_progress to conditional. No target deficit, incompatible
activity, repeated-index estimate or cumulant comparison is an
external premise. Unconditionally proved numbered coverage stays
81/167. P1-MATH-0119 records an unconditional strengthening of
the compressed source/target host count, bringing the confirmed
improvement total to119 without a manuscript conclusion error.

CompressedChannelTargetHosts works at arbitrary fixed positive
coefficients0<a<=b. It extends the earlier principal-channel
geometry beyond b<=4: actual compressed values have height
between N/2 and3bN, width at most b(L+1) about their actual
anchor, and the anchor is at most3bN. For each pair of actual
unit offsets(i,j), the map((x,y),z) -> (anchor(x,y),z) is
injective. Exact source-space compression identifies the
nonzero target intersection with a genuine dependent pair of
finite effective blocks. The existing complete article10.3
then counts these pairs, including the diagonal where z equals
the compressed anchor. No private prime, local full rank,
compatibility, separation or pair injectivity is required.

CompressedChannelTargetCount.fixed_offsets has a common
critical-band threshold before all actual unit offsets.
Summing the actual finite offset cover and absorbing its
(L+1)^2 multiplicity gives the unconditional bound
#allTargets(N,a,b,L)<=N^(1+epsilon).
The actual tuple population includes every source with at
least one exact normalized coincidence and every target whose
effective space meets the original pair sum nontrivially.
The fixed coefficients need not be coprime or distinct.
This weaker-assumption count is P1-MATH-0119. It does not
assert the private-channel probability bound for arbitrary
nonprivate sources, or improve a printed asymptotic exponent.

PairTargetCost defines the actual restricted pair/target mass
and actual incidence population. It proves their exact
weighted-sum identity and monotonicity in both the pair family
and the ground set, retaining all covariance signs by absolute
value and every heterogeneous target marginal. The original
deficit is exactly this mass on the actual dependent-pair
family. The already constructed three-class channel partition
therefore gives an exact three-term deficit decomposition.
Every actual private-pair/target incidence belongs to the image
of the actual compressed tuple population; counting an image
costs no orientation or inverse-normalization assumption.

ChannelPairTargetCost.uniform_channel combines that proved
N^(1+epsilon) population count with the actual private-pair
coefficient cap N^(-2+1/b+epsilon) and the actual target cap
K_C/N. It proves the total actual pair/independent-target
cost N^(-2+1/b+epsilon), uniformly before EVERY prime cutoff H.
Its fixed finite private-channel union therefore costs
N^(-5/3+epsilon). Affine incompatibility is allowed in this
positive absolute cost. A separate uniform_restricted_mass
bounds any actual pair subfamily by its own absolute activity
times N^(-1/2+epsilon), using the already complete fixed-source
independent-target mass theorem. These finite arithmetic
source/target counts and channel-cost bounds are unconditional.

SharpPairTargetDeficitUnderInputs.article_11_1 chooses the
finite-channel partition with a small fixed fraction of the
final margin. The good part has the stronger5/3 rate just
proved; the weak and exceptional parts each have3/2 rate
from their actual activity and the independent-target half
count. Their exact sum and constant absorption prove
D_(2,1)(G)<=N^(-3/2+epsilon) for every deterministic subset G
of the original dyadic block, not only the positive-marginal
ground set. The same threshold also gives
A2(G)<=N^(-2/3+epsilon). The exact geometric source cap is
epsilon/512. It is fixed before the actual source/target
populations and is not a deficit estimate supplied as an input.

SharpThirdCancellationUnderInputs.uniform_cancellation uses
that proved deficit and the unconditional incompatible-triple
reduction. For every actual positive-marginal ground subset G,
it proves simultaneously
  incompatible absolute triple activity<=N^(-3/2+epsilon),
  0<=A3-K3plus<=N^(-3/2+epsilon),
  |kappa3-6K3plus|<=N^(-3/2+epsilon),
  absolute repeated-index cost<=N^(-5/3+epsilon).
Both signs of incompatible coefficients remain in the sum.
Every repeated occurrence of a Bernoulli variable is retained;
the stronger5/3 repeated-index rate is derived from the actual
marginal caps and sharp A2 estimate, not assumed. The exact
connected_activity_eq identifies the full absolute triple sum
with the literal connected A3 in the source. Compatible
coefficient nonnegativity was already proved unconditionally.
The geometric source cap is preciselyepsilon/2048 in this
joint theorem, with one threshold before G,N,L. Its actual
positive-marginal premise is the source admissible set, not a
homogeneous or regular-window replacement.

Stable input P1-ARITH-COMPRESSED-CHANNEL-TARGETS is now proved.
The only unproved properties in the final three article rows
remain P1-GEO-NORMALIZED-CURVE-UNIFORM,
P1-GEO-ORDINARY-SURFACE-COVER and
P1-GEO-CHOSEN-SOURCE-SURFACE-COVER, as ordinary explicit theorem
arguments at the displayed finite caps. This checkpoint adds
no new literature assumption, Paper C source, kernel axiom,
dependency download or manuscript-byte edit. It does not prove
the remaining dense primitive triple bound, the optimal third
cumulant exponent/lower bound, conditional Palm rates or any
complete count-law reconstruction. Palomar remains deferred.

Verified under Lean v4.36.0-rc2: full build passed (12931 jobs); direct axiom audit passed for 9593 declarations using only propext, Classical.choice and Quot.sound; all 7738 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 14.24 GiB.


## P1-MATH-0120 — Endpoint and uniform parameters in the small-kernel window count

The complete several-small-kernel window bound remains valid at
A=2. The proof only needs A>=2, u<=1 and m*(1-beta)>1; it needs
no positive lower bound on beta or u. The actual product-kernel
window estimate is uniform in every real q and every cutoff
0<=H<=D*(L+1), with one common threshold before those choices.
All original strict positive parameter regimes are included.


## Complete several-small-kernel window lemma

Article Lemma 15.4 is complete, with both literal source clauses
proved unconditionally for the actual complete dyadic windows.
It moves from not_started to proved. Numbered coverage is now
82/167. Confirmed mathematical improvements total 120; finding
P1-MATH-0120 records the endpoint A=2 and the weaker parameter
hypotheses actually proved. No source conclusion error is claimed.

CutoffSquareParts defines the full small-prime part s_Y(n), the
literal large square part a_Y(n)=product_(p>Y) p^(valuation_p(n)/2),
and d_Y(n)=s_Y(n)*a_Y(n)^2. This a_Y is not replaced by the
all-prime canonical square part. The exact decomposition
n=d_Y(n)*K_Y(n), quotient identity d_Y=n/K_Y, positivity and
divisibility are proved. Prime divisors of the small part are
at most Y; prime divisors of the large square part exceed Y
and divide n. Large square parts of distinct values at distance
at most Y are therefore coprime. Their coprimality with every
small part proves the exact lcm identity
lcm_i d_Y(v_i)=(lcm_i s_Y(v_i))*product_i a_Y(v_i)^2.
No squarefree replacement of these full prime powers is used.

PrimePowerAllocations assigns each complete prime power of a
positive modulus to one actual selected value that contains it.
Existence of that value follows from the factorization maximum
formula for a finite lcm. The resulting factors are pairwise
coprime, divide their actual values and have exactly the modulus
as product. This gives an actual SmoothModulusHosts certificate
whenever the modulus divides the lcm of actual positive values.
The construction does not assume a squarefree modulus or an
arithmetic assignment/count estimate.

ProductFirstPassage proves finite first-crossing statements for
indexed integer factors and for a factor list with a prescribed
initial product. Its smooth variant retains prime factors with
their multiplicities. SmallKernelCrossingCertificates applies
these to the actual quotients at bounded injective offsets.
If their lcm exceeds X and each a_Y(v_i)^2<=Z, it constructs
either a genuine square r^2 with X<r^2<=X*Z, or a genuine modulus
d with X<d<=X*Y and K_Y(d)=1. Each output carries the actual
pairwise-coprime CRT factors dividing the actual nearby values.
In the second branch, the complete product of large square
parts is kept as the initial product; only small-prime factors
are added. No ambient vector space or target counting assertion
is supplied as a premise.

SmallKernelLcmGrowth proves that m actual kernels at most N^beta
force the quotient lcm above C*N, for every fixed C>=0, when
m*(1-beta)>1. Each quotient is bounded below by a fixed positive
multiple of N^(1-beta). Its actual pairwise gcd is at most twice
the offset width. The finite product/lcm inequality and a proved
polylogarithmic absorption estimate give the strict growth.
The common threshold precedes the cutoff, width, centre and
every actual selected offset family. This is an unconditional
arithmetic estimate, not a quoted asymptotic input.

SquareCertificateCount counts the actual centres from square
certificates by enumerating their roots. The old fixed-modulus
CRT bound and the proved divisor subpower estimate absorb all
complete-prime-power allocations and bounded offsets. It has
one common threshold before the finite centre population and
all widths/interval endpoints. The already proved
SmoothCertificateCount counts the other branch: K_Y(d)=1
allows a Y-smooth factor times a square, with no requirement
that d itself be Y-smooth or squarefree.

SeveralSmallKernelCount combines these two actual populations
at X=2N. The square modulus has root at most
2*N^((1+u)/2) and polynomial height at most N^3 when u<=1.
The other modulus is at most 2*N*(log N)^A. Their union has
cardinality at most N^(max(1-1/A,(1+u)/2)+epsilon).
The selected offsets can vary with each actual centre after
the common threshold. No finite centre count is assumed.

SmallKernelWindowSets defines the actual small-value set inside
NormalizedWindowSets.values(x,L)=[x-1,x+L), the corresponding
severalWindows set and the actual twoWindows product-kernel set.
Finite subset selection gives m distinct actual values and
their bounded injective signed offsets. SmallKernelWindows
then proves the several-window count at the literal cutoff
floor((log N)^A), which represents exactly the primes above
the real threshold (log N)^A. On the critical band, this cutoff
eventually exceeds twice the complete window width. The second
source clause follows from the already proved actual two-kernel
product-cap count, at every H<=D*(L+1). It has the bound
#twoWindows<=N^(q+epsilon), simultaneously for every real q.
The joint theorem article_15_4 supplies one threshold before
every critical length, H and q. The source q>=0 is included.

The endpoint A=2 is covered: the square-smooth Rankin input
allows every sigma>1/2, hence the same N^(1/2+epsilon) modulus
count there. The several-window theorem only needs u<=1 and
m*(1-beta)>1; it uses no positive lower bound on beta or u.
These are the exact proved improvements in P1-MATH-0120.
For negative exponents, an impossible actual selection is
handled by the same statement rather than an omitted case.

This checkpoint adds no external literature property, Paper C
port, kernel axiom, dependency download or manuscript-byte edit.
It does not prove the separate sharp individual two-kernel
7/12 estimates in companion T1.5/T1.13, the Reuss-based input,
or the remaining primitive-mass and count-law reconstruction
results. Existing geometric conditional statements retain their
explicit unproved properties. Palomar remains deferred.

Verified under Lean v4.36.0-rc2: full build passed (12953 jobs); direct axiom audit passed for 9645 declarations using only propext, Classical.choice and Quot.sound; all 7799 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 14.20 GiB.


## The rational witness survives in the full third cumulant

Article Proposition14.5 now has every literal conclusion proved,
conditionally on exactly the previously inventoried normalized-curve
and ordinary/chosen-source surface-cover properties. Its status moves
from in_progress to conditional. The actual positive connected
lower bound remains unconditional. Numbered unconditional coverage
stays82/167 and confirmed mathematical improvements stay120.

SharpThirdCumulantLowerUnderInputs.article_14_5 applies the already
proved sharp third-cumulant cancellation at the fixed margin1/15.
Its error is N^(-43/30), whereas the actual rational witness family
gives K3plus>=c(C)*N^(-41/30), with the explicit positive
c(C)=2^(-4-(71/30)*C)/240. A proved constant-absorption estimate
bounds the error by c(C)*N^(-41/30) eventually. Therefore the full
third factorial cumulant is at least5*c(C)*N^(-41/30).
The factor5 is a convenient checked lower constant, not a sharp
leading coefficient. Every covariance sign, incompatible triple
and repeated occurrence is already included in the cancellation
theorem; none of these terms is discarded in the lower bound.

The joint theorem simultaneously supplies the lower bound for
K3plus on the actual positive-marginal ground set, for its third
factorial cumulant, and for the third factorial cumulant of the
full original dyadic count. The last equality uses the proved
exact restriction of all factorial moments to positive marginals.
It does not discard an exceptional-window event. The common
threshold precedes every critical length. All geometric inputs
are ordinary explicit theorem arguments, at the single fixed
source-cover cap GeneralGraphHostCount.sizeCap(1/30720), and
the corresponding explicitly displayed finite degree bounds.

No target cumulant lower bound, error estimate, arithmetic
exception count or rational witness density is assumed. There
is no new literature property, kernel axiom, dependency download,
Paper C port or source-manuscript edit. This does not complete
the sharp upper bound for the third cumulant or the remaining
aligned/primitive triple populations in article14.1/14.3/14.6.
Palomar remains deferred until the complete project is verified.

Verified under Lean v4.36.0-rc2: full build passed (12955 jobs); direct axiom audit passed for 9647 declarations using only propext, Classical.choice and Quot.sound; all 7801 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 14.18 GiB.


## Actual two-target sections and separate coordinate budgets

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

Verified under Lean v4.36.0-rc2: full build passed (12971 jobs); direct axiom audit passed for 9691 declarations using only propext, Classical.choice and Quot.sound; all 7863 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 14.16 GiB.


## P1-MATH-0121 — Whole label classes have bounded source coefficient covers

The coefficient stage can be carried out on whole nonzero
physical label classes. Their odd prime rows force short supports
through actual fixed source coordinates. The union of ALL potential
source supports of a class has explicitly bounded cardinality.
Its source-value product is divisible by the entire large odd
kernel of the class target product. One N^epsilon coefficient
pool depending only on the fixed sources consequently covers
every pair of targets, every recovery-regularized relation
subspace and every nonzero class, at fixed polynomial height.
No equal-label pairing, binary-component choice, subspace
enumeration or prime assignment is needed for this stage.


## Actual common coefficient pool for two free targets

The actual two-target coefficient enumeration in the proof of
article Lemma15.2 is now proved unconditionally, with a common
source-dependent pool before every target, recovery subspace and
nonzero label. The lemma remains in_progress: the dense pair host
counts and their weighted summation are still open. Completed
numbered coverage stays82/167. P1-MATH-0121 records the stronger
whole-label-class source-cover argument, bringing confirmed
mathematical improvements to121 without a source-conclusion error.

OddLabelCircuitSupport removes ALL occurrences of a nonzero
label alpha from an actual binary prime row in which its
multiplicity is odd. The remaining labels sum to alpha. A proved
short physical representation chooses a support D containing no
alpha label; therefore D has at least two elements. Adding one
alpha occurrence gives a sum-zero support F of at least three
distinct physical blocks. With only two free blocks, F contains
an actual fixed source. This is proved for the literal finite
prime row, including repeated occurrences of alpha elsewhere
in that row. Neither a pairing of equal labels nor a nonzero
relation on just the two targets is assumed.

TwoTargetPrimeClassSupports applies this fact to the actual
prime-valuation rows of PhysicalWindowRelations.code, indexed
by the s fixed source blocks and two free target blocks.
For p>H>=L+1, the already proved row equations and one-occurrence
per physical block give all finite hypotheses. If p has odd
valuation in a whole nonzero label-class product, the class's
row multiplicity is odd. A short support in its actual bounded
pool then contains a fixed source value divisible by p.
The two free targets may overlap or have exact contacts.
No affine compatibility or local full-rank premise is used.

PhysicalSupportPoolBudget proves an individual physical size
bound for EVERY potential short support. If its distinct label
image has at most d elements and each label fibre has at most K
coordinates, its size is at most d*K. Consequently all potential
supports through a class of at most K coordinates have total
count at most K*supportBound(d,t,K), and each has size at most
d*K+1 after inserting the marked class coordinate.

TwoTargetClassSourceCover takes the union of the SOURCE
coordinates in all those potential supports, together with
the source coordinates already in the class itself. Its
cardinality is bounded by the explicit fixed constant
  K + K*supportBound(d,t,K)*(d*K+1),
where K=t-1. This construction enumerates no prime assignment.
For d=s+1, the actual large odd kernel of the class's two-target
product divides the product of the actual source values in
this bounded cover. A prime already dividing the class source
product is included immediately; every other odd target prime
is odd in the whole class product and is covered by the proved
source-support theorem. All source values and divisibilities
are literal positive window integers.

SourceSupportedCoefficientPool defines a finite pool from all
source-coordinate subsets of bounded cardinality, divisors of
their actual products and divisors of the small-prime primorial.
Whenever the large odd kernel of an actual positive integer n
divides one such source product, its FULL squarefree kernel
belongs to that pool and provides the exact integer equation
IsSquare(D*n). There is no assumed square-equation coefficient
or target counting bound. SourceSupportedCoefficientCount then
proves the pool has at most N^epsilon entries uniformly on the
critical band and at every H<=D*(L+1). Bounded source-coordinate
choices cost a fixed polynomial in L+1. Source products have
fixed polynomial height, as does the primorial by its elementary
4^H bound. Proved divisor subpower estimates absorb all three
factors. The threshold precedes every actual source tuple.

TwoTargetClassCoefficients identifies the bounded cover with
actual indices among the s source windows. Its explicit
sourceBound(s,t) is independent of N, target centres, label,
effective relation subspace and choices of divisors. Every whole
nonzero class gives a coefficient in the SAME pool. Its full
squarefree target-product kernel has height at most N^(2K)
when the class contains at most K actual coordinates in the
dyadic critical windows. The coefficient is positive and its
product with the actual target-value product is an integer square.

TwoTargetCoefficientEnumeration.uniform_enumeration supplies
these conclusions simultaneously. Fix s,t,D,C,epsilon with
t>=2. Then choose one threshold before N,L,H, the source tuple,
both free targets, EVERY actual recovery-regularized physical
relation subspace M and EVERY nonzero coordinate label. For
each fixed actual source tuple, one coefficient list of size
at most N^epsilon contains all of their squarefree target-product
kernels, each positive and at most N^(2*(t-1)), with its exact
square equation. Arbitrary contacts and irregular windows are
allowed. No binary graph, deletion pattern, subspace pool,
or prime-by-prime assignment is enumerated in this coefficient
stage. This stronger auxiliary formulation is P1-MATH-0121;
it is not a claim that all later geometric selection steps
can already be omitted.

Stable internal input P1-ARITH-TWO-TARGET-COEFFICIENTS is proved.
The remaining bridge from the lifted effective relation space
to a physical-code subspace, the exclusion of weak aligned
small-curve alternatives, the two mixed/univariate count strata
and their weighted dense-pair mass are not completed here.
The current result supplies their actual arithmetic coefficient
pool; it does not assume any of their desired host counts.
There is no new external literature assumption, kernel axiom,
Paper C port, dependency download or manuscript-byte edit.
Palomar remains deferred.

Verified under Lean v4.36.0-rc2: full build passed (12989 jobs); direct axiom audit passed for 9722 declarations using only propext, Classical.choice and Quot.sound; all 7911 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 14.13 GiB.


## Effective recovery subspaces and literal two-target coefficients

The actual effective-kernel regularization in article15.2 now
passes to a genuine subspace P of the literal physical window
code. Its dimension loss remains measured in the EFFECTIVE
relation kernel, and both target projections stay injective.
This completes the algebraic/arithmetic bridge to the previously
proved common source coefficient pool. The dense pair geometric
selection, weak-alignment removal and weighted summation remain
open. The numbered coverage stays82/167, and the121 confirmed
mathematical improvements are unchanged.

RecoveryImage proves that intrinsic NoDisjointRecovery transfers
through any injective linear map, using the actual equivalence
from a subspace to its image. Nonzero dual labels pull back to
nonzero labels; every recovery equation pulls back literally.
The image has the same finite rank, and injective target
projections transfer through their exact commuting squares.
These statements work over any field.

TwoTargetCodeLift puts the actual three-section physical lift
inside PhysicalWindowRelations.code. The membership proof uses
the already verified even parity in every physical block and
the exact zero sum of all prime-valuation vectors. Each target
projection commutes with this lift and every code coordinate
form pulls back to the corresponding effective-kernel form.
Injectivity of either target projection proves injectivity of
the complete lift. No injectivity of a local square-class map,
target disjointness, regular window or chosen-basis count is
assumed.

TwoTargetIntrinsicClassCoefficients and TwoTargetIntrinsicEnumeration
strengthen the previous coefficient theorems: only intrinsic
NoDisjointRecovery is needed. The proof reconstructs coordinate
multiplicity and bounded support pools from that condition.
It does not require a codimension bound measured in the entire
physical code. This distinction matters for irregular windows:
the full physical code contains local relations that are absent
from the effective kernel, so an image's codimension there need
not equal its regularization loss. No such equality is asserted.
The source cover cardinality, full squarefree coefficient,
common N^epsilon pool, positive polynomial coefficient height
and actual integer square equation all remain unchanged.

TwoTargetPhysicalRegularization chooses t from s and xi before
every source tuple, both targets, L and W. It then produces the
image P of the SAME effective recovery subspace, with intrinsic
recovery exclusion, dim(P)>=dim(R)-xi*L/4 and two injective
literal target-coordinate projections. P's rank is proved equal
to the effective subspace rank through the image equivalence.
No second restriction of the relation space is made.

TwoTargetPhysicalBudgets supplies the actual nonzero coordinate
class partition on P. Every class has at most t-1 coordinates;
separately for j=0 and j=1, its classes satisfy
  #classes_meeting_target_j >= dim(P),
  2*dim(P) <= L+1+#classes_meeting_target_j_once.
These are consequences of the proved target injections and
the actual class partition, not assumed density premises.

TwoTargetPhysicalEnumeration.uniform_enumeration finally fixes
t before D,C,epsilon and the asymptotic threshold. For every
source tuple in the critical dyadic band, its one coefficient
list has at most N^epsilon entries. For every actual target
pair and arbitrary W inside the source sum, disjoint from each
target separately, it constructs the physical P above. EVERY
nonzero label on P has its actual full target-product kernel
in that SAME source-only list, positive and at most N^(2*(t-1)),
and multiplying the literal target product by it is an integer
square. Thus no enumeration of sections, recovery subspaces
or targets is inserted into the coefficient budget.

The source dimension deficit is still the genuine effective
one, including on irregular windows. This is an unconditional
internal bridge, not the full conditional dense-pair estimate.
There is no new literature input, mathematical-finding number,
kernel axiom, Paper C port, dependency download or source edit.
Palomar remains deferred.

Verified under Lean v4.36.0-rc2: full build passed (13003 jobs); direct axiom audit passed for 9738 declarations using only propext, Classical.choice and Quot.sound; all 7928 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 14.10 GiB.


## Actual mixed-class equations and nonaligned half-power hosts

The mixed, nonaligned geometric branch of article15.2 now
uses literal physical label classes and their actual source
coefficient list. The branch proves a uniform N^(1/2+epsilon)
bound when a fixed number of distinct nonzero classes each
meet BOTH targets. Its only unproved inputs are the existing
chosen-source surface-cover and normalized-curve properties,
as explicit theorem arguments. The pure-class alternative,
weak aligned pairs, upper singleton stratum and final weighted
dense mass are still open. Main15.2 remains in_progress;
unconditional numbered coverage82/167 and121 improvements
are unchanged.

CoefficientSplitRadicalPatterns enumerates bounded integer
offset sets and a fixed number of entries from ANY actual
finite positive coefficient list Q. It does not require these
coefficients to have only small prime factors. Its exact finite
cardinality is the old proved offset-pattern cardinality times
|Q|^k. CriticalCoefficientPatterns chooses the explicit positive
coefficient margin epsilon/(2*(k+1)); a list of that subpower
size and all offset patterns together cost at most N^epsilon
on the critical band. One threshold precedes every list Q.

CoefficientNonalignedHostCount applies the already proved
general integer-root host theorem for polynomial-height
coefficients. A finite cover over the ACTUAL pattern pool
then sums all root-system counts. This gives N^(1/2+epsilon)
for arbitrary positive coefficient lists with their explicit
small cardinality and height bounds. Offset sets can have
unequal degrees in different equations; they must be disjoint
within each target and nonempty in both targets. Literal
CompressedTargetAlignment nonalignment is retained, rather
than silently inferred for weak aligned pairs. The selected
homogenization and equation count precede the geometric inputs
and every N,L,Q and host set.

TwoTargetClassOffsets constructs the ACTUAL indices and integer
offsets of a physical class in each of the two target blocks.
Its target coordinate images partition precisely the nonsource
coordinates of the class. The two images are disjoint; their
offset cardinalities add to at most the physical class size.
Different classes have disjoint offsets separately in each
target. Each offset has absolute value at most L+1. The exact
integer product is proved equal to the previous literal
targetProduct, so its square equation gives actual integer
roots of the split product at the two target centres. These
are constructed data, not root equations postulated as inputs.

TwoTargetMixedClassData restricts the source-only coefficient
list to positive entries at most N^(2*(t-1)). This only decreases
its cardinality and retains EVERY actual nonzero class
coefficient, by the previously proved enumeration. Given any
fixed number of distinct nonzero mixed classes on an actual
intrinsic-recovery subspace M of the literal code, it constructs
one admissible bounded-coefficient pattern and all its integer
square roots. Both within-target disjointness conditions and
the total degree bound t-1 follow from the actual class
partition and recovery multiplicity. The enumeration threshold
precedes even this chosen equation count.

TwoTargetNonalignedMixedCount.uniform_hosts now supplies the
literal arithmetic branch: fix s,t,D,C,epsilon, choose the
geometric degree and number k of equations, then supply the
two existing uniform geometric properties. A common A and N0
bound EVERY finite set of actual dyadic target pairs above
EVERY actual fixed source tuple, whenever the pairs are
nonaligned and possess an actual intrinsic-recovery subspace
with k distinct nonzero classes meeting both targets. It gives
|F|<=A*N^(1/2+epsilon). The source coefficient pool, positivity,
polynomial height, offset patterns and roots are all internally
constructed. No pair host bound, assumed pattern enumeration,
subspace count or regular-window condition is an external
premise. This proves one branch of the dense-pair argument;
the assertion that density forces either that branch or the
univariate alternative is not yet supplied by this checkpoint.

The geometric inputs have the exact forms
UniformSourceSurfaceCover.UniformCover k (t-1) Ds and
UniformNormalizedCurvePointCount.UniformBound
((Ds+2).choose2+k) M for every M. Their standard identifiers
P1-GEO-CHOSEN-SOURCE-SURFACE-COVER and
P1-GEO-NORMALIZED-CURVE-UNIFORM remain unformalized literature
inputs. They are ordinary explicit arguments, never kernel
axioms. No new literature claim, finding, dependency download,
Paper C port or source-manuscript edit is made. Palomar remains
deferred.

Verified under Lean v4.36.0-rc2: full build passed (13015 jobs); direct axiom audit passed for 9766 declarations using only propext, Classical.choice and Quot.sound; all 7965 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 14.07 GiB.


## Complete lower nonaligned dense-pair cardinality stratum

The complete LOWER nonaligned cardinality stratum in article15.2
is now proved conditionally on the existing two explicit
chosen-source geometric properties. For arbitrary fixed actual
sources and arbitrary W inside their effective sum, the literal
dyadic nonaligned pairs with W disjoint from each target and
effective relation dimension at least eta*L have cardinality
O(N^(1/2+epsilon)). The dimension condition now internally
produces either enough mixed classes or two pure classes for
each target. It is not an assumed geometric host-count premise.
The upper singleton stratum, weak aligned pairs and weighted
dense mass remain open, so main15.2 stays in_progress. Coverage
remains82/167 and confirmed improvements remain121.

CoefficientUnivariateCount proves an unconditional pooled
one-variable count. Two actual NONEMPTY DISJOINT bounded
offset equations with positive integer coefficients from one
small common list have at most N^epsilon critical dyadic hosts.
This uses the previously proved DisjointSquareEquations bound;
no coefficient height or external curve estimate is needed for
this univariate branch. The pool of all bounded offset patterns
and pairs of coefficients costs the explicitly allocated
subpower margin. The threshold precedes every list, offset
pattern and host set. Counting both coordinate projections
then gives at most N^epsilon ordered pairs when each centre
has such a two-equation system from that SAME list. Correlation
between the chosen systems is allowed.

TwoTargetLabelSelection constructs the actual nonzero labels
in each target and their mixed intersection and pure differences.
Membership is proved equivalent to the corresponding physical
class meeting that target. A pure label has an EMPTY offset
set in the other target. An explicit finite-sampling theorem
selects distinct labels from any sufficiently large finite
population. If each target has at least k+2 labels, either k
distinct mixed labels can be selected, or two distinct pure
labels can be selected separately for EACH target. This is an
exact finite cardinality argument; no density assertion or
number of subspaces is supplied as an input.

TwoTargetPureClassData rewrites the previously proved literal
target-product square equation of a pure class to a genuine
one-variable equation: the other target's integer product is
the empty product one. Two distinct pure classes have disjoint
offsets in the chosen target. Their size and coefficient list
are supplied by intrinsic recovery and the actual common source
enumeration. For both target orientations, the actual system
is constructed, with all square conditions proved. A common
critical threshold precedes every actual source tuple, target
pair, recovery subspace and choice of the two labels.

TwoTargetPureCount.uniform_pairs proves the full PURE branch
unconditionally: any finite dyadic target-pair set admitting
these actual two pure classes in each target has at most
N^epsilon entries. The coefficient list depends only on the
fixed sources. Positivity and its subpower cardinality are
proved internally. There is no alignment, local regularity,
target disjointness or geometric literature hypothesis in this
pure-class theorem. The subspace and labels may vary with each
actual target pair.

TwoTargetLabelDimension explicitly identifies each target's
label population with its physical-class count, so the proved
injective projection gives dim(P)<=#target_labels separately
for the two targets. Both counts use the SAME actual P.

TwoTargetNonalignedDenseCount.uniform_pairs combines ALL these
steps. It first fixes the recovery parameter from s and eta,
then the chosen-source surface degree and number k of equations,
then takes exactly the existing surface-cover and normalized
curve properties as ordinary explicit arguments. It chooses a
uniform length threshold before every source tuple and W.
For every actual pair with d>=eta*L, effective regularization
gives dim(P)>=d-eta*L/4. On the critical band this exceeds k+2
for all sufficiently large N. Separate target injections and
the exact label dichotomy therefore give the actual mixed or
pure alternative. Partitioning the actual host set by mixed
existence, the mixed part has O(N^(1/2+epsilon)) cardinality
and the remaining pure part has at most N^epsilon cardinality.
Their sum gives the claimed bound with an explicit enlarged
constant. Sources and W are arbitrary, and irregular windows
remain included via the exact effective sections.

This theorem uses the genuine kernel dimension. The earlier
effective_dimension_formula proves that it is exactly the
printed dim(W)+dim(S_y)+dim(S_z)-dim(W+S_y+S_z), rather than
the full physical relation rank with local kernels. The
statement allows any finite set of the actual qualifying
dyadic pairs; source freshness and distinctness can be imposed
by taking a subset. No weighted mass estimate is claimed.

The two external properties retain their previous exact forms:
UniformSourceSurfaceCover.UniformCover k (t-1) Ds and
UniformNormalizedCurvePointCount.UniformBound
((Ds+2).choose2+k) M for every M. No new literature input,
kernel axiom, mathematical-finding identifier, Paper C port,
dependency download or manuscript source edit is introduced.
The full article15.2 conclusion and Palomar remain deferred.

Verified under Lean v4.36.0-rc2: full build passed (13027 jobs); direct axiom audit passed for 9779 declarations using only propext, Classical.choice and Quot.sound; all 7985 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 14.03 GiB.


## P1-MATH-0122 — Direct actual label-class proof of both nonaligned strata

For the NONALIGNED part of the two-target estimate, both
cardinality strata admit a direct proof on whole nonzero
coordinate label classes. Separate target ranks force many
mixed classes or two pure classes in each target. Above half
rank, the exact singleton budgets force a common degree-one
mixed type in one orientation, or the same pure alternative.
The pure branch needs only two disjoint nonempty square
equations with arbitrary nonzero integer coefficients; its
subpower bound is already proved internally. Thus no prime-row
pairing or binary-component graph is needed for these
nonaligned counting stages. The actual source-only coefficient
pool and the recorded geometric hypotheses suffice. This does
not yet extend the argument to weak aligned pairs.


## Complete upper nonaligned dense-pair cardinality stratum

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

Verified under Lean v4.36.0-rc2: full build passed (13045 jobs); direct axiom audit passed for 9791 declarations using only propext, Classical.choice and Quot.sound; all 8001 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 14.00 GiB.


## Literal nonaligned dense-pair mass above arbitrary effective sources

The full literal NONALIGNED weighted summand of article15.2
is now proved conditionally on the three existing geometric
properties. The theorem uses the exact actual heterogeneous
infinite-model marginals, the printed effective dimension
deficit, distinct target centres and exclusion of all fixed
source centres. It proves the N^(-1+epsilon) bound with one
threshold before every source tuple and W. Weak aligned pairs
and the full source-restricted primitive-family clause remain
open, so main15.2 stays in_progress. Proved numbered coverage
remains82/167 and confirmed improvements remain122.

TwoTargetNonalignedRankWeight proves the complete effective
rank-weight sum O(N^(1+epsilon)) over EVERY finite set of
actual qualifying nonaligned dyadic target pairs. It partitions
the actual set at d=(1/2+delta)*L. The previously proved lower
cardinality estimate and a proved critical binary-power bound
pay for the lower stratum. The upper cardinality estimate
and the genuine effective inequality d<=L pay for the upper
stratum. All internal margins are fixed before N. The two
regularization parameters and geometric equation counts are
chosen before the sources and W; they may differ between the
two strata. No abstract rank-weight bound is assumed as input,
and no physical local kernels are added to d.

TwoTargetNonalignedMass.uniform_mass multiplies this rank sum
by the proved uniform cap on the EXACT actual marginals.
Their nonnegativity and separate bounds give
p_y*p_z<=(M/N)^2, retaining all incompatible and irregular
windows as their actual probabilities dictate. Finite sums
are handled exactly, then the fixed multiplicative constant
is absorbed into the remaining exponent margin. The result is
sum(p_y*p_z*2^d)<=N^(-1+epsilon), uniformly over the actual
sources and every W inside their effective sum, when W is
disjoint from each target and d>=eta*L. There is no replacement
of the marginals by a homogeneous probability or assumption
of compatibility.

TwoTargetDensePairs defines the literal nonaligned population:
both centres lie in the dyadic block, are distinct and outside
every prescribed source centre, are nonaligned in the source's
exact sense, and satisfy the separate W disjointness and
effective density conditions. Its explicit deficit is
dim(W)+dim(S_y)+dim(S_z)-dim(W+S_y+S_z). The earlier exact
effective dimension formula proves this equals the actual
relation-kernel dimension for every W inside the source sum.
The membership equivalence records every restriction.

TwoTargetNonalignedMassTheorem.article_15_2_nonaligned now
states and proves the actual printed weighted nonaligned
summand on that explicit finite population, with the printed
deficit in both its membership condition and exponent. It
does not merely apply to an unspecified host set. The fixed
source tuple and W can be irregular or dependent; their
admissibility is precisely W<=sum(source spaces), with the
separate target disjointness imposed on the summation set.

The exact external arguments remain the existing chosen-source
surface cover for the lower mixed stratum, the ordinary surface
cover for the singleton stratum and normalized-curve bounds in
their two explicit ambient dimensions. These are the same
three recorded P1-GEO identifiers, without a new unformalized
input. Their translation from the literature is still open;
they remain ordinary explicit theorem parameters, not axioms.

This closes the nonaligned weighted part only. No theta for
weak aligned pairs, removal of their small curves, or full
source-restricted primitive dense mass is claimed. Those
unproved portions prevent completion of article15.2. There
is no new mathematical-finding number, Paper C port, dependency
download or original manuscript edit. Palomar remains deferred.

Verified under Lean v4.36.0-rc2: full build passed (13053 jobs); direct axiom audit passed for 9796 declarations using only propext, Classical.choice and Quot.sound; all 8008 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 13.97 GiB.


## Actual units and fixed selected grids for weak aligned targets

The arithmetic foundations for the weak aligned selection
stage of article15.2 are now proved unconditionally. Actual
units have the claimed lower effective intersection rank,
all but one unit can be excluded through boundedly many actual
coordinate labels, and the surviving fixed-size normalized
selections give the exact even independence and disjointness
required by the existing geometric host theorems. The remaining
population budgets after exclusion and their geometric host
count composition are not yet complete. Main15.2 remains
in_progress;82/167 proved numbered results and122 confirmed
mathematical improvements are unchanged.

EvenImageEmbeddingDefect uses the previously proved actual
extension by zero along a finite embedding. It constructs an
injective map from the selected even-map kernel into the full
even-map kernel and proves the finite-rank inequality. Over
any division ring, with no finite-dimension assumption on the
ambient value space, the selected image loses at most the
full image's defect from its formal even-selection dimension.
The outside-image zero evaluation is also proved. These are
actual maps and rank-nullity arguments, not assumed quotient
injectivity.

EvenSubsetRankDefect instantiates this on literal arithmetic
value sets S<=T:
  |S|-1<=rank(space(S))+(|T|-1-rank(space(T))).
UnitIntersectionRankLower applies it to the full normalized
intersection of the two actual windows. Normalized value-set
cardinality is proved equal to the actual unit count, and its
even image lies in the genuine target intersection. Combining
with the exact local rank identity gives the general finite
inequality
  #units<=dim(S_y intersect S_z)+local_relation_rank(y)+1.
Thus a local defect at most one gives the literal u-2 lower
intersection bound used in the companion. No private-prime
condition on the normalized union or local full-rank premise
is used. WeakAlignmentUnitCount then supplies one critical
threshold for EVERY actual pair and ALL positive channel
coefficients, with no height restriction. In the weak case it
gives u<=theta*L+2 from the actual effective intersection bound.

FiniteRungeIndependence first proves that absence of nonempty
even square-product subsets implies injectivity of the actual
even-selection map. The selected support and its product are
constructed from each hypothetical kernel vector. The proved
quantitative Runge theorem then rules out such a support in
[U,U+R] when its fixed cardinality is below the explicit
Runge threshold. CriticalFiniteRungeIndependence proves the
uniform consequence: for fixed K,D,J, EVERY actual set of at
most K integers in an interval of width at most D*(L+1)^J and
base U>=N/2 is even-independent on the critical band, above a
common N0. This is even independence, not an assertion that
each individual integer has a private prime or is nonsquare.

EvenIndependentIntersection proves the exact intersection
identity space(S intersect T)=space(S) intersect space(T)
under even independence of S union T. Equality of two actual
even combinations is extended into the common union, where
injectivity identifies their coefficients. Absent coefficients
vanish, so the common value is supported in the literal
intersection. Consequently normalized grids with at most one
common integer have disjoint even square-class spaces. Full
private-prime independence of the union is unnecessary for
this auxiliary identity.

CriticalAlignedSelections applies the finite Runge result to
the literal enlarged alignment coefficients a,b<=(L+1)^3.
The already proved enlarged pair geometry puts all deduplicated
normalized values in an interval of width at most6*(L+1)^4
with base at least N/2. A common threshold therefore makes
EVERY fixed-size selected normalized union even-independent,
including pairs with no exact unit and irregular full windows.
If the two selected normalized grids share at most one value,
the exact intersection identity and invariance under dilation
give even independence of each ORIGINAL selected grid and
disjointness of their ORIGINAL effective spaces. Both channel
orientations are included. No uniqueness-of-alignment assertion
or full-window independence is assumed.

TwoTargetUnitExclusion constructs the actual two physical
endpoints of each deleted unit and their coordinate-label
image. At most2*#deleted_units labels are excluded. Every
class with a surviving label avoids all those actual endpoints;
this removes selectable classes without restricting the
regularized relation subspace again. The exact finite
except_one construction deletes u-1 units when u>0, and zero
when u=0, leaving at most one. For selected target index sets
avoiding a deleted endpoint on each deleted unit, the literal
normalized selected value intersection has cardinality at
most one. It is covered by the image of the actual surviving
unit pairs, so no prime or alignment assignment is enumerated.

All these results are unconditional internal arithmetic and
linear algebra. They do not assume a weak aligned host count
or add an unformalized geometric input. The previously proved
nonaligned weighted clause remains complete under the recorded
geometry. To complete the weak aligned clause, the remaining
target and singleton populations after this actual label
exclusion must still be linked to the mixed/pure selection
and the existing selected-admissibility host counts. The full
source-restricted primitive clause also remains open.
No kernel axiom, new finding identifier, dependency download,
Paper C port or source-manuscript edit is added. Palomar remains
deferred.

Verified under Lean v4.36.0-rc2: full build passed (13071 jobs); direct axiom audit passed for 9820 declarations using only propext, Classical.choice and Quot.sound; all 8035 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 13.94 GiB.


## P1-MATH-0123 — Selected-grid admissibility from one supplied alignment

The small-curve removal stage for weak aligned targets can
use any one bounded alignment supplied by the actual alignment
condition. Its unit count is controlled by the effective
intersection. Exclude classes touching all but at most one
unit of that chosen channel. For every FIXED number of selected
coordinates, the deduplicated values normalized by its two
channel coefficients lie in one polynomial-logarithmic interval.
The proved Runge bound gives even independence of this small
union, and its at-most-one overlap gives exact selected-space
disjointness. Thus the actual selected grids satisfy the
geometric admissibility properties directly. No uniqueness
proof for the global alignment is required for this local
stage, and no claim about units on all other channels is needed.
The full weak aligned population count is still separate.


## Actual selected-grid arithmetic and pooled geometric counts

The literal selected grids of actual classes now supply the
geometric admissibility needed for weak aligned targets, and
the two common-coefficient geometric counts are proved with
that selected admissibility in place of global nonalignment.
The remaining class populations after exclusion and the full
weak aligned dense host counts are still open. Main15.2 stays
in_progress, with82/167 proved numbered results. P1-MATH-0123
records the chosen-alignment finite-selection proof of this
admissibility stage, bringing confirmed improvements to123.

CoefficientPatternGrids constructs the two actual unions of
the root sets in a finite coefficient pattern. Each equation's
root sets lie in these unions, whose combined cardinality is
at most k*K when every equation has total degree at most K.
Their actual integer-value sets have no larger cardinality.
These are fixed-size selected grids, rather than full window
sets.

CoefficientSelectedHostCount proves the half-power geometric
bound after summing all bounded offset and common-list
coefficient patterns. It uses GeneralRootHostCount on the
actual selected grids, with their explicit positivity, even
independence and effective disjointness. The host need not be
globally nonaligned. These arithmetic admissibility conditions
are precise hypotheses about actual finite value sets, not an
assumed host bound. Only the existing chosen-source surface
cover and normalized-curve properties remain external inputs.

SelectedDegreeOneRootHostCount constructs the literal integer
radicand list and reindexes every root, degree and disjointness
condition. OrdinaryDyadicRootHostCount then supplies N^epsilon
hosts when the selected grids are admissible. It chooses a
positive fixed number of equations before the geometry and N.
The ordinary affine-curve input is again obtained through the
proved normalized-curve specialization. This theorem retains
polynomial-height integer coefficients and works on either
selected target orientation without a global nonalignment
premise.

CoefficientSelectedDegreeOneHostCount pools that actual
degree-one theorem over the common finite coefficient list.
A pattern's singleton right offsets are constructed and proved
distinct; its positive left degree is fixed within that pattern
and may vary across patterns. Positivity and polynomial height
of coefficients and the small list cardinality are explicit.
The resulting N^epsilon bound has one threshold before every
actual list, pattern and host set. The existing ordinary surface
cover and normalized-curve properties are its only unproved
inputs.

TwoTargetSelectedGrids identifies the actual integer offsets
of any fixed number of physical classes with the image of
their actual target indices. Their evaluated natural values
are proved exactly equal to the actual original window labels.
Both selected grids are positive and lie in their original
windows. Their total index cardinality is at most k*K. If the
physical classes avoid every endpoint of deleted actual units,
their selected indices avoid every deleted unit. The actual
normalized selected value intersection consequently has at
most one element when all but at most one unit have been
deleted. No root set, integer value or unit membership is
postulated as a geometric input.

WeakAlignedSelectedGrids.uniform_admissible finally constructs
the COMPLETE SourceCurvePointCover.Admissible property for
these actual class grids. For any supplied bounded enlarged
alignment, any fixed number of classes of fixed bounded size,
and any actual unit deletion leaving at most one unit, the
proved finite Runge independence and one-overlap intersection
identity give positivity, even independence of each original
selected grid and disjointness of their actual effective
spaces. It supplies BOTH target orientations above one
threshold chosen before all sources, targets, alignment data,
classes and deletions. The regularized relation space is not
restricted again.

This establishes the selected-admissibility mechanism needed
by the two pooled geometric host bounds. To close the weak
aligned dense estimate, the available target and singleton
label counts after deletion must still be shown sufficient,
and actual admissible patterns must be selected and counted.
The weighted weak aligned and source-restricted primitive
clauses remain unproved. There is no additional literature
input, kernel axiom, Paper C port, dependency download or
source-manuscript edit. Palomar remains deferred.

Verified under Lean v4.36.0-rc2: full build passed (13083 jobs); direct axiom audit passed for 9838 declarations using only propext, Classical.choice and Quot.sound; all 8057 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 13.91 GiB.


## P1-MATH-0124 — Subtract excluded singleton labels once

After excluding a common set E of endpoint labels, count the
surviving singleton labels directly. Before exclusion, each
target satisfies 2*dim(P)<=B+n_singleton. At most |E| of those
singleton labels are removed, so the surviving population is
at least 2*dim(P)-B-|E|. In contrast, applying the generic
inequality n_singleton_remaining>=2*m_remaining-B after
m_remaining>=dim(P)-|E| loses 2*|E|. The direct budget saves
one entire exclusion cost, without restricting P or changing
its coordinate labels or coefficient list. With the actual
unit exclusion |E|<=2*theta*L+2 this yields the proved lower
bound 2*d-xi*L/2-B-(2*theta*L+2) and the upper-stratum count.


## Complete dense-pair first conclusion, including weak alignment

The complete FIRST conclusion of article Lemma15.2 is now
proved under exactly the previously inventoried geometric
properties. This includes the literal union of nonaligned
pairs and pairs with effective target intersection at most
a fixed positive theta*L. The printed effective deficit,
exact heterogeneous marginals, distinct targets and exclusion
of all source centers are retained. The uniform threshold is
chosen before all sources, their effective subspace W and the
targets. The source-restricted primitive-family conclusion
remains open, so main15.2 stays in_progress and unconditional
numbered coverage stays82/167. P1-MATH-0124 records the sharper
post-exclusion singleton budget, bringing improvements to124.

TwoTargetAllowedLabels removes a COMMON finite label set E
from each actual target population. Each original population
has cardinality at most the remaining population plus |E|.
Its exact mixed-or-two-pure dichotomy returns only labels
outside E. A label outside E that is pure among the remaining
targets is also pure in the original physical classes.
TwoTargetAllowedSingletonSelection proves the analogous
singleton dichotomy, using a finite fixed-degree sampling
lemma. It chooses either k distinct surviving mixed classes
with a common positive opposite degree and singleton degree
in one target, or two surviving actual pure classes per target.

TwoTargetWeakRegularization chooses the recovery parameter t
from s and the dimension-loss margin BEFORE C, theta and N.
For any actual weak aligned pair, choose any one supplied
bounded enlarged alignment a,b. The actual unit count is at
most theta*L+2. Removing all but at most one unit gives an
actual deletion D and its endpoint-label image E with
|E|<=2*theta*L+2, including the empty-unit case. The SAME
physical relation space P, recovery exclusion and coefficient
list are retained. For EACH target separately the surviving
label population is at least d-xi*L/4-(2*theta*L+2), and its
surviving singleton population is at least
2*d-xi*L/2-(L+1)-(2*theta*L+2). The latter subtracts |E| once,
rather than twice as in recomputing 2*m_remaining-(L+1).

TwoTargetOrientedClassPattern constructs one literal pattern
from the actual label classes and exposes its exact left and
right selected grids, pool membership, mixed and degree-one
validity and integer square roots in both orientations.
TwoTargetSelectedClassData combines it with the common
source-only coefficient list and proved finite-Runge selected
grid admissibility. Every selected nonzero label outside the
actual endpoint-label image yields actual bounded-size classes
avoiding all deleted endpoints. Their coefficients are
positive, at most N^(2*(t-1)), and drawn from one subpower list.
No chosen equation, grid, coefficient or host bound is an
additional arithmetic hypothesis.

TwoTargetWeakMixedCount and TwoTargetWeakSingletonCount apply
the existing chosen-source and ordinary geometric host counts
to those actual patterns. Their sole unproved properties remain
the inventoried source-surface cover, ordinary-surface cover
and normalized-curve count, at explicitly displayed finite
parameters fixed before N. The selected equations and their
admissibility are constructed internally. The mixed branch is
N^(1/2+epsilon); a fixed singleton orientation is N^epsilon.

TwoTargetWeakDenseCount uses xi=eta and intersection at most
eta*L/64. Positive effective relation rank d>=eta*L supplies
enough surviving target labels, hence the safe mixed/pure
alternatives and the complete half-power count. The pure
alternative uses the previously proved unconditional two-
equation count in each target. TwoTargetWeakUpperCount uses
xi=delta and intersection at most delta*L/64. When
 d>=(1/2+delta)*L the surviving singleton budget forces a
safe fixed-degree singleton orientation or the pure case,
giving the complete N^epsilon upper-stratum count.

TwoTargetWeakRankWeight chooses the positive theta as the
minimum of the two fixed intersection thresholds, and combines
the actual two rank strata with the full factor2^d. The actual
effective kernel has dimension at most L, including irregular
source and target windows. TwoTargetWeakMass multiplies by
the exact actual marginals and uses the uniform marginal cap
to prove mass<=N^(-1+epsilon). TwoTargetDenseMass partitions any
actual host population into its nonaligned and remaining weak
aligned parts and absorbs the finite sum into the margin.

TwoTargetAdmissibleDensePairs defines the literal full dense
population, including distinctness and all source exclusions,
and proves that every direct target pair satisfies its pair
condition. TwoTargetDensePairTheorem.article_15_2_dense_pair
then states the complete first displayed bound of15.2 with
the PRINTED deficit, using its proved equality with the actual
effective relation-kernel dimension. It is stronger than the
printed big-O bound because the constant is absorbed after a
common threshold. The primitive source-restricted displayed
bound still needs the exact family decomposition and source
marginal summation. No numbered completion is claimed yet.

No new external literature property, kernel axiom, dependency
download, Paper C port or source-manuscript edit is introduced.
Palomar remains deferred until full coverage and verification.

Verified under Lean v4.36.0-rc2: full build passed (13111 jobs); direct axiom audit passed for 9866 declarations using only propext, Classical.choice and Quot.sound; all 8093 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 13.85 GiB.


## Conditional completion of both conclusions of article15.2

Article Lemma15.2 is now COMPLETE CONDITIONALLY, including
BOTH of its literal displayed conclusions. The previous
checkpoint proved the full nonaligned-or-weak-aligned pair
mass, with source exclusion and the printed effective deficit.
The new SourceRestrictedDenseMass.article_15_2_source_restricted
proves the source-restricted dense homogeneous mass for actual
unordered primitive families of every fixed size r>=3.
Main15.2 moves from in_progress to conditional. Exactly the
three previously inventoried geometric properties remain
unproved; there is no additional source-restricted host-count
input. Unconditional numbered coverage stays82/167, while
conditional numbered coverage rises from14 to15. Confirmed
mathematical improvements remain124.

TwoTargetPrimitiveCut proves the exact generic algebra behind
the primitive consequence. Zero nullity on a disjoint union
forces its two actual effective spans to be direct. For a
nonempty source family E and two distinct targets outside E,
zero nullity of every proper subfamily gives directness of
each target from the complete source span and directness of
the two targets. The source family itself is direct. Its rank
sum therefore equals its effective span rank, and the full
relative nullity is exactly the two-target dimension deficit.
These facts concern actual effective spaces and remain valid
with local relations in the individual windows.

TwoTargetFamilyCover constructs the actual family obtained by
inserting two distinct targets outside E, and the actual finite
pair population whose resulting family belongs to F. Every
I containing E with |I|=|E|+2 is such an actual extension. A
proved nonnegative weighted cover bounds the sum over actual
unordered families by the sum over their prescribed source
collection and actual target pairs. It allows multiple source
representations and both target orders without any equality
or undercounting claim. No combinatorial cover is assumed.

TwoTargetPrimitiveData instantiates the generic primitive cut
for actual square-class spaces. It identifies the span of the
source set exactly with the indexed span of its injective
finite enumeration. For every actual primitive extension, the
full nullity equals the actual effective Kernel dimension;
its two targets are direct and hence satisfy the proved dense
pair condition for every nonnegative intersection threshold.
The heterogeneous homogeneous weight factors EXACTLY into
the actual source marginal product times p_y*p_z*2^d. The
source marginal product is bounded by the corresponding fixed
power of the uniform marginal cap.

TwoTargetPrimitiveExtensions applies the already proved full
dense-pair mass to each actual source set E of fixed positive
size s, before summing sources. Its geometric parameters and
common N0 precede all E, all actual primitive extension
populations F and every choice of targets. The direct target
pair condition is proved internally from primitiveness. With
M(C)=2*2^C it bounds the complete actual extension weight by
(M(C)/N)^s*N^(-1+epsilon). All factors are exact heterogeneous
marginals, and all arithmetic assumptions needed by the
conditional geometric bounds have already been proved.

SourceRestrictedDenseMass.article_15_2_source_restricted now
sums these actual extensions. The prescribed source collection
has actual sets of size r-2 in the dyadic block and cardinality
at most N^(a+epsilon/4). Each actual family in F lies in that
block, has size r, is primitive, has relative nullity at least
eta*L, and contains a member of that prescribed collection.
The proved finite weighted cover and source caps give mass at
most M(C)^(r-2)*N^(-(r-1)+a+epsilon/2). The fixed constant is
absorbed after one common threshold, yielding the literal
N^(-(r-1)+a+epsilon) conclusion. The source-count epsilon/4
makes explicit the companion's instruction to divide the final
exponent margin between the source count and conditional
estimate. It expresses the usual arbitrarily-small-margin
source-count hypothesis without spending the final margin
twice. The theorem uses the actual PrimitiveWindowMass.mass,
which is the printed sum of (product p_i)*2^rho(I).

The existing source-surface cover, ordinary-surface cover and
normalized-curve properties remain ordinary explicit theorem
arguments at fixed displayed finite parameters. Their imported
arithmetic preparation is proved; their geometric literature
translation is still open. Accordingly this completion is
conditional, not an unconditional proof or Palomar record.
There is no new literature property, mathematical finding,
axiom, dependency download, Paper C port or manuscript-source
edit. The original V1.6 sources remain byte-for-byte preserved.

Verified under Lean v4.36.0-rc2: full build passed (13121 jobs); direct axiom audit passed for 9881 declarations using only propext, Classical.choice and Quot.sound; all 8111 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 13.82 GiB.


## P1-MATH-0125 — Two whole classes suffice for one dense bounded-width target

A dense single free target above fixed sources can be counted
using just two whole coordinate-label classes. Lift the actual
effective intersection into a physical relation code with an
identically zero auxiliary target; regularization preserves
many distinct nonzero labels in the free target. Every such
class is pure there and supplies one actual square equation
whose full squarefree coefficient belongs to one source-only
subpower list. Two distinct classes have disjoint nonempty
root sets, so the proved unconditional two-equation count
already gives N^epsilon targets. Upper logarithmic width alone
suffices for both coefficient and offset enumeration. Enclosing
an arbitrary bounded-width compressed set in one longer original
window therefore proves the compressed-target count without
the old product-certificate/residual-group dichotomy or an
injectivity hypothesis for the compressed map.


## Unconditional completion of article15.3

Article Lemma15.3 is now proved UNCONDITIONALLY, for the actual
compressed-center population of every fixed positive channel
0<a<=b. DenseCompressedTargetCount.article_15_3 includes ALL
actual unit-offset patterns and the exact effective prescribed
space W. Coprimality, strict channel ordering, private primes,
local regularity and injectivity of the compressed selection
map are not needed for this stronger count. Main15.3 moves
from not_started to proved. Unconditional numbered coverage
rises from82 to83/167; the15 conditional results stay separate.
P1-MATH-0125 records the two-whole-class proof at logarithmic
width, bringing confirmed mathematical improvements to125.

LogarithmicSourceCoefficientCount proves the common source-
only coefficient pool bound with only an upper logarithmic
width for the actual source coordinate set and the prime
cutoff. Actual source values have the explicit height bound
N^2. The threshold precedes every source-value list, length
and cutoff. LogarithmicCoefficientPatterns proves the bounded
offset and common-list pattern count under the same upper
width alone. LogarithmicUnivariateCount then applies the
proved unconditional two-disjoint-square-equation estimate on
any fixed comparable positive interval. Its integer coefficients
need only be nonzero and come from a common subpower list;
no coefficient height or unformalized curve estimate is used.

IntersectionKernelLift embeds W intersect S_y in the actual
two-target relation kernel by (u,-u,0). Its auxiliary target
projection is identically zero and its first target projection
is injective. OneTargetPhysicalLift composes this with the
proved arbitrary effective sections, obtaining an injective
physical lift of the ACTUAL intersection. Sources may overlap,
be dependent or have local relations.

OneTargetPhysicalRegularization chooses t from the source
number and rank margin before all actual windows and W. It
regularizes the pulled-back physical coordinate forms and
pushes the shared subspace into the literal physical code.
The image has intrinsic recovery exclusion, retains rank at
least dim(W intersect S_y)-xi*L/4, has injective first target
projection and still has identically zero auxiliary target.
The first target separately has at least dim(P) distinct
nonzero coordinate labels. Every nonzero class has no
coordinate at all in the auxiliary target.

OneTargetClassSystem consequently chooses just TWO distinct
actual target labels. Their physical classes have uniformly
bounded size, disjoint nonempty target offsets and coefficients
in the common full squarefree source-only list. The actual
square roots and both univariate square equations are proved.
OneTargetLogDenseCount combines these constructions with the
logarithmic pool and two-equation counts. It gives N^epsilon
actual dense targets on every fixed comparable positive interval,
for ANY sufficiently large logarithmic length, above ANY
prescribed subspace of the actual source span. The threshold
precedes every source, W, target population and actual code.
The old strict-product-certificate/residual-prime-group
classification is not required for this alternative proof.

BoundedWidthWindows embeds every actual finite set in
X+[-R,R] into the complete original window starting at
X-R+1 with length2R. It proves monotonicity of the actual even
square-class spaces and injectivity of this shifted center
once X>=R. BoundedWidthDenseCount uses this embedding with
R=D*(L+1). The enlarged length remains logarithmic; all old
source windows embed in the corresponding longer source
windows. Their actual values satisfy the fixed height bound
uniformly. A fixed reduced density margin retains the original
intersection threshold eta*L. The shifted center stays in a
fixed comparable positive interval. Thus the count applies to
EVERY actual family U_X of bounded width, even when it varies
with X and has local square relations. No injectivity of its
even-selection map is assumed.

CompressedTargetCenters constructs the actual centers as the
image of actual dyadic source pairs with an exact unit at the
chosen two offsets. Its block is exactly the previously proved
compressed union of the two normalized windows. Its width is
at most b*(L+1), with center between N/2 and3*b*N. The literal
dense population filters the actual effective intersection
with W. Every actual compressed pair satisfying that rank
condition is proved to belong to the population, and all unit
offset patterns are included in allDenseCenters.

DenseCompressedTargetCount first applies the general bounded-
width count uniformly to every offset pair. It then sums all
(L+1)^2 choices, absorbing this factor into the exponent margin.
The final article_15_3 theorem counts the actual compressed
centers, with one N0 before the critical length, every source
tuple, every W and all offset patterns. It proves card<=N^epsilon,
which implies the printed big-O conclusion. A fixed finite
set of channels can be summed with the same margin convention.
This proof uses only established unconditional arithmetic,
linear algebra and two-equation estimates.

There is no new external literature property, kernel axiom,
dependency download, Paper C port or manuscript-source edit.
The broader project remains incomplete and Palomar is deferred.

Verified under Lean v4.36.0-rc2: full build passed (13145 jobs); direct axiom audit passed for 9906 declarations using only propext, Classical.choice and Quot.sound; all 8141 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 13.77 GiB.


## P1-MATH-0126 — Minimal relative seeds unify fixed pair extensions

Choose a minimal nonempty subset of the new target indices
for which the prescribed source span and those targets fail
directness. Its actual relative addition kernel is positive,
and deleting any target makes that kernel zero. Hence one actual
relation has a nonzero component at EVERY target, while its old
source component is allowed to be zero. This single construction
covers both cases in the printed proof: an internal relation
among new targets and a relation meeting the old pair span.
The singleton case agrees exactly with the unary target deficit;
all larger minimal subsets enter the same conditional half-count.
Finite weighted coverage proves D_k<=(M+1)^k*(D_1+k*Q*A_2)
with the actual heterogeneous marginals. This gives an explicit
finite combinatorial bridge and avoids a separate preliminary
test for internal directness. The argument is fixed-order only.


## Conditional completion of article15.7

Article Lemma15.7 is now complete CONDITIONALLY on exactly the
three already recorded geometric properties used for article11.1:
chosen-source surface covers, ordinary surface covers and uniform
normalized-curve point bounds. No additional analytic premise or
desired extension bound is assumed. Main15.7 moves from not_started
to conditional. Unconditional coverage remains83/167; conditional
coverage rises from15 to16, separately. P1-MATH-0126 records a
minimal-relative-seed simplification of the proof. All original
manuscript bytes are preserved and Palomar remains deferred.

ErasedNullityRelations proves that a positive actual relation
space, whose erasures vanish at designated target indices, has
one actual relation nonzero at every designated target. Other
reserved components are allowed to vanish. MinimalRelativeRelations
adds one actual source span as an Option-indexed block, proves
the exact relative dimension identity, identifies zero nullity
with the existing compressed directness predicate, and extracts
a minimal nonempty target subset and its full-target-support
relative relation. The source component may be zero. This handles
both internal target dependence and dependence on the old source
span with the same actual construction.

RelativeWindowFamilies defines actual unordered target families
with a nonzero participating vector at each target, above the
prescribed source space. It proves coverage by injective actual
enumerations in the existing conditional half-count population.
RelativeOriginalWindowMass proves, unconditionally and uniformly,
count at most N^(h/2+delta) and independent heterogeneous mass at
most N^(-h/2+delta), for any fixed h and any prescribed space
inside the sum of a fixed number of actual old dyadic windows.
The one threshold precedes N,L,all source centers,the prescribed
space and the actual target ground set. All exact marginals,
including zero marginals, remain unchanged.

FixedPairExtensions defines precisely the actual U disjoint from
the pair e, of cardinality k, for which the compressed source
space and the individual new spaces fail directness. Its proved
membership equivalence uses the existing literal compressed-block
directness predicate. Every such U contains a minimal relative
seed of some size1<=h<=k. Actual finite weighted coverage and the
seed product estimate bound all remaining independent factors by
(M+1)^k when the total actual marginal mean is at most M. At h=1,
the seed mass is exactly the marginal sum over targets meeting
the pair span. Summing over ALL dyadic pairs gives precisely the
previous IndependentTargetDeficit: pair activity vanishes for
direct pairs. No positivity restriction on the actual activity
or Bernoulli marginals is introduced.

The exact finite bound is
D_k <= (M+1)^k * (D_1 + k*Q*A_2),
where Q uniformly bounds every seed mass of size2 through k,
D_1 is the literal unary deficit and A_2 is the full actual
absolute pair activity. The actual mean bound gives M=2*2^C.
With delta=epsilon/8 the proved relative half-count gives
Q=N^(-1+delta); article11.1 gives D_1<=N^(-3/2+delta)
and A_2<=N^(-2/3+delta). The higher-seed contribution is
therefore at most N^(-5/3+2*delta), and the finite k-dependent
constant is absorbed into the exponent margin.

FixedPairExtensionDeficitUnderInputs.article_15_7 proves the
literal final N^(-3/2+epsilon) bound. The finite geometric caps
are chosen before the corresponding geometric arguments, then
the common threshold precedes every actual N,L and G subset of
the dyadic block. The threshold may depend on fixed k,C,epsilon;
no growing-order or all-cardinality conclusion is asserted.
The geometric properties themselves remain unformalized inputs.
No new dependency, PaperC port or registration is added.

Verified under Lean v4.36.0-rc2: full build passed (13157 jobs); direct axiom audit passed for 9931 declarations using only propext, Classical.choice and Quot.sound; all 8176 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 13.74 GiB.


## P1-MATH-0127 — Independent tails need only coordinatewise participation

The two-anchor certificate alternative only needs a nonzero
effective relation component at the currently exposed window.
The relation can be chosen separately for each window. If a
family has an enumeration with no moderate certificate, every
unmarked vertex therefore has an actual saturation neighbor,
even if there is no single relation nonzero in every block.
The exact factorial enumeration and a uniform cardinality tilt
then give the entire a<2 independent tail for this larger
participating-family population. This proves the original-window
full-support assertion as a special case. No primitivity,
separation, regularity or common full-support relation is needed
for the stronger tail. This does not apply to positive masses
containing a factor2^rho, or yet to a compressed block.


## Original-window all-cardinality independent tail

The ORIGINAL-WINDOW assertion of article Lemma15.8 is now proved
UNCONDITIONALLY at all cardinalities. For every fixed v>0,a<2 and
epsilon>0, one fixed cutoff s and one threshold precede all N,L
and all actual dyadic ground sets. The literal sum over actual
full-support families of cardinality at least s, weighted by
the exact product of v*p_x, is at most N^(-a+epsilon). Overlapping
windows, local relations, incompatible affine systems and zero
marginals are all retained. The separate assertion with one fixed
compressed block is NOT yet proved. Main15.8 moves to in_progress;
unconditional coverage stays83/167 and conditional coverage16.
P1-MATH-0127 records the stronger participating-family bridge.

ParticipatingWindowCertificates lifts actual effective relations
to actual even physical window words. A selected large odd prime
has an actual receiving value with ODD valuation in another
window, not just a divisibility witness. Every unmarked window
that participates in some actual relation yields either an actual
moderate certificate for the entire tuple or an actual outgoing
saturation edge. The proof is uniform in the finite order; no
bound on the number of windows or growing-order constant is used.
The existing moderate and saturation estimates are then applied
to their exact original arithmetic populations.

AllFamilyEnumerations injects every actual unordered family
together with ALL permutations of its enumeration into the
actual tuple population. It proves F.card*r!<=tuplePopulation.card.
WindowCertificateFamilies uses a universal enumeration predicate
for certified families and proves that a family failing this
predicate has an actual enumeration with no moderate certificate.
The coordinate alternative makes its literal subtype vertex set
admissible in the actual marked saturation graph. Exact vertex
images and cardinalities are proved. WindowCertificateMass uses
the factorial divisor at every order and then sums the actual
finite family layers against the already proved summable moderate
certificate series. The factorial never estimates the growth
of an arithmetic constant depending on the order.

MarkedWindowCount proves the actual marked-center count
N^[1-(1-beta)*(1-sigma)+epsilon] for Y=log(N)^A,T=N^beta,
provided sigma>=1/2,sigma<1,A*(1-sigma)<1. It starts from an
actual B-position cover of marked centers and the proved Rankin
bound. Upper logarithmic width alone suffices for this count.
PowerTiltedGraphTail applies the actual marked-star generator.
UniformGraphCardinalityTail has ONE threshold before every
cardinality cutoff s and every finite graph: if its vertex count
is at most N and both mark count and maximum degree are at most
N^(1-2*theta), its independent tail with weight at most M/N is
at most N^(-theta*s+epsilon). Tilting by N^theta leaves the full
generating function bounded by exp(M+8*M^2).

OriginalParticipatingTail splits an actual finite population by
its certificate predicate and proves its mass is at most
N^(-2*beta+4/A+epsilon)+N^(-theta*s+epsilon). Its threshold precedes
all orders, every nonnegative heterogeneous weight function
bounded by M/N, and every actual family population in the dyadic
block. Crucially it needs only that EACH target participates in
SOME relation; a single relation using all targets is unnecessary.
Explicit parameter choices prove the subcritical a<2 tail with
s fixed before N. FullSupportIndependentTail.article_15_8_original
specializes this stronger statement to the literal actual
full-support population and the true Bernoulli marginals.

No geometric input, desired target estimate, dependency download,
PaperC port, manuscript-byte change or Palomar registration is
added. Compressed blocks, the all-cardinality pair deficit and
positive or centered masses amplified by relative nullity remain
separate open tasks.

Verified under Lean v4.36.0-rc2: full build passed (13177 jobs); direct axiom audit passed for 9958 declarations using only propext, Classical.choice and Quot.sound; all 8209 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 13.69 GiB.


## P1-MATH-0128 — The independent full-support exponent improves to one

The proved fixed-order half-exponent count gives independent
mass N^(-r/2+epsilon) for coordinatewise participating actual
families. Combine its finitely many orders below a fixed cutoff
with the already uniform all-cardinality certificate tail, using
a=1 in that tail. Every nontrivial family has size at least two,
so the entire sum is N^(-1+epsilon). The exact r! enumeration
then gives this stronger bound for all injective full-support
ordered lists with nominal weights, even without separation or
regularity, and with one threshold before all cutoffs s>=2.
This strengthens T22.1's exponent2*s/(2*s+1) to1. It applies
to arbitrary nonnegative heterogeneous product weights capped
by M/N at the unordered level. Positive joint probabilities or
centered activities with relative-nullity factors are not covered.


## Unconditional completion of companion T22.1

Companion Proposition T22.1 is now proved UNCONDITIONALLY,
including the literal ordered-list sum with weights u^r/r!
and nominal factor p^r, p=2^(-L). The actual manuscript list
population requires distinct dyadic starts, full effective
support, rank L at every window, and pairwise distance greater
than L. FullSupportOrderedLists.mem_manuscriptLists identifies
all these actual conditions. No minimality or affine
compatibility is imposed. The printed bound is exactly
N^(-2*s/(2*s+1)+epsilon) for each fixed s>=2.
T22.1 moves from not_started to proved. Unconditional numbered
coverage rises from83 to84/167; the16 conditional results stay
separate. P1-MATH-0128 records a stronger N^(-1+epsilon) bound.

FamilyEnumerationUpper proves the reverse factorial inequality
by injecting actual ordered tuples into their actual finite
family and the permutation of its canonical enumeration.
Together with the previously proved forward injection it gives
the exact identity #lists=r!*#unorderedFamilies. It includes
empty and singleton orders as well. FullSupportOrderedLists
proves the exact cardinality identity for the real full-support
tuple population, cancels the actual factorial, and identifies
the sum over all orders with the actual unordered family sum.
The nominal-weight formula is exactly the expression printed
in T22.1. The manuscript population is a proved subset of this
larger actual list population, so its weighted count follows
without a counting assumption.

OriginalParticipatingMass.fixed_mass proves independent mass
at most N^(-r/2+epsilon) at each fixed order r, for arbitrary
nonnegative heterogeneous weights bounded by M/N and actual
coordinatewise participating families. It uses the proved
relative half-count with no old sources, and the actual family
inclusion, not a supplied desired host estimate.
OriginalParticipatingMass.uniform_mass combines these finitely
many fixed-order bounds with OriginalParticipatingTail's uniform
all-cardinality tail. The small-order cutoff is chosen before N;
only the finitely many orders below that cutoff use their own
fixed-order thresholds. The large orders use the already proved
uniform certificate generator. The total mass of ALL such
families of size at least two is at most N^(-1+epsilon).
The threshold precedes every actual weight function and family
population; zero weights and all actual overlaps are allowed.

FullSupportWeightedCount.uniform_ordered_mass specializes to
the nominal constant weight u*2^(-L), whose cap is proved from
the critical-band condition. It gives N^(-1+epsilon) for the
larger actual injective full-support list population, without
regularity or separation, with one threshold before EVERY
cutoff s>=2. The stated source exponent follows because
2*s/(2*s+1)<=1. FullSupportWeightedCount.companion_T22_1 then
restricts to the literal separated regular manuscript lists.

The strengthening concerns INDEPENDENT product weights. It
does not establish positive joint or centered masses containing
the factor2^rho, nor the separate compressed-block assertion of
main15.8. No geometric input, dependency download, PaperC port,
original manuscript edit or Palomar registration is added.

Verified under Lean v4.36.0-rc2: full build passed (13185 jobs); direct axiom audit passed for 9974 declarations using only propext, Classical.choice and Quot.sound; all 8229 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 13.67 GiB.


## Uniform first moment of the actual rough-prime window product

Preparation of the all-cardinality independent deficit15.6:
the rough-prime WINDOW AVERAGE in its proof is now established
unconditionally, with an explicit constant and without treating
the number of exposed sources as fixed. Main15.6 moves from
not_started to in_progress. Its final deficit estimate is NOT
yet proved. Coverage remains84/167 proved and16 conditional,
with128 confirmed mathematical improvements. This checkpoint
adds arithmetic foundations and no new numbered completion.

FiniteEulerAverage proves the exact finite divisor expansion
of an arbitrary nonnegative local Euler product over a finite
set of distinct primes. For every natural X, the average over
1<=n<=X is at most
X*product_p(1+h(p)/p).
The exact expansion uses the actual count floor(X/d) of positive
multiples of the product d of the selected distinct primes.
Primality supplies the actual coprimality implication d|n iff
every selected prime divides n. In particular there is no
spurious +1 term for each modulus in this first-moment bound.

InverseSqrtTail proves the finite elementary bound
sum_{Y<n<=X} n^(-3/2) <= 2/sqrt(Y), for every Y>=1.
It telescopes reciprocal square roots and does not invoke an
analytic tail premise or any prime-distribution estimate.
RoughEulerMoments uses the cutoff Y=64*B^2 and the actual
factor p^(-1/2). For p>Y the moment increment
h_B(p)=(1+p^(-1/2))^B-1 is at most8*B*p^(-1/2).
The already proved elementary exponential remainder gives
this bound since B/sqrt(p)<1/8. The finite tail bound gives
sum_p h_B(p)/p<=2 for EVERY finite prime set above this cutoff.
Consequently the actual B-th moment of the local rough-prime
Euler product, summed over1<=n<=X, is at most X*exp(2),
uniformly in B and in the actual finite prime set.

FiniteProductPowerMean proves the pointwise AM-GM inequality
product_i f_i <= average_i f_i^B for B positive positions,
and the finite first-moment consequence after interchanging
the actual sums. This suffices in place of the printed Holder
step. WindowEulerAverage.first_moment applies it to every true
position x-1+i of an actual complete dyadic window. Each fixed
position maps the actual starts injectively into1..3N.
For N>=2 and1<=B<=N+1 it proves
sum_{N<=x<2N} product_{i<B} product_{p in P,p|(x-1+i)}
  (1+p^(-1/2)) <= 3*N*exp(2),
for EVERY finite prime set P above64*B^2. This product counts
a prime once for every position it divides and therefore also
majorizes the single-occurrence union-of-primes product in
the manuscript. The explicit bound is independent of B.

The constant enlargement from the printed cutoff B^2 to64*B^2
is internal to these new lemmas; no preserved manuscript is
changed. The old-source Euler factor, the actual relative
exceptional exposure count and its entire cardinality sum
remain to be connected before15.6 can be completed. No desired
deficit bound or growing-order arithmetic constant is assumed.
There is no new geometric or literature input, PaperC port,
dependency download, original-source edit or Palomar registration.

Verified under Lean v4.36.0-rc2: full build passed (13195 jobs); direct axiom audit passed for 9990 declarations using only propext, Classical.choice and Quot.sound; all 8249 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 13.65 GiB.


## Uniform actual independent-exposure rows

The ARITHMETIC exposure budget for article15.6 is now proved
unconditionally with a threshold before every number of preceding
windows. Its final independent deficit sum is still OPEN.
Main15.6 remains in_progress; coverage remains84/167 proved,
16 conditional and128 confirmed mathematical improvements.

LogBudgetEuler proves the finite prime Euler-product estimate
exp(c*sqrt(Y)/log(Y)+K/(sqrt(Y)*log(Y))) from the ACTUAL prime
logarithmic budget sum(log(p))<=K. Small primes are bounded by
the proved elementary weighted-prime estimate; above Y each
inverse square root is charged to log(p)/(sqrt(Y)*log(Y)).
No prime-pool cardinality estimate is substituted for its log
budget. EulerPrimeCovers proves the monotonicity and finite
union-cover bounds, allowing repeated prime occurrences and
arbitrary overlaps.

IndependentExposurePrimePool defines the literal old-source
pool together with ALL primes up to Y=64*(L+1)^2. Its Euler
factor baseEuler(S,L) is at most N^epsilon uniformly for every
actual dyadic source set S with card(S)<=s, where s is fixed
before N. The actual log budget is
Y*log(4)+B*log(4)+s*B*log(3N), B=L+1.
Since sqrt(Y)=8B, the exponent is at most
[8*(c+log(4))*B+log(4)/8+s*log(3N)/8]/log(Y).
Critical-window geometry puts B<=D*log(N), and a fixed minimum
length makes log(Y) arbitrarily large before any actual source
is supplied. Thus this factor is uniformly subpower. All primes
of the real source values are retained.

IndependentExposureEulerBudget defines the actual rough-prime
window product A_x, with primes bounded by3N and above Y.
It has A_x>=1 and the already proved first moment at most
3*N*exp(2). For any fixed old source set S and ANY new set A
of dyadic windows, with NO bound on card(A), it proves
Euler(primePool(rawValues(S union A)))
  <= baseEuler(S,L)*product_{x in A} A_x.
The literal prime-set cover follows from actual prime factors
of actual true window values. A prime at most Y goes into the
base pool; every larger prime from a new window occurs in its
actual positionwise rough-prime Euler product.

For arbitrary weights w_x<=M/N, M>=0, the same development
proves sum_x w_x*A_x<=3*M*exp(2). The exact exceptional row is
BranchingExceptional.badStarts for all raw old source values.
Its weighted mass is at most
rowConstant(S,N,L,M)*product_{x in A} A_x,
where rowConstant=(M/N)*(B/2)*sqrt(3N)*baseEuler(S,L).
This uses the exact supported-value Euler count, including
contacts and local defects, with no separate contact deletion
or worst-case arithmetic constant depending on card(A).

UniformIndependentExposureBudget.uniform_row_constant proves
rowConstant<=N^(-1/2+epsilon), uniformly in fixed-cardinality
sources. uniform_budget therefore supplies ONE threshold
before all N,L,S,weights and arbitrarily large preceding sets A,
simultaneously with the constant weighted mean of A_x. These
are actual arithmetic row estimates, not assumptions of the
desired final independent deficit.

The remaining work for15.6 is finite: relate failure of the
literal source-plus-target directness to an exceptional exposure
in every ordering, retain the exact factorial enumeration, and
sum the weighted exposure bounds over all cardinalities. This
checkpoint asserts none of these unfinished closure steps.
No new external input, dependency download, PaperC port,
manuscript-byte change or Palomar registration is added.

Verified under Lean v4.36.0-rc2: full build passed (13205 jobs); direct axiom audit passed for 10010 declarations using only propext, Classical.choice and Quot.sound; all 8276 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 13.63 GiB.


## P1-MATH-0129 — Unordered seeds close the full independent deficit

The all-cardinality independent deficit admits a fully finite
unordered proof. For each non-direct extension choose a minimal
relative target relation, remove one participating target x,
and use its nonzero component to place x in the actual exceptional
row for the remaining targets A and fixed sources. The resulting
seed insert(x,A) is contained in the extension. Sum all supersets
of each seed with the exact identity
product_D(w)*product_{G minus D}(1+w). The actual row estimate
badRow(A)<=D*product_A(a) then gives the entire mass at most
D*exp(sum w+sum w*a)<=D*exp(2K), provided a>=1 and sum w*a<=K.
This removes the ordered-exposure and factorial summation from
15.6. The full raw-value prime pool already includes contacts
and local defects, so no separate contact term is needed. The
same proof works for every subspace of the full raw source span,
which contains the effective source span. The W component of
a target-minimal relation may be zero; internal target dependence
must remain included in the literal non-direct population.


## Unconditional completion of the uniform independent deficit

Main Lemma15.6 is now proved UNCONDITIONALLY for the literal
independent deficit summed over ALL cardinalities. One threshold
is chosen before N,L,all actual dyadic source and target sets,
every source set of cardinality at most the fixed s, and every
subspace W of the FULL RAW source value span. The result is
therefore stronger than restricting W to the effective source
span. The ground set G may be any actual subset of the dyadic
block; targets are exactly G minus the sources.

IndependentExtensionDeficit.Direct means literal injectivity of
the addition map from W and the individual effective spaces S_x.
Its equivalence with zero relative nullity is proved. The finite
population is exactly every target subset for which this map
is not injective, with no restriction on cardinality. Its weight
is exactly u^card(U)*product_{x in U} infiniteMarginal(x,L),
proved equal to product_{x in U}(u*infiniteMarginal(x,L)). Zero
marginals are retained. These are independent product weights,
not conditional extension probabilities or positive joint weights.

IntersectionExceptional proves that a nonzero vector belonging
both to an actual effective window space and to the full old
raw-value span forces at least two supported physical positions.
The even coefficient vector is lifted from the actual effective
space; its nonempty binary support has even cardinality. Every
selected coordinate lies in the real old prime pool by the
already proved private-prime argument. Thus its center belongs
to the literal BranchingExceptional.badStarts set. The effective
source span is proved to lie in the raw source-value span. The
latter has an actual finite enumeration from the full coefficient
map, so arbitrary source subspaces can be used without assuming
local regularity or a dimension formula for W.

For each non-direct U, choose a minimal relative dependent J
inside U. A genuine relation is nonzero in every target of J;
its sum lies in W. Choose x in J and put A=J minus x. The x
component is nonzero and lies in the full raw span of sources
union A. Hence x is an actual exceptional start relative to A,
and insert(x,A) is a subset of U. This covers internal target
dependence as well as dependence meeting W. The W component
may vanish, and no nonzero-source-component condition is added.

AllCardinalitySeedBound proves the exact finite identity for
all supersets of a seed D inside G:
  sum_{D subset U subset G} product_U w
    = product_D w * product_{G minus D}(1+w).
ExceptionalSeedBound then bounds every covered family by
  exp(sum_G w) * sum_{A subset G} product_A w * badRow(A).
If badRow(A)<=D*product_A a, a_x>=1, and
sum_G w_x*a_x<=K, this is at most D*exp(2K).
This is a pure finite unordered argument; no enumeration by
orders, factorial normalization or growing-order constants
are used in this closure. Overcounting is justified solely by
nonnegative finite sums, including overlaps between witnesses.

UniformIndependentDeficit.finite_bound applies this identity
to the actual source-relative seeds. The published arithmetic
row budget supplies D=N^(-1/2+eta), a_x=windowEuler(N,L,x),
and K=3*M*exp(2), where M=u*2*2^C is a uniform actual marginal
cap. These inputs hold before arbitrarily large preceding sets A.
The already proved first moment bounds K independently of N,L.
With eta=epsilon/2, the fixed factor exp(2K) is absorbed using
a second epsilon/2. UniformIndependentDeficit.uniform_bound
therefore proves the full printed N^(-1/2+epsilon) estimate,
uniformly in sources and W, at every cardinality simultaneously.
Contacts and local defects remain in the exceptional row; no
extra contact deletion or correction term is necessary.

Main15.6 moves from in_progress to proved. Numbered unconditional
coverage rises from84 to85/167;16 conditional results remain
separate. P1-MATH-0129 records the unordered finite closure and
the stronger raw-source-space scope. This result does not prove
the compressed clause of15.8 or the pair-weighted total15.9.
No new geometric input, dependency download, PaperC port,
manuscript-byte change or Palomar registration is introduced.

Verified under Lean v4.36.0-rc2: full build passed (13215 jobs); direct axiom audit passed for 10026 declarations using only propext, Classical.choice and Quot.sound; all 8298 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 13.60 GiB.


## P1-MATH-0130 — Original participating unions replace pair compression in15.9

The good-pair large-seed part of15.9 can be proved entirely
with ORIGINAL windows, without the compressed clause of15.8.
A dependent pair is coordinatewise participating. A minimal
relative target seed over its effective span is participating
relative to that pair. Lifting each actual relative sum through
the source addition map shows that their union is coordinatewise
participating in the original spaces. Different coordinates
may have different witnessing relations; a single full-support
relation is unnecessary. The stronger original certificate tail
already proved for this larger population therefore applies.
For actual private good-channel pairs the activity divided by
product_e(u*p_x) is at most K*N^(1/3). Charge a distinguished
pair inside its union by at most2^card(I), absorbed by doubling
the fixed independent weight. Taking a=23/12 in the original
participating tail gives the stronger large-seed rate
N^(-19/12+epsilon), hence the required N^(-3/2+epsilon).
Free complements cost a constant by the actual marginal mean.
Minimal relative seeds include internal target dependence,
so a separate internal-directness test is also unnecessary.
The final15.9 remains conditional only on the same finite
geometric inputs already used for weak/exceptional activities
and fixed-size seeds; no compressed-tail premise is added.


## Conditional completion of the pair deficit at every cardinality

Article Proposition15.9 is now complete CONDITIONALLY under
exactly the existing chosen-source surface covers, ordinary
surface covers, and uniform normalized-curve point bounds.
AllPairExtensionDeficit.deficit is the literal D_2(u): sum over
ALL unordered actual dyadic pairs of the absolute actual centered
coefficient times the exact independent extension deficit over
EVERY cardinality, with the actual heterogeneous marginals.
AllPairDeficitUnderInputs.article_15_9 proves its eventual bound
N^(-3/2+epsilon). No desired pair or extension mass is assumed.
Main15.9 moves from not_started to conditional; unconditional
coverage remains85/167, conditional results rise from16 to17,
and confirmed mathematical improvements rise from129 to130.

RelativeParticipatingUnion proves a stronger algebraic bridge
than a simultaneous full-support relation. If every source
coordinate participates in some relation, and every target
coordinate participates relative to the effective source span,
then EVERY coordinate in the original source-target union
participates in some relation with zero total. For a target,
its actual relative sum is lifted through the actual addition
map onto the source span, and subtracted after extension by zero.
For a source, its source-only relation is extended by zero.
Every actual dependent pair is participating, since it is a
minimal non-direct two-element family. Source coordinates may
vanish in target witnesses. No claim of a single relation
nonzero at all source-target coordinates is made or needed.

DistinguishedSeedWeights proves the exact finite overcounting
bound for a distinguished disjoint source e and target seed A.
If c(e)<=R*product_e(w), then
  sum_e c(e)*sum_A product_A(w)
    <= R*sum_I product_I(2*w),
provided each union I=e union A belongs to the target family.
For each fixed e, A is determined by I because e and A are
disjoint. For fixed I, at most2^card(I) choices of e exist.
That factor is absorbed exactly by doubling the independent
weight, before any cardinality cutoff or N is chosen.
PairExtensionSeedTail applies the bridge to actual relative
participating seeds disjoint from each dependent pair.

GoodPairSeedTail.private_product proves the exact product
of actual marginal weights for a private channel pair:
product_e(u*p_x)=u^2*(2^(-L))^2.
The existing actual covariance estimate divided by this product
is at most2^((L+1)/3)/u^2, since every channel in the finite
good family has height b>=3. In the critical band this is at
most K*N^(1/3), K=2^((C+1)/3)/u^2. uniform_ratio has one threshold
before every actual good pair in the fixed finite channel set.
The doubled weights2*u*p_x have a fixed cap4*u*2^C/N.
The already proved original coordinatewise-participating tail,
with a=23/12<2, bounds all unions of large relative seeds by
N^(-23/12+eta). Multiplying by the ratio gives
K*N^(-19/12+eta), stronger than the required N^(-3/2+epsilon).
This entire good-pair large-seed estimate is UNCONDITIONAL.
It uses original windows and does not use a compressed-block
certificate theorem or assume a compressed-tail estimate.

AllPairExtensionDeficit proves the remaining exact finite cover.
Every failed extension contains a minimal nonempty relative seed.
Seeds of size below fixed s are covered by the actual fixed-order
extension populations of15.7; all larger ones belong to the
actual relative participating-seed tail. The exact finite
superset identity charges free complements by exp(sum_x u*p_x).
After weighting pairs, each fixed small seed order contributes
u^k*FixedPairExtensions.deficit(G,L,k). The cutoff s is chosen
before N, so only finitely many fixed-order bounds are used.
The class partition is an equality for the literal weighted
D_2, including all direct pairs with their zero coefficients.

UniformPairClassDeficit proves that ANY actual pair class has
mass at most its absolute activity times N^(-1/2+eta), using
unconditional15.6 with the actual full raw source span. The
proved finite-channel weak and exceptional activity bounds,
N^(-1+eta) and N^(-1+eta), therefore yield N^(-3/2+O(eta)).
The good-pair small seeds use the existing conditional15.7,
and their large seeds use the new unconditional estimate.
The true actual marginal mean bounds the free-complement
factor by exp(u*2*2^C). All finite factors are absorbed after
choosing eta=epsilon/16.

FinitePairDeficitInputs.Parameters and Hypotheses are only a
finite explicit bundle of the SAME geometric propositions.
They contain no host estimate, arithmetic mass bound or new
axiom. The final theorem chooses Q,s and finitely many actual
geometric dimensions before their supplied hypotheses, then
one threshold before all N and critical L. The chosen-source
size caps are sizeCap(epsilon/2048) for the pair partition and
sizeCap(epsilon/65536) for each of the finitely many fixed seed
orders. The three geometric translations themselves remain
unformalized, so this result is NOT counted as unconditional.

P1-MATH-0130 records that the stronger coordinatewise-tail
property removes the geometric-compression step from the proof
of15.9, and also removes the need to separate internal target
dependence in this argument. Main15.8's separate compressed
assertion remains OPEN; this checkpoint does not claim it.
No new dependency, PaperC port, original-source change or
Palomar registration is introduced.

Verified under Lean v4.36.0-rc2: full build passed (13231 jobs); direct axiom audit passed for 10049 declarations using only propext, Classical.choice and Quot.sound; all 8328 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 13.56 GiB.


## P1-MATH-0131 — Stronger unconditional independent retained deficits

Both counting deficits of T17.1 admit stronger unconditional
independent-weight estimates. Ordinary primitive seed coverage,
the exact finite superset identity, and the already proved
coordinatewise-participating independent mass give
F<=N^(-1+epsilon), removing the printed separate B/N term.
The second deficit is exactly4*sum_good_e q(e)*E_{S_e}(2).
The actual good-pair total joint mass is at mostN^(-2/3+eta),
uniformly for every real private-prime cutoff H: actual good
edges are a subset of the two private channel families at
cutoff0, whose homogeneous mass already has that upper scale.
Combine this with unconditional15.6, E_{S_e}(2)<=N^(-1/2+eta),
to obtain mathfrakG<=N^(-7/6+epsilon), stronger thanN^(-1+epsilon).
Thus neither positive primitive mass nor positive distinguished
compressed mass is needed to prove T17.1. These estimates concern
the literal independent counting weights; they do not prove the
separate positive-mass estimates with nullity amplification.


## Unconditional completion of companion T17.1

Companion Lemma T17.1 is now complete UNCONDITIONALLY, with
stronger independent deficit powers than the printed statement:
  F <= N^(-1+epsilon),
  mathfrakG <= N^(-7/6+epsilon).
These are the literal two retained-reference counting deficits,
including their original2^r cardinality weights, actual nominal
marginal on the regular ground, and actual good-pair joint
probabilities. RetainedIndependentDeficitRates.companion_T17_1
proves exactly the printed weaker rates
F<=N^(-4/5+epsilon)+(L+1)/N and mathfrakG<=N^(-1+epsilon).
The existing exact cardinality grouping identifies the complete
sums over0<=r<=n; coefficients above n are already zero.
The common threshold precedes every critical L and EVERY real
private-prime threshold H, including a scale-dependent H.

OrdinaryIndependentDeficit defines ALL non-direct subsets of
an actual original-window ground set with arbitrary independent
product weights. Each contains an ordinary primitive subset.
Every primitive subset has size at least two and is genuinely
coordinatewise participating; its simultaneous full-support
relation is also proved. The exact finite superset cover gives
mass<=exp(sum_G w)*primitiveSeedMass. The already proved
OriginalParticipatingMass.uniform_mass bounds every such seed
population by N^(-1+eta), for arbitrary heterogeneous w>=0
with w_x<=M/N. The total weight is at most M, since the dyadic
block has exactly N starts. After absorbing exp(M),
OrdinaryIndependentDeficitBound.uniform_bound proves the entire
non-direct independent mass<=N^(-1+epsilon), uniformly over
all actual dyadic ground sets and all weights with the fixed cap.
No positive joint mass or relative-nullity amplification is
substituted for these independent product weights.

RetainedIndependentDeficitComparison.first_eq identifies the
literal firstMass with that development at w_x=2*p_x on the
actual regular set. failed_eq identifies the actual failed
compressed extensions with literal non-directness of the source
span plus individual target spaces. second_eq proves the exact
identity
  secondMass(H,N,L)=4*sum_good_e q(e)*E_{S_e}(2),
with all cardinalities present. The factor4 is exactly the two
original endpoints' cardinality weight, not an asymptotic loss.
These identities use effective spaces and do not assume direct
factorization of any failed dependent extension.

Every prime is positive, so an actual PrivateAbove(H) condition
implies PrivateAbove(0), even for arbitrary real H. Actual good
edges lie in the two private channel families2:3 and3:4 at
cutoff0; the at-least-two-unit property follows from actual
nonzero intersection and private normalized values. Their true
joint mass is bounded by the actual homogeneous rank probability,
then by the previously proved raw principal homogeneous mass.
RetainedGoodPairMass proves beta(H,N,L)<=N^(-2/3+eta), uniformly
in ALL H, with no H-range assumption and no new geometry.
This is an upper bound; it asserts no uniform lower phase at
arbitrary H.

Uniform independent deficit15.6, with exactly two old sources
and u=2, gives E_{S_e}(2)<=N^(-1/2+eta) for every good pair,
including all its failed extensions and exact zero marginals.
The exact secondMass identity thus gives
4*beta*N^(-1/2+eta)<=N^(-7/6+epsilon).
The actual marginal cap supplies the firstMass specialization
with M=4*2^C. Both stronger estimates are unconditional.
Consequently T17.1 needs neither the positive primitive
mass theorem nor the distinguished compressed positive-mass
theorem used in its printed proof. No conclusion about those
separate positive-mass theorems is inferred.

T17.1 moves from not_started to proved; unconditional coverage
rises from85 to86/167;17 conditional results remain separate.
P1-MATH-0131 records the stronger powers and simpler independent
proof. All geometric translations remain explicit unproved
arguments in their separate conditional results. No new
external input, dependency download, PaperC port, manuscript
byte change or Palomar registration is introduced.

Verified under Lean v4.36.0-rc2: full build passed (13241 jobs); direct axiom audit passed for 10065 declarations using only propext, Classical.choice and Quot.sound; all 8347 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 13.54 GiB.


## Conditional completion of companion T17.4

Companion Lemma T17.4 is now complete CONDITIONALLY under
the same three already recorded finite geometric properties:
chosen-source and ordinary surface covers, and uniform actual
normalized-curve counts. Its entire finite analytic inequality
remains unconditional. The only use of geometry in this
completion is the arithmetic upper bound for the ACTUAL
regular-set covariance parameter at the literal a_N scale.
No desired conversion error or covariance bound is an input.

SecondFactorialCorrection.value is exactly
a_N=E(Z_N)_2-(N*2^(-L))^2, for the full actual dyadic count.
The second factorial moment is the actual Bochner expectation,
not an independent approximation. gap_identity proves
a_N-kappa_2=(E Z_N)^2-lambda_N^2, with the full diagonal
correction retained. The previously proved actual mean-bias
estimate and actual mean caps give, unconditionally,
|a_N-kappa_2|<=N^(-1+epsilon).

SecondFactorialCorrectionLower.uniform_lower proves the
unconditional lower bound a_N>=c_C*L*N^(-2/3), c_C>0.
The actual positive2:3 channel gives a lower bound for beta;
the already proved one-sided full-cumulant comparison gives
2*beta-kappa_2<=N^(-1+epsilon). Together with the actual
mean-square gap this yields the claimed lower bound after
absorbing two N^(-11/12) errors. Thus positivity of the
literal a_N does not rely on the conditional upper profile.
This extends the already recorded unconditional positivity
argument of finding87 to the literal nominal correction.

SharpCovarianceScaleUnderInputs.uniform_absolute_scale
uses the existing actual pair-activity profile with fixed
margin1/15 and the unconditional principal beta upper phase.
The profile remainder N^(-4/5+1/15)=N^(-11/15) is smaller than
L*N^(-2/3). It proves the sharp bound
absolutePairMass(G,L)<=K_C*L*N^(-2/3) for EVERY actual
dyadic subset G, with NO epsilon in this power. The actual
regular covariance sum C_2 is bounded by this absolute mass.
Using the unconditional lower bound for a_N gives
|C_2|<=R_C*a_N. Both the signed covariance definition and
all possibly incompatible pairs remain exact.

SecondFactorialCorrection.regular_mean proves that the
actual regular-set count mean is n*p, n=card(G_N), p=2^(-L).
regular_cumulant proves its actual second factorial cumulant
equals2*C_2-n*p^2. The existing CountVariance identity
identifies that parameter exactly with variance minus mean.
There is no omitted marginal diagonal or change of mean.

SharpRetainedConversionUnderInputs.companion_T17_4 inserts
these actual parameters into the previously proved full
signed-measure conversion. It gives the literal ordinary l1
sum of absolute singleton errors over ALL k>=0:
  ||B_beta-Q(mu,alpha_G)||_1
    <=4*|beta_N-C_2|+K_C*(N^(-2)+a_N/N).
Here B_beta is the actual finite binomial pair reference
embedded as a signed measure, beta_N is the actual joint
mass of retained good edges, C_2 is the actual regular
covariance sum, mu is the actual regular mean, and alpha_G
is its actual variance-minus-mean parameter. Every real
private-prime threshold H is allowed; the beta discrepancy
is kept explicit, so no approximation beta_N=C_2 is assumed.
The exact coefficient4 is retained.

The geometric dimensions are chosen before their explicit
Hypotheses bundle, with chosen-source sizeCap(1/100).
After those supplied properties there is a constant K_C
and one threshold before every N,L and H. Those three
geometric translations themselves remain unformalized;
T17.4 moves from in_progress to conditional, not proved.
Unconditional coverage remains86/167; conditional results
rise from17 to18;131 confirmed improvements remain unchanged.
No new literature input, dependency download, PaperC port,
manuscript-byte edit or Palomar registration is introduced.

Verified under Lean v4.36.0-rc2: full build passed (13249 jobs); direct axiom audit passed for 10073 declarations using only propext, Classical.choice and Quot.sound; all 8357 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 13.51 GiB.


## P1-MATH-0132 — Fixed and all-cardinality primitive power improves to one

The primitive exponent4/5 in T4.3 and T14.2 improves to1
under the existing dense two-target geometric inputs. For
triples with nullity at least L/4, sum the already proved
one-source extension bound over the N singleton sources:
each costs O(N^(-2+eta)), giving N^(-1+eta) in total.
For smaller nullity, the unconditional independent half-count
N^(-3/2+eta) is multiplied by at mostN^(1/4), giving the
stronger N^(-5/4+eta). Fixed orders at least four already have
the unconditional boundN^(1-r/2+eta)<=N^(-1+eta).
At all larger cardinalities a primitive has nullity at mostL;
multiply the uniform original participating independent tail,
with exponent arbitrarily close to2, by at most2^L=O(N).
The resulting primitive rank tail is N^(-1+epsilon).
Combine only finitely many small orders, then use the actual
joint and centered rank bounds on the regular ground.
The ordered fixed-size statement retains its exact factorial
fiber bound. The larger unordered rank-weight result allows
all dyadic primitive families, including overlap, local
irregularity and zero marginals. Geometry is needed only
for the dense three-window fixed-order branch.


## Conditional completion of fixed and all-cardinality primitive mass

Companion Proposition T4.3 and Theorem T14.2 are now complete
CONDITIONALLY under only the same chosen-source surface covers,
ordinary surface covers and uniform normalized-curve bounds
already required for15.2. Both printed exponents4/5 improve to1.
The entire literal fixed-order ordered nominal primitive sum
of T4.3 is bounded by N^(-1+epsilon), and the entire primitive
joint-plus-absolute-centered sum of T14.2, at ALL cardinalities
at least three, is bounded by N^(-1+epsilon).

DensePrimitiveTripleMassUnderInputs sums the ACTUAL one-source
two-target estimate proved in15.2. For every singleton source E,
the dense primitive extension rank mass is at most
(2*2^C/N)*N^(-1+eta), uniformly in E. The finite weighted source
cover uses all singleton subsets of the dyadic block; there
are exactly N. Every actual primitive triple has such a source,
and its remaining two centers are an actual pair in that cover.
The dense threshold is fixed at relative nullity L/4. Thus all
dense primitive triples together have mass N^(-1+epsilon).
No desired dense triple host count or target mass is assumed.

For the remaining primitive triples, relative nullity below
L/4 contributes at most2^((L+1)/4)<=K_C*N^(1/4).
The unconditional actual independent half-count contributes
N^(-3/2+eta), so their rank mass is N^(-5/4+eta), stronger than
the required power one. FixedPrimitiveMassUnderInputs combines
the two classes and proves rank mass<=N^(-1+epsilon) for EVERY
actual primitive triple population in the dyadic block. Local
irregularities, overlaps and zero marginals remain included.
For every fixed order r>=4, the earlier unconditional
N^(1-r/2+epsilon) primitive estimate already gives power at
least one. Consequently every fixed primitive order r>=3
has the stronger power one, with geometry needed only for
the three-window dense branch.

WeightedPrimitiveMass defines the exact u^card(I)-weighted rank
mass, and the actual joint-plus-absolute-centered mass. The
primitive relative nullity is at most L, so the rank mass is
at most2^L times the exact independent product with weights
u*p_x. Every primitive family is genuinely participating;
its full-support relation is proved. WeightedPrimitiveTail
uses the already uniform original participating tail with
a=2-epsilon/4 and its fixed size cutoff chosen before N.
Its independent mass is N^(-2+epsilon/2); multiplying by
2^L<=2^C*N and absorbing the fixed constant proves the
UNCONDITIONAL large-cardinality rank tail N^(-1+epsilon).
The relative-nullity amplification is included explicitly;
this is not merely an independent product estimate.

AllPrimitiveMassUnderInputs.uniform_rank combines that
uniform tail with only the finitely many fixed sizes below
its prechosen cutoff. The finite thresholds are maximized
after the actual finite geometric properties are supplied.
No fixed-order constant is evaluated at an order depending
on N. It proves the full rank-mass sum, including EVERY
cardinality and every actual dyadic primitive population,
is at mostN^(-1+epsilon). On the actual regular ground all
marginals are positive and nominal. The already proved
Fourier rank bounds give q(I)+|c(I)|<=2*rankWeight(I), for
compatible and incompatible systems alike. uniform_actual
therefore proves the stronger literal T14.2 bound; the named
companion_T14_2 also gives the exact printed power4/5.
No probability of an exceptional-window event is discarded.

FamilyEnumerationWeights bounds arbitrary nonnegative
family-dependent weights on any selected injective list
population by r! times its actual unordered family mass.
The finite fiber over each family has at most r! elements;
no constancy of nullity across different families is used.
PrimitiveOrderedMass defines exactly the actual distinct,
separated regular primitive lists of T4.3 and the literal
sum p^r*2^rho. Its membership theorem verifies all those
conditions. weight_formula identifies the nominal rank
weight with the actual heterogeneous primitive rank weight
ON THIS REGULAR population. rank_formula proves
rho=r*L-rank(sum of actual effective spaces).
The finite weighted enumeration inequality and fixed-order
factor absorption then prove the exact ordered T4.3
statement. No nominal-equals-actual-probability assertion
is made for incompatible systems or irregular windows.

The geometric Parameters and Hypotheses bundle contains
precisely the eight existing15.2 arguments, in the two target
orientations: chosen-source covers, ordinary covers and their
actual normalized curve bounds. Its cutoffs, degrees and
radical bounds are chosen by the existing dense two-target
theorem before the corresponding hypotheses. For the
all-cardinality result only a finite collection is used,
indexed below the already fixed tail cutoff. No new
geometric input, arithmetic mass assumption or axiom is
introduced. These properties themselves remain unformalized.

T4.3 moves from in_progress to conditional, T14.2 moves from
not_started to conditional. Unconditional numbered coverage
remains86/167; conditional results rise from18 to20. Finding
P1-MATH-0132 records the stronger primitive power one, the
short dense/low-nullity argument for triples, and the larger
unordered population without separation or local regularity.
No original manuscript byte, dependency, PaperC port or
Palomar registration is added. The sharper4/3 primitive tail
in main15.12 and the four-window branch of15.5 remain OPEN.

Verified under Lean v4.36.0-rc2: full build passed (13265 jobs); direct axiom audit passed for 10094 declarations using only propext, Classical.choice and Quot.sound; all 8385 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 13.47 GiB.


## All-order moderate certificates with a fixed number of anchors

The moderate arithmetic and all-order mass budget in main15.11
is now formalized for every fixed positive integer t. Main15.11
moves to in_progress: its saturated-family conclusion and the
general physical relation-to-saturation bridge remain OPEN.
Unconditional numbered coverage86/167, conditional coverage20,
and confirmed improvements132 are unchanged.

MultiAnchorValues uses ACTUAL t distinct offsets in one dyadic
window. The corresponding truncated odd kernels are pairwise
coprime because their prime factors exceed the window width.
Their product Q is squarefree, positive and at most(3N)^t.
For unmarked anchors it exceeds T^t. Every prime factor of Q
belongs to one actual selected value and is larger than Y.
MultiAnchorPrimeBudget proves the literal ceiling bound
m_t=ceil(t*log(3N)/log(Y)) on the number of these primes.

MultiAnchorModuli proves at most t receiving moduli exceed N
whenever their positive product is at most(3N)^t and N>3^t.
This threshold depends only on the FIXED anchor count, never on
the family order. The exact CRT product cost is at most
(6B)^t*2^(r-1)*N^(r-1)/Q. MultiAnchorAssignments obtains this
cost for actual center tuples from the existing prime-assignment
codes and literal congruence fibers; no count is assumed.
The number of assignments is at most(rB)^m_t.

MultiAnchorTupleCover counts the r*N*B^t choices of anchor
coordinate, dyadic center and ordered distinct offsets.
MultiAnchorCertificateCount.HasCertificate requires actual odd
prime membership in the receiving window for EVERY prime of Q.
The finite source tuple bound, uniform in every order r>=1, is
6^t*r*B^(2t)*2^(r-1)*N^r*(rB)^m_t/T^t.
Injectivity is retained and proves the source population is
empty when r>N. The empty-order population is also empty.

MultiAnchorWeightedSeries gives the actual convergent sum over
ALL orders with coefficient a^r/r!. Its finite majorant is
(6^t/2)*B^(m_t+2t)*(m_t+1)!/T^t
times exp(exp(1)*2aN). MultiAnchorOrder proves
m_t*loglog(N)/log(N) tends to t/A for Y=(log N)^A.
MultiAnchorFactorialBudget proves, uniformly for B<=D*log N,
B^(m_t+2t)*(m_t+1)!<=N^(2t/A+epsilon).
The all-order moderate mass is consequently
N^(-t*b+2t/A+epsilon) for T=N^b and any a>=0 with aN<=M.
MultiAnchorCertificateAsymptotic proves this before every
width B and weight a. Its critical-band specialization uses
the exact nominal marginal, with a fixed independent weight.

MultiAnchorFamilyMass recovers the actual factorial divisor by
counting EVERY injective enumeration of each certified family.
Certified means every enumeration has an actual moderate
certificate; it does not assume the desired mass estimate.
The finite layer and all-cardinality inequalities retain
arbitrary nonnegative heterogeneous weights p_x<=a.
MultiAnchorModerateMass.uniform_bound proves their literal
unordered independent product mass is at most
N^(-t*b+2t/A+epsilon), uniformly over every dyadic family
population, all critical-band lengths and all weights bounded
by M/N. No separation, regularity or positive-marginal premise
is used. Contacts and zero weights remain included.

This establishes the moderate certificate calculation with
all quantifiers and factorial costs. The next step must still
construct the t-anchor saturation graph, prove both directed
degrees, and connect actual block-dependent relation witnesses
to the certificate-or-edge alternative. No saturation-tail
bound or completed main15.11 result is claimed here.
No new geometric input, axiom, dependency download, Paper C
port, manuscript-byte change or Palomar registration is made.

Verified under Lean v4.36.0-rc2: full build passed (13289 jobs); direct axiom audit passed for 10143 declarations using only propext, Classical.choice and Quot.sound; all 8457 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 13.44 GiB.


## Unconditional completion of both multi-anchor certificate budgets

Main Lemma15.11 is now complete UNCONDITIONALLY, including
both literal all-order certificate budgets and their connection
to block-dependent physical relation witnesses. It moves from
in_progress to proved. Unconditional numbered coverage rises
from86/167 to87/167; conditional results20 and confirmed
improvements132 are unchanged. No geometric input is used.

MultiAnchorSaturation defines an ACTUAL directed edge x->y:
t distinct offsets in x have a kernel product divisible by D,
where D>6NB, and EVERY true prime factor of D divides a value
in y. Its divisor data prove squarefreeness, prime cardinality
at most m_t, product(D.primeFactors)=D, and large-prime support.
The receiving window's full prime pool has at most B*m_t
members, for every t>=1. There is no abstract edge-degree
hypothesis substituted for the required arithmetic.

MultiAnchorSaturationCounts proves both exact finite covers.
Outgoing centers cost at most B^t*(B+1)^m_t. Incoming centers
cost at most B^t*(t*exp(1)*B)^m_t: every divisor prime is assigned
to an actual selected source offset, while its membership in
the actual receiving prime pool is proved. The bounded-subset
weight inequality handles every prime cardinality, including
the range near the whole pool. MultiAnchorGraph proves its
maximum degree is at most
2*B^t*(2*t*exp(1)*B)^m_t.
MultiAnchorDegreeBudget and MultiAnchorSaturationDegrees prove
the eventual bound N^(t/A+epsilon), simultaneously for both
directed degrees and the actual undirected maximum degree.
One threshold precedes all critical lengths and vertices.

MultiAnchorRelationCertificate chooses t distinct nonzero
coordinates from an ACTUAL physical source word. Prime parity
shows every prime of their truncated kernel product occurs
with odd exponent at a value of some OTHER window. The finite
receiver and offset choices construct a literal assignment
code. If every receiving group modulus is moderate, the tuple
has HasCertificate. Otherwise its oversized group modulus is
a divisor witness for an actual t-anchor saturation edge.
This argument accepts arbitrary contacts and local defects.

MultiAnchorRelationFamilies.Witnesses is the source hypothesis
in literal physical even coordinates: for each UNMARKED block
there is a possibly different family of even coefficient words
whose total parity vector is zero and which selects at least
t values at that block. The witness may depend on the block.
No simultaneous full-support relation is assumed. The words
are reindexed through each actual injective enumeration.
Every noncertified family satisfying these witnesses is
proved admissible in the actual marked saturation graph.
The marks are precisely windows containing a value with
truncated odd kernel at most N^b above Y=(log N)^A.

UniformGraphExponentTail proves a general uniform generator
bound with SEPARATE mark and degree exponents d and q.
For any tilt gamma>0 with d+gamma<=1 and q+2gamma<1, all
admissible families of cardinality at least s have mass at
most N^(-gamma*s+epsilon), under weights<=M/N.
The threshold is chosen before s, every graph and every
family population. It follows from the already proved
positive marked component generator; no desired tail is an
input. The finite denominator and free mark contributions
are bounded explicitly.

MultiAnchorSaturatedMass sets delta=(1-b)*(1-sigma),
theta=t/A and eta=min(delta/4,(1-theta-delta)/2).
The actual marked count is N^(1-delta+eta), and the actual
degree is N^(theta+eta). When theta+delta<1, the general
generator admits the EXACT tilt delta/2, uniformly in s.
Consequently the literal unordered saturated mass is
N^(-s*delta/2+epsilon), with one threshold before ALL s.
Arbitrary nonnegative heterogeneous weights bounded by M/N
are retained. No epsilon times s is lost by moving the tilt.

MultiAnchorBudgets.article_15_11 partitions every actual
witness family into the moderate and noncertified saturated
populations and proves the two printed bounds simultaneously:
N^(-t*b+2*t/A+epsilon) and N^(-s*delta/2+epsilon).
uniform_split_bound also bounds the complete witness-family
mass by their sum. The independent weight per block, true
marginals p_x<=2*nominal_p, contacts, zero weights and irregular
windows are all covered by the more general cap M/N.
The moderate estimate itself was already proved without the
saturated parameter gap; the new theorem preserves that
earlier independent statement.

This completes15.11. It does not yet prove15.12: the ten-core
projection-to-heavy-even-word bridge, quantitative core
peeling, centered activity comparisons and literal primitive
tail remain to be connected. No new mathematical correction
is recorded merely for adding these proofs. No manuscript
byte, dependency, Paper C port or Palomar registration changes.

Verified under Lean v4.36.0-rc2: full build passed (13309 jobs); direct axiom audit passed for 10174 declarations using only propext, Classical.choice and Quot.sound; all 8503 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 13.40 GiB.


## P1-MATH-0133 — An unconditional primitive tail of power7/5

The primitive tail in main15.12 improves unconditionally
from N^(-4/3+epsilon) to N^(-7/5+epsilon), for every cardinality
at least256. The stronger statement bounds actual rank mass
and q(P)+|c(P)| on the whole dyadic block, including contacts,
irregular windows, incompatibility and zero marginals.
Split at the FIXED nullity9. Below9 the rank factor is at
most256; apply the two-anchor15.11 budget with
A=14,b=59/70,sigma=93/100, giving powers7/5 and176/125.
At nullity at least9, every primitive kernel coordinate
projection has that same dimension; the maximal-support
even-word argument provides ten selected values there.
Use t=10,A=12,b=31/60,sigma=23/25, whose independent
powers are7/2 and1856/375. The primitive rank factor
2^rho<=2^L=O(N) leaves power at least5/2.
Combine the two filtered populations and absorb fixed
constants. This removes the primitive compatibility
case split, the L/60 threshold and the growing-rank
comparison in the original proof. The connected clause
is a separate assertion and is not proved by this argument.


## Stronger unconditional primitive tail at all sizes above256

The primitive clause of main15.12 is now proved
UNCONDITIONALLY, with a stronger exponent7/5 instead of4/3.
It includes every cardinality at least256, and proves the
larger actual joint-plus-absolute-centered mass, as well as
the actual heterogeneous rank mass. Main15.12 moves from
not_started to in_progress because its separate CONNECTED
clause remains OPEN. Numbered coverage87/167 and20 conditional
results are unchanged. Confirmed improvement133 records the
stronger primitive tail and its shorter fixed-rank split.

MaximalSupportWord proves an elementary finite coding fact:
some binary codeword has weight at least the code dimension.
Choose a word of maximal support; restriction of the code to
that support is injective, since a nonzero kernel word has
disjoint support and increases the chosen support after
addition. The dimension is bounded by that restriction's
target dimension. For an even code and even t, dimension
at least t-1 therefore yields a word of weight at least t.
No pivot coordinates or simultaneous block support are
assumed or supplied as external data.

PrimitiveCoordinateProjection proves every coordinate
projection of a minimal effective relation kernel is
INJECTIVE. A kernel vector vanishing at that coordinate
restricts to the proper erased family; its nullity zero
forces the restriction to vanish, and extension by zero
recovers the whole vector. Hence every projection image has
dimension equal to the entire primitive nullity.
HeavyPhysicalRelations uses the previously proved
effective_projection_rank_le and the actual surjection
from physical even relations to effective relations.
The coding lemma then constructs an ACTUAL global physical
even relation with at least t selected values at any
prescribed block. PrimitiveAnchorWitnesses consequently
gives the literal15.11 witness predicate whenever
rho>=t-1. Different blocks may use different relations.
In particular every primitive has two-anchor witnesses,
and nullity at least9 gives ten-anchor witnesses.

PrimitiveIndependentBudgets supplies a uniform general
all-cardinality bound from the PROVED15.11 budgets,
using actual independent weights u*p_x and the
unconditional cap p_x<=2*2^C/N. Two explicit specializations
start at cardinality256:
  t=2,A=14,b=59/70,sigma=93/100:
    delta=11/1000, theta=1/7,
    moderate exponent=-7/5,
    saturated exponent=-176/125.
  t=10,A=12,b=31/60,sigma=23/25:
    delta=29/750, theta=5/6,
    moderate exponent=-7/2,
    saturated exponent=-1856/375.
The strict cutoff and graph gaps are verified by exact
rational arithmetic. Both estimates have one threshold
before all sizes, lengths and actual primitive populations.

Primitive256RankTail splits ONLY at the FIXED integer
nullity9. When rho<9, rank amplification is at most2^8=256,
so the two-anchor independent bound gives rank mass
N^(-7/5+epsilon). When rho>=9, the ten-anchor independent
bound applies, and the already proved primitive inequality
rho<=L costs at most2^L<=2^C*N. That branch has the stronger
rank mass N^(-5/2+epsilon). The exact finite filtered sum
then proves the FULL primitive rank mass at every
cardinality at least256 is N^(-7/5+epsilon).
No comparison rho versus a growing fraction of L, no
core deletion, compatibility split, or cardinality upper
cutoff is needed for this primitive argument.

PrimitiveActualMass extends the exact centered-to-rank
comparison to ALL actual marginal patterns. If some actual
marginal is zero, the existing finite probability transport
proves its whole centered coefficient is zero. Otherwise
the actual heterogeneous Fourier inequality applies.
Together with the already proved joint inequality this
gives q(I)+|c(I)|<=2*rankWeight(I), including contacts,
local irregularities, affine incompatibility and zero
marginals. The ground is the FULL dyadic block, with no
regularity filter or separation assumption.

Primitive256Tail.uniform_actual and uniform_centered prove
the stronger all-size exponent7/5. The named
article_15_12_primitive proves the literal printed4/3
bound for all primitive sets of cardinality>256 above
ANY actual ground subset of the dyadic block. It therefore
includes every source-family restriction in the paper.
The independent per-block weight remains fixed before N.
No geometric property, desired arithmetic mass, or new
axiom is an input. The connected part of15.12 is not
claimed, and the all-size T14.2 total still has its recorded
conditional small-size step. No original manuscript byte,
dependency download, Paper C port or Palomar action changes.

Verified under Lean v4.36.0-rc2: full build passed (13327 jobs); direct axiom audit passed for 10193 declarations using only propext, Classical.choice and Quot.sound; all 8524 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 13.36 GiB.


## Constructed relation cores and their actual mass

The actual core construction, exact centered peeling bound,
small-core probability ratio and large-core mass in main15.12
are now formalized UNCONDITIONALLY. These are preparatory
parts of its connected assertion. Main15.12 remains
in_progress: its separate primitive clause is already proved
with stronger power7/5, while the final connected summation
and the required fixed connected activity step remain OPEN.
Numbered coverage87/167, conditional results20 and confirmed
improvements133 are unchanged. No new finding is added for
proving the manuscript's existing core steps.

RelationProjectionRank.loss is the ACTUAL deletion nullity
rho(I)-rho(I erase x). kernel_finrank proves that the kernel
of coordinate projection has exactly the erased nullity:
the finite kernel cardinality is the already exact
missedRelations count, and binary cardinality identifies
its dimension. Rank-nullity then proves
dim(projection_x K(I))+rho(I erase x)=rho(I).
The loss equals the actual effective projection rank.
No ambient finite-dimensionality of the full prime vector
space is required, and no kernel dimension is assumed.

RelationCorePeeling constructs a terminal finite deletion
trace, deleting only blocks of relation projection rank
at most k. Its exact budget is
rho(A)<=rho(D)+k*(card(A)-card(D)).
At termination every remaining projection rank is greater
than k. This differs from the older private-rank peeling:
the new construction deletes SMALL RELATION projections,
which is the direction needed by15.12.
RelationCoreWitnesses.Core t L D uses these exact losses.
exists_ten_core constructs a true ten-core with k=8 and
the exact nullity budget. The previously proved heavy even
word theorem converts each effective projection into an
actual physical relation with ten selected values at that
block; different blocks may use different witnesses.

RelationCoreIndependentBudget.uniform_ten applies the
proved t-anchor budgets to every actual ten-core of
cardinality at least256, giving independent mass
N^(-7/2+epsilon), at ALL cardinalities. The exact parameters
are t=10,A=12,b=31/60,sigma=23/25.
LargeTenCoreMass.uniform_rank includes the ACTUAL nullity
amplification for cores with rho<=2L: it costs at most
2^(2L)=O_C(N^2). Their full rank-weight mass is therefore
N^(-3/2+epsilon). uniform_actual proves the larger actual
q(D)+|c(D)| mass has this same power, including incompatible
and zero-marginal systems. The proof does not assume
primitiveness, separated windows, local regularity or
positive compatibility. It directly supplies the large
ten-core branch needed in15.12.

RelationCoreCounting.full_support_lower proves
(1-card(D)/2^k)*2^rho(D)<=number of full-support relations
whenever each actual projection rank is at least k.
It uses the exact erased-kernel cardinalities and a finite
union bound. half_full_support gives
2^rho(D)<=2*number of full-support relations for every
ten-core of size at most256.
RelationCoreMomentRatio.centered_count transports the
actual compatible infinite-model centered coefficient
to this exact square-class relation count. Together with
the actual joint rank formula, ten_core_ratio proves
q(D)<=2*c(D) for every compatible actual ten-core with
at most256 blocks. There is no common nominal marginal
or hypothetical affine sign prescription.

RelationCoreActivityPeeling.compatible_majorant extends
the actual compatible-nullity centered majorant to every
marginal pattern, including zeros. peeling_bound proves
the literal pointwise activity inequality
|c(I)|<=2^card(I)*2^(k*(card(I)-card(D)))*
        product_{I minus D}(p_x)*q(D)
for any actual compatible maximizing source A and a
constructed k-peeling trace from A to D.
The larger I may be incompatible; every factor is an
ACTUAL marginal or joint probability. The proof uses the
actual maximizing-compatible-nullity equality, the exact
trace budget and the finite product decomposition.
No deletion-order enumeration occurs.
exists_ten_core_bound INTERNALLY chooses the maximizing
compatible A, constructs D, proves q(D)>0, and supplies
the ten-core property, exact rank budget and activity
inequality simultaneously. Neither this core nor its
probability estimate is an external premise.

The remaining connected proof must sum the freely
weighted complements, handle the growing-cardinality
rank retention, and bound the finitely many small cores
using the still-open fixed connected activity estimate.
These verified pieces alone do not establish that final
4/3 bound, T16.2 at all sizes, or the complete stopped law.
No geometric input, new axiom, dependency download,
Paper C port, manuscript byte or Palomar action changes.

Verified under Lean v4.36.0-rc2: full build passed (13343 jobs); direct axiom audit passed for 10213 declarations using only propext, Classical.choice and Quot.sound; all 8547 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 13.33 GiB.


## All-order large-core closure and low compatible nullity

Two complete branches of the CONNECTED argument in main15.12
are now proved UNCONDITIONALLY: arbitrary-cardinality closure
above a large chosen ten-core has mass N^(-3/2+epsilon), and
every connected family of size at least256 with compatible
nullity at most L/60 has mass N^(-83/60+epsilon).
Main15.12 remains in_progress because its small chosen-core
branch still needs the fixed connected activity and pair
deficit assembly. Its separate primitive clause is already
unconditionally proved with stronger power7/5.
Coverage87/167, conditional results20 and confirmed
improvements133 are unchanged.

SeedComplementMass proves the exact finite identity
sum_{D subset I subset G} product_{I minus D}(w_x)
  =product_{G minus D}(1+w_x).
No seed marginal is divided out, so zero weights are allowed.
Its general positive cover theorem allows an ARBITRARY
nonnegative activity c(D) on each seed. If each family
activity is bounded by one seed's activity times its true
independent complement product, the entire family sum is
bounded by exp(sum_G w_x)*sum_D c(D). The finite sum
interchange and actual cover are proved, with no factorial
or deletion-order factor and no family-size cutoff.

ChosenRelationCore.core uses the previously proved existence
theorem to choose an ACTUAL compatible ten-core for every
nonzero length and every original family, including an
incompatible original family. properties supplies its
containment, actual positive joint probability, projection
conditions, exact rank budget and actual activity inequality.
weighted_bound absorbs all fixed powers from peeling into
the single fixed weight512*u. The inequality is
u^card(I)*|c(I)| <= (512u)^card(D)*q(D)*
                   product_{I minus D}(512u*p_x).
All true marginal and joint factors are retained.

LargeCoreFamilyCover.cores is the literal finite population
of actual ten-cores inside G, of size at least256 and raw
nullity at most2L. If the chosen core D of I is large and
rho_*(I)<=2L, its positive probability and containment imply
rho(D)<=rho_*(I), so D really belongs to that population.
finite_bound uses the general complement cover, and
source_mass_le_actual compares its q-weighted seed sum to
the already proved actual core mass q+|c|.
LargeCoreClosureMass.uniform_bound therefore proves
sum_I u^card(I)*|c(I)|<=N^(-3/2+epsilon)
for EVERY actual family population with those chosen-core
properties, at ALL cardinalities. No connectedness or
growing-order cutoff is required for this larger population.
The exact marginal cap bounds the free-complement mean by
a constant before N; its exponential is absorbed only as
a fixed constant. This fully sums the large-core branch,
rather than assuming a propagation or complement estimate.

OriginalTwoAnchorWitnesses proves actual coordinatewise
participation implies projection rank at least one at
EVERY block. The supplied effective relation gives a
nonzero vector in the actual projection image; the exact
projection-rank identity and the physical heavy-word
theorem give the literal two-anchor witness.
Every connected original family of size at least two is
proved to have that property via an actual coordinate
relation. No single relation nonzero at all blocks is
assumed. No coefficient-nonzero or positive-marginal
premise is needed for this connected participation fact.

ConnectedIndependent256Budget.uniform_bound applies the
retuned t=2,A=14,b=59/70,sigma=93/100 certificate budgets.
It proves the ACTUAL independent product mass of every
connected dyadic population of sizes at least256 is
N^(-7/5+epsilon), uniformly at all cardinalities.
LowCompatibleNullityTail.uniform_bound combines that with
the actual compatible-nullity centered majorant, using
weights2*u*p_x. The full maximum rho_* is kept, even for
incompatible I and zero marginal patterns. Under
rho_*(I)<=L/60, the binary rank amplification costs at most
N^(1/60+epsilon). The resulting power is83/60, stronger
than the27/20 low-rank branch in the source proof and
stronger than the required final4/3. This refinement uses
the same two-anchor parameter retuning already recorded
in finding133; no new overall connected theorem is claimed.

The remaining case has a small chosen compatible ten-core.
Its nonempty-rank retention on the growing range,
connectedness forcing a non-direct complement, finite
small-core activity and pair-deficit summation still have
to be assembled. None of those desired arithmetic bounds
is substituted as an external hypothesis here.
No geometric input, axiom, dependency download, Paper C
port, original manuscript byte or Palomar action changes.

Verified under Lean v4.36.0-rc2: full build passed (13357 jobs); direct axiom audit passed for 10227 declarations using only propext, Classical.choice and Quot.sound; all 8563 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 13.30 GiB.


## Exact small-core deficits and the complete pair branch

The exact small chosen-core reduction of main15.12 and its entire
size-two branch are now formalized. The remaining unresolved arithmetic
quantity is the activity of actual small cores of sizes3 through255.
Main15.12 remains in_progress; its primitive clause and two previously
completed connected branches retain their published proofs. Coverage
remains87/167 unconditional,20 conditional,133 confirmed improvements.

SmallCoreRankRetention proves rho(D)>L/120 directly from the exact
chosen-core budget when rho_*(I)>L/60 and |I|<=L/960. Consequently
|D|>=2. If |I|>256 and |D|<256, then D is a proper subset of I;
the actual positive-joint core ratio gives q(D)<=2c(D).
SublogCardinalityCap.uniform_cap derives |I|<=L/960 uniformly from
K_N/log N tending to zero. Its threshold precedes every critical
length. The lower critical-scale estimate retains its true L+1
term, rather than replacing it silently by L.

ConnectedComplementDeficit proves that for ANY nonempty proper
D in a connected I the actual complement I minus D is non-direct
over the true effective span S_D. If it were direct, compressed
nullity equality and restriction would give an additive nullity
split, contradicting actual connectedness. No full-support witness
simultaneously nonzero in every block is postulated.
RestrictedSeedComplements proves a positive finite cover with the
EXACT allowed complement family at each source D. For fixed D,
I maps injectively to I minus D when D is contained in I; the true
allowed complement sum is retained, without a free-complement
exponential, factorial or deletion-order factor.

SmallCoreFamilyCover defines actual positive-joint ten-cores of
sizes2..255 inside G and their joint-weighted non-direct independent
complement sourceMass. The chosen-core activity inequality and the
proved complement cover bound every actual small-core connected
population by sourceMass at the single inflated weight512*u.
The actual small-core ratio converts q(D) into2*|c(D)|, preserving
ALL heterogeneous marginals, including zero-marginal cases.
SmallCoreDeficitReduction.uniform_source then applies the ALREADY
PROVED uniform independent deficit15.6 with source-size cap255.
It proves sourceMass<=2*N^(-1/2+epsilon)*sum_D v^|D|*|c(D)|.
The growing_range_reduction constructs all necessary core size
premises internally, with one threshold before all N,L,G,F.
This is an exact reduction, NOT the final connected4/3 estimate:
its remaining small-core activity has not been assumed bounded.

IndependentDeficitMonotonicity and AllPairDeficitMonotonicity prove
nonnegativity and ground-set monotonicity for the actual independent
and full weighted pair deficits. SmallCorePairDeficit splits the
finite source sum exactly into sizes2 and3..255. Its size-two part
is at most2*v^2*D_2(G,v), with the TRUE full pair deficit D_2.
Its pair_family_bound applies this to every actual connected family
whose chosen core has size2, without any upper cardinality cutoff
or compatible-rank cap. No uniform N^(-1/2) estimate is substituted
for that stronger weighted pair sum.

SmallCorePairMassUnderInputs proves both the source and complete
family size-two contributions are at most N^(-3/2+epsilon).
The proof uses the completed conditional article15.9 theorem;
its finite geometric bundle and all caps remain explicit ordinary
arguments. The common threshold precedes every dyadic subground,
length and actual family population. Thus the pair-core branch is
complete CONDITIONALLY on the SAME existing three geometric
properties; no new desired arithmetic estimate is an input.
The size3..255 activity and final connected-branch assembly remain
open. No new literature property, axiom, dependency download,
Paper C port, original manuscript-byte edit or Palomar action occurs.

Verified under Lean v4.36.0-rc2: full build passed (13377 jobs); direct axiom audit passed for 10250 declarations using only propext, Classical.choice and Quot.sound; all 8588 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 13.26 GiB.


## P1-MATH-0134 — Coefficient-one positive triple seeds and a two-sided error

The positive connected triple seed step of main15.10 can use
coefficient1 instead of2 in front of A3. The actual exact centering
identity applies to EVERY triple, so its primitive case need not
be split off. Connectedness makes each nonzero erased-pair term
an actual dependent-target event; exact pair/triple incidence
bounds their total by D1 with no multiplicity factor. Thus
T3_joint<=A3+D1+M3_independent. The same identity bounds the
signed joint/activity error and incompatible connected activity
by D1+M3_independent, giving the stronger finite statement
|T3_joint-A3|<=3*(D1+M3_independent).
The already proved sharp D1 estimate and connected independent
half-count give |T3_joint-A3|<=N^(-3/2+epsilon) under the SAME
explicit finite geometric properties as article11.1. This holds
on every actual dyadic subground, including zero marginals and
incompatible triples. It replaces only the positive-triple seed
step; it does not prove an absolute N^(-1) bound on A3 or the
remaining higher-order connected activity reduction.


## Positive connected triple seeds with coefficient one

The positive-triple seed step inside main15.10 is now proved with
a stronger coefficient1, replacing the coefficient2 in the source
proof. In fact its stronger TWO-SIDED comparison is proved:
|T3_joint(G)-A3(G)|<=N^(-3/2+epsilon), conditional only on the
same existing finite geometric properties as article11.1.
This does NOT bound A3 itself. Main15.10 moves from not_started
to in_progress; the remaining connected-family seed alternatives,
positive propagation and the printed4/3 remainder remain open.
Coverage87/167 unconditional and20 conditional is unchanged.
Confirmed improvement134 records the stronger finite and asymptotic
comparison for future manuscript integration.

ConnectedTargetDependence proves every member of ANY connected
family with at least two members has a nonzero intersection with
the true effective span of its complement. The existing canonical
coordinate relation supplies a nonzero vector at that member;
RelationCoordinateSpan places it in the complement span. The
other relation coordinates may vanish, so no simultaneous
full-support relation or positive coefficient is assumed.

TripleJointReconstruction proves the literal heterogeneous identity
q(T)=c(T)+sum_(z in T)c(T minus z)*p_z+product_(z in T)p_z
for every actual triple. Its error_bound keeps the exact signed
pair terms before taking absolute values. No primitive/nonprimitive
split, compatibility assumption, regular-site restriction or
positive-marginal premise is required for this identity.

ConnectedTriplePositiveReduction.pair_cost sums these actual
pair terms over ALL connected triples. A nonzero pair coefficient
forces positive pair nullity, even with zero marginals, by the
proved zero-nullity centered cancellation. Connectedness gives
the actual dependent-target condition. The exact distinguished-
member/pair incidence injects this restricted sum into the literal
IndependentTargetDeficit, with no multiplicity constant.
Consequently T3_joint<=A3+D1+M3_independent, with coefficient1.
The same proof gives |T3_joint-C3_signed|<=D1+M3_independent.
Its incompatible_bound controls the incompatible connected triple
activity by this SAME remainder, without any positive-ground
hypothesis. Compatible coefficient nonnegativity then gives
|T3_joint-A3|<=3*(D1+M3_independent).

ConnectedTriplePositiveUnderInputs.uniform_reduction uses the
already proved sharp actual D1 bound15.1/11.1 and the unconditional
connected independent half-count at order3. It obtains
T3_joint<=A3+N^(-3/2+epsilon). Its uniform_absolute_error proves
the stronger absolute-difference statement. The finite chosen-source
surface, ordinary-surface and normalized-curve inputs remain explicit
ordinary arguments at source capepsilon/1024. One threshold precedes
ALL lengths and actual dyadic subgrounds. Zero actual marginals,
contacts and affine incompatibility are retained. The true moving
A3 remains on the right and is not supplied as a bounded premise.
No new external property, axiom, dependency download, Paper C port,
original manuscript-byte edit or Palomar registration is introduced.

Verified under Lean v4.36.0-rc2: full build passed (13385 jobs); direct axiom audit passed for 10261 declarations using only propext, Classical.choice and Quot.sound; all 8599 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 13.23 GiB.


## The complete direct minimal-crossing seed alternative

The complete DIRECT minimal-crossing seed alternative in the proof
of main15.10 is now proved CONDITIONALLY on the same existing three
finite geometric properties. At every fixed target size r>=2,
the actual sum over ALL dependent pairs e and all direct minimal
crossings A of size r is at most N^(-5/3+epsilon).
No desired crossing mass or source host count is an input.
Main15.10 remains in_progress: the remaining internally dependent
crossings (especially the two-pair case), propagation and the
printed full4/3 remainder are not claimed. Coverage87/167,
20 conditional results and134 confirmed improvements are unchanged.

MinimalSpanCrossing constructs an actual inclusion-minimal A
whose effective span meets the old space W. Every proper B has
span DISJOINT from W; B is allowed to have its OWN internal
relations. This differs from minimal relative nullity, which
would also exclude internal relations. Choosing a nonzero
intersection vector and an actual preimage under relation
addition proves a relation nonzero at every target, with a
NONZERO sum in W. The source component is retained explicitly.
MinimalCrossingWindows turns this actual relation into the
already defined coordinatewise relative-window witnesses.
ConnectedSpanCrossing proves every nonempty proper part of an
actual connected family has such a minimal span crossing,
using the exact canonical direct-partition contradiction.

RelativeIntersectionNullity proves the exact generic identity
rho_W(A)=rho(A)+dim(W intersect span(A)). TwoTargetCrossingCut
then proves the precise two-target data for a DIRECT minimal
crossing. After removing two distinct targets y,z, put B for
the other targets and Q=W+span(B). Minimality and directness
prove Q is disjoint from S_y and S_z, and S_y is disjoint
from S_z. The relative nullity is EXACTLY
  dim(Q)+dim(S_y)+dim(S_z)-dim(Q+S_y+S_z).
The old source W may be internally dependent when represented
by its original windows; B may be empty. No primitive property
of the entire original source-plus-target family is assumed.

ExtensionJointFactor proves q(E union A)=q(E)*product_A(p_x)*
2^rho_(S_E)(A) whenever the whole system has positive joint
probability. It proves the corresponding upper bound for EVERY
actual system, including incompatible ones and q(E)=0, without
any division by q(E). DirectCrossingTargets identifies the
printed two-target deficit with the existing actual effective
Kernel dimension and obtains the exact heterogeneous joint
majorant q(e)*product_B(p_x)*p_y*p_z*2^dim(Kernel).

DirectCrossingExtensionsUnderInputs applies the ALREADY PROVED
full dense two-target mass to that actual population. For every
fixed source number it bounds the sum over actual target pairs
by q(e)*product_B(p_x)*N^(-1+epsilon). Pair directness proves
the required nonaligned-or-small-intersection alternative
internally. All eight finite cover/curve arguments are packaged
in the existing Parameters/Hypotheses structure; these are the
same three recorded geometric properties, not a new estimate.
The common threshold precedes every e,B and actual target set.
DenseDirectCrossingFamiliesUnderInputs chooses the two targets
by a proved unordered weighted cover, then sums EVERY choice
of the other sources B. Their true product mass is bounded by
exp(actual_mean), hence a fixed constant; no factorial or host
count is presumed. It proves the ENTIRE dense direct-crossing
family mass above e is at most q(e)*N^(-1+epsilon).

LowCrossingJointMass gives an unconditional complementary
estimate. For every fixed r,s and a>=0, all actual minimal
crossings with relative nullity<=a*L have total joint mass
at most q(e)*N^(-r/2+a+epsilon), uniformly in every source e
of size s and every actual dyadic target subground. This
estimate even allows internal target relations under its
relative rank cap. The actual relative half-count and a
proved critical binary-power bound supply every factor.
DirectCrossingFamiliesUnderInputs splits the direct population
at a=epsilon/4, chosen BEFORE N. Combining low and dense
parts proves the FULL fixed-size direct-crossing mass above
e is at most q(e)*N^(-1+epsilon).

DependentPairJointActivity proves q(e)<=2*|c(e)| on every
actual dependent pair: if q(e)>0 its exact binary rank factor
is at least2 and c(e)=q(e)-product(p_x); if q(e)=0 the
inequality follows directly. The sharp actual pair-activity
bound then proves the full dependent-pair joint sum is
N^(-2/3+epsilon), retaining irregular and zero-probability
pairs. DirectCrossingPairSeedsUnderInputs finally SUMS the
proved source-relative cost over the actual dependent pairs.
The resulting double sum of TRUE joint probabilities is
N^(-5/3+epsilon), at ANY fixed target size at least2 and on
EVERY dyadic subground. The threshold precedes all actual
pair-indexed target populations. Fixed sizes are not replaced
by a growing-order assertion. No external property, axiom,
dependency download, Paper C port, original manuscript-byte
edit or Palomar action is added.

Verified under Lean v4.36.0-rc2: full build passed (13413 jobs); direct axiom audit passed for 10287 declarations using only propext, Classical.choice and Quot.sound; all 8625 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 13.17 GiB.


## Low-intersection two-pair seeds and fixed compatible propagation

The LOW span-intersection two-pair alternative of main15.10,
including propagation to every fixed larger compatible family,
is now proved CONDITIONALLY on the same existing finite geometry.
Main15.10 remains in_progress: dense intersections and its other
remaining primitive/higher-order alternatives are not asserted.
Coverage87/167,20 conditional results and134 confirmed mathematical
improvements remain unchanged.

BlockJointIntersection proves the exact actual two-block identity
q(E union A)=q(E)*q(A)*2^dim(S_E intersect S_A)
whenever the whole system has positive joint probability. For
EVERY actual disjoint E,A it proves the corresponding upper
bound, including incompatible systems and zero source masses.
The proof keeps both exact heterogeneous joint factors and uses
the newly proved relative/internal/intersection nullity identity.
Its finite_bound allows TWO DIFFERENT actual source populations
P,Q and any restricted H subset of P times Q. Under a genuine
pointwise intersection-factor cap K>=0, the actual union joint
sum is at most K*(sum_P q)*(sum_Q q). Positive enlargement and
the finite product-sum identity are proved internally.

LowTwoPairJointMassUnderInputs.uniform_bound applies this to
actual disjoint dependent pairs on every dyadic subground.
If their effective span intersection has dimension at most a*L,
with a>=0 fixed before N, the full actual pair-of-pairs joint
sum is at most N^(-4/3+a+epsilon). Every cardinality, pair-
nullity, disjointness and rank condition refers to the actual
finite population. The completed dependent-pair joint mass
N^(-2/3+epsilon) is used TWICE; the critical binary-power
estimate supplies the intersection factor. There is no input
assuming a pair-of-pairs mass or independent source weights.
The finite geometric cap isepsilon/4096.

LowTwoPairSeeds.sourcePairs defines the literal restricted
pair-of-pairs population. families is its actual union image;
family_data proves every member lies in G and has exactly4
windows. The positive image bound retains all duplicate source
representations safely. LowTwoPairSeedsUnderInputs.uniform_seeds
therefore proves the actual unordered4-window seed joint mass
at the same4/3-a scale, without a canonical pairing assumption.

The existing PROVED unordered positive propagation theorem
then sums every fixed larger family containing one of those
actual seeds. Its true fixed factorial and subpower costs are
absorbed after one common threshold; no propagation estimate
is postulated. uniform_extensions proves actual joint mass
N^(-4/3+a+epsilon) at every fixed order4+k. Compatible
centered coefficients are bounded by their true joint mass
times2^(4+k), yielding uniform_centered_extensions at the SAME
rate. Its compatibility premise is explicit; incompatible
centered families are not dropped from a purported full bound.
Finally uniform_small_intersection_extensions chooses
a=epsilon/2 before N and divides the error margin in half,
obtaining the literal required N^(-4/3+epsilon) compatible
centered bound for this branch. Its finite source cap is
epsilon/65536. The threshold precedes every critical length,
dyadic subground and actual extension population.

This also covers zero span intersection, used when a proper
dependent target pair is direct from the old pair. The dense
strong-alignment pair alternatives remain open. The distinct
fixed/growing-order regimes, actual zero marginals and zero
joint masses are retained. No external property, axiom,
dependency download, Paper C port, original manuscript-byte
edit or Palomar action is added.

Verified under Lean v4.36.0-rc2: full build passed (13421 jobs); direct axiom audit passed for 10298 declarations using only propext, Classical.choice and Quot.sound; all 8638 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 13.15 GiB.


## Dense admissible two-pair seeds and compatible propagation

The DENSE nonaligned-or-weakly-aligned two-pair crossing alternative
of main15.10 is now proved at the true5/3 scale, including every
fixed larger compatible extension. The two new targets are ALLOWED
to depend on each other. This is distinct from the previously
completed direct-target alternative. Main15.10 remains in_progress:
strongly aligned dense crossings and the other remaining primitive
alternatives are not claimed. Coverage87/167,20 conditional results
and134 confirmed improvements remain unchanged.

TwoTargetJointWeight.pair_kernel proves that relative nullity above
ANY actual old-source span, on a pair of distinct targets, equals
the actual three-space Kernel dimension. No target pair directness
is used. intersection_le_kernel bounds the actual source/pair span
intersection by that dimension, retaining internal target nullity.
joint_bound therefore bounds the TRUE joint probability by
q(e)*p_y*p_z*2^dim(Kernel), with both exact heterogeneous target
marginals and the actual source q(e), including zero joint masses.
one_target_bound separately proves q(e union {y,z})<=q(e)*p_y
whenever S_y is direct from S_e. It follows by actual monotonicity
and the zero-intersection block joint bound; no regularity or
nominal marginal replacement is required.

TwoTargetJointMassUnderInputs.uniform_joint applies the completed
dense two-target weighted estimate to actual minimal pair crossings.
Minimality internally proves each target is direct from the old
source. A dense intersection of S_e with S_y+S_z supplies the
required Kernel rank. The admissible alternative is the literal
nonalignment OR small effective S_y/S_z intersection. The threshold
for that intersection is chosen before all N, sources and target
populations. The result is the whole joint target cost
q(e)*N^(-1+epsilon). All existing finite source-surface, ordinary-
surface and curve properties remain ordinary explicit arguments;
no target mass is an input.

DenseAdmissiblePairSeedsUnderInputs sums this proved source-relative
cost over ALL actual dependent old pairs. The already proved full
pair joint mass N^(-2/3+epsilon) gives the TRUE double joint seed
sum N^(-5/3+epsilon), even with internally dependent new targets.
Its two finite geometric parameter bundles are chosen before N;
the pair-bundle source cap isepsilon/2048.

DenseAdmissiblePairSeeds defines the literal dyadic target populations
and their four-window union family. Membership exposes every actual
disjointness, alignment, minimality and intersection condition.
family_data proves size4 and containment in G. A positive union/image
cover retains every source or target representation without an
assumed canonical pairing. DenseAdmissibleSeedFamiliesUnderInputs
proves the actual unordered seed joint bound and propagates it,
using the ALREADY PROVED unordered positive propagation, to every
fixed compatible order4+k. Both its true factorial and2^(4+k)
centered-conversion factors are absorbed as fixed constants. The
complete compatible centered extension sum has rate5/3; its finite
pair-bundle cap isepsilon/8192. All actual marginals, affine
incompatibility and fixed-order quantifiers remain explicit.
No new literature property, axiom, dependency download, Paper C
port, original manuscript-byte edit or Palomar action is added.

Verified under Lean v4.36.0-rc2: full build passed (13431 jobs); direct axiom audit passed for 10309 declarations using only propext, Classical.choice and Quot.sound; all 8651 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 13.12 GiB.


## P1-MATH-0135 — All dense pair crossings at power5/3 without exceptional exchange

The dense two-dependent-pair alternative in the proof of15.10
can dispense with the exceptional-pair exchange and the special
both-exceptional host count. Its ENTIRE actual joint seed mass,
including those exceptional configurations, has the stronger
N^(-5/3+epsilon) bound instead of the3/2 bound used for its final
exceptional subcase.
The proved bounded-width dense target count15.3 applies to the
normalized union even when that union has LOCAL relations: its
effective space is exactly S_y+S_z whenever an exact unit exists.
For each offset pattern the actual compressed anchor is injective,
so the dense PAIRS themselves, not only their centers, have a
subpower count after summing the logarithmically many patterns.
The uniform enlarged aligned rank theorem forces every strongly
aligned effective pair into a fixed finite channel set with at
least one exact unit; it excludes both growing height and zero
units at a prescribed positive rank margin. Consequently ALL
strongly aligned dense target pairs have count N^epsilon,
WITHOUT any private or good-edge assumption.
Minimality of the crossing gives S_e disjoint from each target.
Actual monotonicity then yields q(e union {y,z})<=q(e)*p_y.
The exact heterogeneous marginal cap proves the complete strongly
aligned source-relative cost q(e)*N^(-1+epsilon), unconditionally.
Combine this with the already proved conditional nonaligned/weak
target estimate, and sum the actual source pairs with their
N^(-2/3+epsilon) joint mass. This proves the full dense two-pair
seed rate5/3 under only the SAME three explicit finite geometric
properties. The same rate holds for compatible fixed-size
extensions. This strengthens one branch, not the full15.10 result.


## Complete dense pair crossings including exceptional alignments

The ENTIRE DENSE minimal two-target/pair crossing alternative of
main15.10 is now proved, with the stronger uniform actual seed
rate5/3, including EVERY strongly aligned exceptional normalization.
The source's exchange of exceptional pairs and its final3/2
exceptional-host estimate are unnecessary for this branch.
Improvement135 records this simplification and stronger branch rate.
Main15.10 remains in_progress: its other primitive alternatives,
complete connected-family cover and incompatible part are still
open. Coverage87/167 unconditional and20 conditional is unchanged.
Confirmed mathematical improvements increase from134 to135.

DenseCompressedPairs defines actual dense exact-unit target pairs
and their actual fixed-offset fibers. At each offset pattern the
compressed anchor is INJECTIVE on the original source pairs.
The exact effective block identity identifies the normalized union
space with S_y+S_z, even when it has local relations. Hence the
fiber injects into the ALREADY PROVED dense compressed-center
population. Summing all (L+1)^2 patterns gives a literal finite
pair count bound. No private prime, injective normalization map,
regularity, compatibility or exceptional-pair enumeration is used.
DenseCompressedPairCount consequently proves that ALL dense
actual pairs in ANY fixed channel have cardinality at most N^epsilon,
uniformly over the prescribed old sources and their subspace W.
This counting theorem is UNCONDITIONAL, using the proved15.3 input.

StrongAlignedUnitChannels chooses a finite height cutoff Q after
θ>0 and BEFORE even C or N. The genuinely uniform enlarged aligned
rank theorem implies that every aligned pair with actual effective
intersection rank>θ*L has height at most Q and at least one EXACT
normalized unit. A height larger than Q contradicts the uniform
L/max(a,b) rank cap; zero units contradict the separate full-loss
cap. Both coefficient orientations, height1/2 boundary channels,
irregular windows and nonprivate normalized unions are included.
StrongAlignedDensePairCount covers the whole strongly aligned
population by the fixed finite channel union and its swapped
images. One common threshold for that finite union precedes ALL
actual sources, W and target populations. It proves the full count
is N^epsilon, with no private/good-pair restriction and no geometric
literature input.

StrongAlignedDenseJointMass then uses the exact heterogeneous
one-target bound q(e union {y,z})<=q(e)*p_y, which follows from
minimal crossing and actual source/target directness. The actual
marginal cap p_y<=M(C)/N and the new subpower pair count prove the
ENTIRE strongly aligned dense joint cost is q(e)*N^(-1+epsilon).
This source-relative branch is UNCONDITIONAL, even for internally
dependent old sources and internally dependent new target pairs.
It avoids the need for source/target rank upper bounds involving
nominal regular marginals or for classifying both pairs as exceptional.

DenseTwoTargetJointMassUnderInputs partitions the full dense
minimal pair population into the earlier nonaligned-or-weak
class and its strongly aligned complement. The latter now has
its proved unconditional bound. Thus EVERY dense minimal pair
crossing above any fixed number of actual old windows has joint
mass at most q(e)*N^(-1+epsilon), without any alignment exception.
Only the SAME existing finite source-surface, ordinary-surface
and normalized-curve properties remain explicit theorem arguments
for the first class. No desired mass or pair-count hypothesis is
supplied as an input.

DensePairCrossingSeedsUnderInputs sums that actual source-relative
cost over ALL actual dependent old pairs. The proved sharp pair
joint mass gives the complete dense double joint seed sum
N^(-5/3+epsilon), including the previously exceptional aligned
configurations. DensePairCrossingSeeds defines the full literal
four-window union population, with NO alignment, private, good-edge
or regularity filter. Membership and size4 are proved and duplicate
representations are handled by a positive union/image cover.
DensePairCrossingFamiliesUnderInputs proves the actual unordered
seed joint bound, then propagates it to every fixed larger
compatible order4+k using the already proved positive propagation
and centered-to-joint comparison. The full actual compatible
centered extension rate remains5/3. Fixed factorials and powers
are absorbed after the common threshold. The final pair-bundle
source cap isepsilon/8192; all parameter and quantifier orders
remain explicit. Incompatible centered families are not claimed
bounded by this compatible statement. No new literature property,
axiom, dependency download, Paper C port, original manuscript-byte
edit or Palomar action is added.

Verified under Lean v4.36.0-rc2: full build passed (13449 jobs); direct axiom audit passed for 10324 declarations using only propext, Classical.choice and Quot.sound; all 8671 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 13.08 GiB.


## Isolated-vertex connected triple joint mass

The actual connected-triple branch with an isolated vertex in its
PAIR-dependence graph is now proved at joint-mass rate1, conditionally
on the SAME explicit finite geometric properties. This includes every
primitive triple and every triple with exactly one dependent pair.
An isolated vertex is direct from each of the two other windows taken
separately; it need not be direct from their combined span. No desired
triple-mass estimate is supplied as a theorem input.

ConnectedTripleLowCrossing proves the finite pointwise bound
q(T)<=K*(sum_{x in T}|c(T erase x)|*p_x+prod_{x in T}p_x)
whenever SOME vertex/complement crossing has binary dimension factor
at most K. The exact pair reconstruction, heterogeneous marginals
and positive one-term enlargement are retained, including zero actual
marginals and incompatible systems. Its finite sum is at most
K*(D1+M3_independent_connected), using the proved pair-incidence cost
without any representation multiplicity. The asymptotic version
allows any fixed a>=0 and yields N^(-3/2+a+epsilon) when some actual
crossing dimension is at most a*L. Its pair-geometry source cap is
epsilon/2048. No isolated-vertex assumption is needed for this low
crossing theorem.

RestrictedSingletonPairCover defines the ACTUAL source-specific
fibers F.filter(T=>x in T and R(x,T)). Its weighted positive cover
sums only actual two-target extensions belonging to that fiber.
It does not replace R(x,T) by the weaker existence of another suitable
source. Membership, the cover and exact source erasure are proved.
ProperPairCrossing proves that directness from each target implies
directness from EVERY proper subfamily of that target pair, without
assuming the target pair is internally direct.

IsolatedVertexDenseTripleMassUnderInputs uses those literal fibers
with an actual isolated vertex and crossing dimension>=eta*L. The
completed full dense minimal-pair cost applies above its singleton
source, even when the other two targets are internally dependent.
Summing the actual source marginals uses the proved bounded mean;
a single common threshold precedes all critical lengths, subgrounds,
triples, vertex choices and pair representations. The resulting
actual joint sum is N^(-1+epsilon). IsolatedVertexTripleMassUnderInputs
partitions the whole isolated-vertex triple population at crossing
threshold L/4. The low branch is stronger than rate1; the dense branch
has rate1. Their sum retains rate1 after error absorption. Both finite
parameter bundles and the pair source capepsilon/4096 are explicit.

This is a proved BRANCH, not a bound for all connected triples.
Triples containing at least two dependent pairs remain to be covered.
The printed sharp exponent41/30 of main14.3 is not claimed for this
larger population. Main15.10 remains in_progress, including its
separate sharp primitive-four and full connected-family requirements;
main15.12's connected tail remains open. Coverage87/167 unconditional,
20 conditional and135 confirmed improvements are unchanged. No new
literature property, axiom, dependency download, Paper C port,
manuscript-byte edit or Palomar action is added.

Verified under Lean v4.36.0-rc2: full build passed (13461 jobs); direct axiom audit passed for 10333 declarations using only propext, Classical.choice and Quot.sound; all 8681 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 13.05 GiB.


## Full coarse connected triple joint mass and activity

The ENTIRE actual connected-triple joint mass and absolute centered
activity are now proved at coarse rate1, conditional on the SAME
existing finite geometric properties. This is a new proved ingredient
for the still-open connected-tail reduction. It is weaker than the
paper's sharp41/30 triple rate and does not complete main14.3, main15.10
or the connected clause of main15.12. Coverage87/167 unconditional,
20 conditional and135 confirmed improvements remain unchanged.

StrongAlignedUnitChannels now preserves actual coprimality in
bounded_coprime_channels; its previously published bounded_channels
statement is unchanged and follows by dropping that field. The SAME
uniform rank and exact-unit proof chooses a finite Q BEFORE C or N.
FiniteInteriorUnitEdges defines the actual finite interior coprime
channel set0<a<b<2a, b<=Q and its actual exact-unit pair population.
Every edge lies in the literal dyadic two-subsets. Channel, source,
actual geometric alignment and either endpoint orientation are proved.
Two such distinct edges inside an actual three-element family yield
an exact source unit and a bounded geometric target at either endpoint.
No private-prime, regularity, separation or compatibility filter occurs.
SharedFiniteInteriorTripleMass therefore applies the ALREADY PROVED
EndpointGeometricTripleMass theorem to obtain actual joint mass
N^(-41/30+epsilon) for all such triples, UNCONDITIONALLY.

StrongAlignedInteriorEdges proves every actual strongly aligned pair
outside the1:1 and1:2 boundary channels belongs to that fixed finite
interior unit population. Coefficients are coprime and bounded before
N; actual sorted endpoint geometry excludes the reversed orientation
except for the1:1 boundary. Coprimality identifies equality b=2a with
the1:2 boundary. The common critical threshold controls ALL actual
pairs and lengths. This classification is UNCONDITIONAL.

TriplePairDependence proves a literal three-element family either
has a vertex direct from EACH other window or at least two actual
dependent pairs. In the latter case its vertices are covered by the
actual two-element dependent edges; their true finite union cardinality
forces at least two edges. No probabilistic or geometric assumption
enters this finite exhaustive fact.

CoarseTriplePairSeeds defines the ACTUAL dependent pairs which are
weak, nonaligned,1:1 or1:2 boundary pairs. Membership and a positive
four-population absolute-activity bound are proved. The completed weak,
nonaligned and boundary estimates give their full activity
N^(-1+theta+epsilon). Only the already explicit source-surface,
ordinary-surface and normalized-curve properties enter the nonaligned
branch; no desired pair/triple bound is postulated. The source cap is
epsilon/64. DependentPairSeedPropagation proves actual joint mass of
EVERY fixed containing order is controlled by2*(2+k)!*N^epsilon
times the exact seed activity, using q(e)<=2|c(e)| only for actual
dependent pairs and the proved positive unordered propagation. The
coarse pair-seed extensions keep rate1-theta with source capepsilon/256.

CoarseTripleFiniteReduction proves a COMPLETE cover of ALL actual
three-element dyadic families: an isolated vertex; an actual weak/
nonaligned/boundary dependent-pair seed; or at least two actual edges
from the fixed finite interior unit-channel set. The theorem chooses
Q after theta and BEFORE C,N. Its proof derives every remaining
dependent pair's sorted alignment, true rank>theta*L, boundary
exclusions and exact-unit membership. It assumes none of the desired
mass estimates and is UNCONDITIONAL.

CoarseConnectedTripleJointMassUnderInputs combines this actual cover
with the completed isolated-vertex bound, the pair-seed propagation
and the unconditional finite-channel41/30 bound. Choosingtheta=epsilon/4
before N gives the ENTIRE actual connected triple joint sum
N^(-1+epsilon), uniformly for every subground G and every actual
subpopulation of connected triples. Duplicate representations are
handled by positive union covers. Its independent finite parameter
bundles and source capsepsilon/8192 andepsilon/1024 are explicit.

CoarseConnectedTripleActivityUnderInputs then uses the ALREADY PROVED
two-sided comparison |T3_joint-A3|<=N^(-3/2+epsilon) to bound the FULL
actual connected third absolute centered activity byN^(-1+epsilon).
This includes incompatible systems and zero marginal probabilities;
it does not silently discard them via a compatible-only comparison.
The three pair-bundle source caps areepsilon/16384,epsilon/2048 and
epsilon/2048. All geometric inputs precede a single threshold uniform
in every critical length and actual dyadic subground. No universal
triple-mass, activity, counting or literature conclusion is itself an
assumed hypothesis. The sharp primitive-four branch and the remaining
small-core connected-tail assembly remain OPEN. No new literature
property, axiom, dependency download, Paper C port, manuscript-byte
edit or Palomar action is added.

Verified under Lean v4.36.0-rc2: full build passed (13481 jobs); direct axiom audit passed for 10349 declarations using only propext, Classical.choice and Quot.sound; all 8700 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 13.00 GiB.


## Actual exhaustive seed cover and fixed-range coarse connected mass

Every actual connected family in ANY prescribed fixed range3..R
now has total JOINT mass N^(-1+epsilon), conditionally on a finite
bundle of the SAME existing geometric properties. The matching
coarse compatible absolute centered activity is also proved.
The threshold precedes ALL orders3<=r<=R, all critical lengths,
all dyadic subgrounds and all actual subpopulations. This is a
coarse bound: it does not assert the printed4/3 rate of15.10 or
an incompatible higher-centered bound. Main15.10 and the connected
clause of15.12 remain in_progress. Coverage87/167 unconditional,
20 conditional and135 confirmed improvements are unchanged.

SmallParticipatingConnected constructs an actual effective
relation nonzero at one prescribed coordinate from its genuine
intersection with the span of the other coordinates. It uses
extension by zero and a single-coordinate subtraction, keeping
all effective local kernels. At order at most3, coordinatewise
participation makes the canonical partition connected. This only
requires EACH coordinate to have SOME relation; it does not assume
one simultaneously full-support binary relation. CrossingPairTriple
therefore proves a dependent pair plus an extra window crossing
its span is a connected triple. It also proves every nontrivial
connected family has positive actual relative nullity.

DirectCrossingSeedFamilies defines the literal unordered unions
of a dependent pair and an internally direct minimal crossing of
fixed sizeh>=2. Membership, exact size2+h, ground containment and
a positive double-cover mass bound are proved. The completed
source-relative direct-crossing estimate gives unordered seed
mass N^(-5/3+epsilon), and positive propagation retains this rate
for every fixed containing order. No compatibility is required
for these actual joint bounds. Source caps areepsilon/2048 for
seeds andepsilon/4096 for fixed extensions.

ConnectedSeedCover proves the ENTIRE actual finite combinatorial
cover of a connected I withcard(I)>=3. It contains either a
primitive seed of size>=3; a connected triple; a low-intersection
pair-pair seed; a dense minimal pair-crossing seed; or an internally
direct crossing seed of target size2..card(I)-2. A primitive
subfamily is genuinely extracted. If it is a pair, an actual
minimal crossing to the complement is chosen. Singleton crossings
give connected triples. Internally dependent larger crossings
contain a primitive subfamily: size>=3 returns to the first class;
a proper primitive pair is direct from the source and gives a
zero-intersection pair-pair seed. The remaining pair is split at
its actual span-intersection dimension. Thus proper subfamilies
with INTERNAL relations are retained, and no unproved seed-cover
hypothesis is supplied to an asymptotic theorem.

VariableSeedMassPropagation extends the completed unordered
positive propagation to a SINGLE actual seed population of
VARYING sizes1..r. The actual target population is positively
covered by seed-cardinality fibers. Exact fiber reindexing counts
each source seed once, so only the true fixed target factorialr!
and the chosen subpower factor remain. All source/target masses
are actual heterogeneous joint probabilities, including zeros.

ConnectedSeedCatalog fixes the crossing cutoff atL/12 and collects
all actual seeds needed for orders up toR. Its coverage, actual
ground containment, minimum size3 and positive finite mass bound
are proved. CoarseConnectedParameters is a FINITE parameter bundle:
its hypotheses contain ONLY the existing chosen-source surface,
ordinary surface and normalized curve properties inside the already
recorded Dense/Pair interfaces. It contains no desired activity,
seed mass, connected mass or counting conclusion. The finite lists
and geometric choices precede N.

ConnectedSeedCatalogUnderInputs proves the ENTIRE catalog joint
mass at rate1: primitive seed rate1; connected triple rate1; low
pair-pair rate5/4 at cutoff1/12; dense pair-crossing rate5/3; and
direct-crossing rate5/3. The actual finite channel/order unions
cost at most2*(R+1)+3, which is absorbed after a common threshold.
All geometric bundle source caps are recorded in the Hypotheses
structure and remain finite. There is no order growing with N.

CoarseConnectedJointMassUnderInputs.uniform_range combines this
completed catalog with varying-size propagation. The source
catalog is restricted to actual seed sizes<=r; its full mass bounds
the restricted mass positively. The actual factorialr! is bounded
byR! and absorbed. This proves total actual connected joint mass
N^(-1+epsilon) uniformly for every3<=r<=R, without regularity,
compatibility or positive-marginal restrictions. The separate
uniform_compatible_activity theorem uses the true compatible
centered-to-joint comparison and absorbs2^R, yielding the same
rate for compatible absolute centered activity. Incompatible
higher centered coefficients are not silently excluded from a
purported full statement. The parameter margin isepsilon/4 for
the joint theorem andepsilon/8 for compatible activity. The next
open step is the remaining small compatible relation-core mass
and its connected-tail assembly. No new literature property,
axiom, dependency download, Paper C port, manuscript-byte edit
or Palomar action is added.

Verified under Lean v4.36.0-rc2: full build passed (13501 jobs); direct axiom audit passed for 10367 declarations using only propext, Classical.choice and Quot.sound; all 8723 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 12.95 GiB.


## P1-MATH-0136 — Complete connected tail at power83/60 with coarse positive fixed-order inputs

The ENTIRE connected tail in main15.12 improves from
N^(-4/3+epsilon) to N^(-83/60+epsilon), with the same fixed cutoff256,
true compatible-nullity cap2L, fixed positive weight and every
K_N=o(L), under the same three finite geometric properties.
The source's already available low-rank83/60 budget is preserved
when combined with the now proved3/2 large-core and small-core
budgets, instead of weakening the combined result to4/3.
Moreover the small-core proof needs only the coarse ACTUAL connected
joint rate1 at fixed orders, not the sharper4/3 centered proposition
15.10. Every canonical component has size>=2 because the compatible
ten-core ratio forces a nonzero centered coefficient. A component
of size>=3 contains a seed from the completed positive catalog;
otherwise two direct canonical pairs supply a controlled four-window
seed. The same positive propagation thus bounds the full actual
small-core joint mass by N^(-1+epsilon). Apply the independently
proved all-cardinality complement deficit N^(-1/2+epsilon) DIRECTLY
to q(D), and keep the already proved exact pair-core branch. This
avoids both a sharp primitive-four dependency and a separate estimate
for incompatible fixed higher-centered activity. Those stronger
fixed-order tasks remain open and are not implicitly asserted.


## Completion of both15.12 clauses and stronger connected tail

Main15.12 is now COMPLETE CONDITIONALLY on the SAME existing
finite geometric properties: its entire growing-order connected
clause and its all-cardinality primitive clause are both proved.
The connected clause has the stronger exponent83/60 instead of4/3;
the primitive clause retains its previously proved UNCONDITIONAL
stronger exponent7/5. Finding136 records the full connected
improvement, distinct from the earlier primitive improvement133.
Unconditional numbered coverage remains87/167; conditional results
increase from20 to21. Confirmed improvements increase135 to136.

The connected theorem includes EVERY actual dyadic subground,
fixed positive cardinality weightu, every finite actual connected
population with256<card(I)<=K(N), and true compatible nullity
rho*(I)<=2L. K(N)/log(N)->0 is selected before the common critical
threshold; in the critical band this is the source's K_N=o(L).
The primitive assertion sums every size>256 with NO upper cutoff;
its stronger existing version also includes size256. All marginals,
zero probabilities and incompatible centered coefficients are actual.
No good-source, private-prime, separated or regular-only replacement
is made to the connected population.

DirectBlockDisjoint proves distinct parts of a genuine direct
partition have disjoint effective sum-spaces, using injectivity
of block addition and two single-coordinate tuples. No finite-
dimensional ambient assumption is needed. NoSingletonSeedCover
transfers this to actual canonical component images. Any family
with at least3 vertices and no singleton canonical components
contains a controlled connected seed: either a connected component
of size>=3 contains a seed from the completed catalog, or two
actual canonical pair components form a zero-intersection low
pair-pair seed. The pair components are genuinely dependent and
their actual spaces are direct, with no assumed factorization cost.

The previously proved connected joint-range theorem is strengthened
by exposing uniform_catalog_extensions for ALL actual families
containing catalog seeds. Its older uniform_range and compatible
activity statements remain unchanged. NoSingletonJointMassUnderInputs
therefore proves actual joint mass N^(-1+epsilon) for ALL fixed
orders3..R without singleton components. Its weighted version
sums every size3..R simultaneously, absorbing only fixed powers
and the true finite cardinality-fiber constant. Its finite geometric
bundle is the SAME CoarseConnectedParameters bundle; it does not
assume any desired mass, count or activity conclusion.

SmallCoreJointMassUnderInputs applies this to the actual compatible
ten-cores of sizes3..255. The PROVED ratio q(D)<=2c(D) makes their
centered coefficient nonzero, so their canonical components cannot
be singleton. Their ENTIRE weighted actual joint mass is consequently
N^(-1+epsilon), even when the core is disconnected. This avoids any
need for a sharp fixed higher-centered estimate or for assuming the
full4/3 proposition15.10. Applying the completed UNCONDITIONAL
all-cardinality independent deficit directly to q(D), not to a
surrogate centered activity, proves their actual source-deficit
mass is N^(-3/2+epsilon). The source cap is255 before all actual cores.

SmallCoreSourceMassUnderInputs combines this with the ALREADY PROVED
size-two core branch and the EXACT two/at-least-three source split.
Thus the WHOLE small compatible-core sourceMass has rate3/2.
The exact chosen-core finite cover and retained rank under the
sublogarithmic cardinality cap prove the entire high-rank, small-core
connected branch at rate3/2, uniformly in its actual growing orders.
No enumeration of peeling orders or growing factorial cost is added.

ConnectedTailUnderInputs.uniform_tail now covers the ENTIRE connected
population by low compatible nullity, a large chosen core, and the
remaining high-rank small core. The three PROVED rates are respectively
83/60,3/2 and3/2. Positive actual union bounds and fixed-factor
absorption retain83/60 for their full sum. The low and large-core
branches are unconditional; only the small-core arithmetic uses
the SAME recorded chosen-source surface, ordinary surface and
normalized curve properties, in explicit FINITE parameter bundles.
The final coarse bundle margin isepsilon/64; the pair source caps
are sizeCap((epsilon/128)/128) and sizeCap((epsilon/128)/4096).
Every geometric parameter precedes one N-threshold uniform in
critical lengths, grounds, all orders and all actual families.

ConnectedTailUnderInputs.article_15_12 weakens83/60 to the printed
4/3 and combines it with the separately proved literal all-cardinality
primitive assertion under the same threshold, proving BOTH clauses
of the numbered source proposition. No desired connected or primitive
bound is supplied as an external input. The three geometric literature
properties remain ordinary explicit arguments and are NOT axioms or
claimed internally proved. Main15.10's sharper fixed4/3 assertion,
including primitive-four sharpness and incompatible higher activity,
remains open; it is not needed for this completed tail proof. No
new literature property, dependency download, Paper C port, original
manuscript-byte edit or Palomar action is added.

Verified under Lean v4.36.0-rc2: full build passed (13513 jobs); direct axiom audit passed for 10381 declarations using only propext, Classical.choice and Quot.sound; all 8737 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 12.92 GiB.


## P1-MATH-0137 — Full fixed connected activity at power1 including incompatibility

The full fixed-order connected absolute centered bound of
companionT14.1 improves from N^(-4/5+epsilon) to N^(-1+epsilon)
under the same existing finite geometric properties. It holds on
any actual dyadic subground, including affine incompatibility and
zero marginals; the separate contact bound retains its unconditional
rate1. The proof first bounds all dependent joint masses and all
absolute centered masses at rate2/3. Exact inverse centering then
charges each incompatible connected family to proper centered sources
and their actual failed independent complements. The latter have
the already proved rate1/2, so the entire incompatible contribution
has rate7/6. Combining it with the completed compatible connected
joint/centered rate1 gives the stronger full rate1. This avoids a
homogeneous-majorant argument for separated systems and avoids
assuming the sharper uncompleted4/3 fixed connected proposition15.10.
Only fixed finite ranges are asserted; the constant and threshold
may depend on their order cutoff, selected before N.


## Complete fixed connected centered activity including incompatible systems

CompanionT14.1 is now COMPLETE CONDITIONALLY under the SAME three
explicit finite geometric properties, with a stronger connected
exponent1 instead of4/5. Its separate contact assertion is retained
at rate1 and is UNCONDITIONAL. Finding137 records the stronger full
fixed connected activity. Unconditional coverage remains87/167;
conditional results increase21 to22; confirmed improvements136 to137.

The bound includes EVERY actual connected family at every prescribed
fixed orderr>=3, throughout any fixed range3..R with a common threshold.
Affine incompatibility and zero actual marginals are included. The
actual ground can be any subset of the full dyadic block, so it includes
the source's regular ground. All order cutoffs, finite geometric
parameters and error margins precede N. This is a fixed-order result,
not a bound uniform in an arbitrary order growing with N.

DependentSeedCover defines the actual union of all dependent pairs
and the completed connected seed catalog. It proves every actual
dependent family of size<=R contains one of those seeds, by extracting
a genuine primitive subfamily. It also proves dependent populations
at sizes0 and1 are empty from their actual zero nullity.
FixedDependentJointMassUnderInputs applies the proved varying-size
positive propagation, the sharp actual pair joint mass at rate2/3,
and the complete catalog at rate1. Consequently ALL actual dependent
joint masses in every fixed range2..R have rate2/3. No desired joint
or counting bound is supplied as a hypothesis.

FixedAbsoluteActivityUnderInputs uses the completed exact absolute
centering decomposition. Its independent dependent-family term has
the already proved unconditional rate1; the other terms are actual
dependent joint masses times exact independent complement coefficients.
The bounded actual mean controls those finite coefficients. This
proves FULL absolute centered activity at rate2/3 throughout1..R,
including disconnected, incompatible and irregular families. It uses
the SAME finite geometric bundle and one actual pair-input bundle.

IncompatibleConnectedDeficit proves the exact finite mechanism missing
from a compatible-only argument. When q(I)=0, inverse centering bounds
|c(I)| by the sum of proper centered-source terms. The empty source
is the actual independent product. EVERY nonempty proper sourceD
inside a connectedI has its actual complementI\D in the failed
independent extension population. A proved injective complement
fiber bound handles incidence and duplicate sources without a fake
multiplicity assumption. Thus incompatible activity is at most its
actual independent mass plus the proper-source absolute activity
weighted by the exact all-cardinality independent deficit. This
finite theorem requires no positivity, regularity or geometric input.

IncompatibleConnectedActivityUnderInputs combines that finite bound
with the source rate2/3 and the independently proved complement
deficit rate1/2. The independent connected term has rate at least3/2
at orders>=3. The ENTIRE incompatible connected absolute activity
therefore has rate7/6, uniformly over every fixed range3..R and every
actual subpopulation. All source-cardinality fibers and their fixed
constant are proved. Its geometric margins areepsilon/32 for the
coarse bundle and source capsizeCap(epsilon/32768) for the pair bundle.

CoarseConnectedActivityUnderInputs.uniform_range combines the
completed compatible rate1 with this incompatible rate7/6, using
an exact positive/zero joint split. It proves FULL actual connected
absolute activity N^(-1+epsilon) for every3<=r<=R. The final finite
coarse bundle margins areepsilon/16 andepsilon/64, with pair source
capsizeCap(epsilon/65536). Its companion_T14_1 theorem weakens1 to
the printed4/5 and simultaneously supplies the source's contact
bound from FixedContactCenteredActivity.uniform_bound. The contact
proof needs only the already proved unconditional subpower moments.

The earlier weaker half-power auxiliary estimates under BCN remain
valid historical declarations; they are not inputs to this completion.
Only the recorded chosen-source surface, ordinary surface and
normalized curve properties remain unproved external arguments.
The sharper4/3 assertion of main15.10, its primitive-four sharpness,
and the all-cardinality companionT16.1–T16.3 assertions are not claimed
proved here. No new literature property, axiom, dependency download,
Paper C port, manuscript-byte edit or Palomar action is added.

Verified under Lean v4.36.0-rc2: full build passed (13525 jobs); direct axiom audit passed for 10392 declarations using only propext, Classical.choice and Quot.sound; all 8750 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 12.88 GiB.


## P1-MATH-0138 — All-cardinality connected exponent min(1,2-eta)

The all-cardinality connected bound in companion T16.1 improves
from exponent min(4/5,2-eta) to min(1,2-eta) under the same existing finite
geometric properties. It applies to every actual dyadic subground, with
zero actual marginals and affine incompatibility included. All sufficiently
large cardinalities satisfy the stronger rate 2-eta unconditionally, by
the completed original participating tail with exact heterogeneous weights
and the actual compatible-nullity majorant. Every coordinate participates
in some relation; a single binary relation meeting every block is not
needed. The remaining finite cardinality range uses the full connected
rate1 of T14.1. The cardinality threshold, order cutoff and finite geometric
bundles are chosen before N. This also extends the displayed inequality to
eta>=2, where it need not express decay; the source's regime 0<=eta<2 is
fully included.


## Complete all-cardinality bounded-nullity connected theorem

Companion T16.1 is complete conditionally under the same three explicit
finite geometric inputs. The all-cardinality bound improves from
N^(-min(4/5,2-eta)+epsilon) to N^(-min(1,2-eta)+epsilon).
It holds for every actual subground of the full dyadic block and every
actual connected subpopulation with at least three elements and compatible
nullity at most eta*L. There is no upper cardinality cutoff. The proof in
fact allows every eta>=0; the source's nontrivial decay regime eta<2 is
included. Zero marginals and affine incompatibility are retained.

ConnectedParticipatingWindows.witnesses proves that each coordinate of a
connected family of cardinality at least two participates in an actual
relation. Its relation is allowed to depend on the chosen coordinate.
No simultaneous binary relation with full support is asserted or assumed.

ConnectedBoundedNullityTail.uniform_bound is unconditional. For fixed
eta,u,C,epsilon it selects a fixed integer s and then a common N threshold,
and bounds all actual connected families of cardinality at least s by
N^(-(2-eta)+epsilon). It applies the completed original participating
all-cardinality independent-weight tail to the exact heterogeneous weights
2*u*p_x, whose actual marginal cap is proved. The actual compatible-nullity
majorant contributes at most N^(eta+small margin), proved uniformly from
the critical window band and the actual rank cap. No geometric counting
input or homogeneous substitution for the actual marginals is needed in
this large-cardinality sector.

FixedConnectedWeightedUnderInputs.uniform_bound sums the completed full
fixed connected activity over every order from 3 to a prescribed R. The
weight u^r and the finite number of cardinality fibers are absorbed only
after R and u have been fixed. This includes incompatible systems, using
the completed T14.1 proof rather than a compatible-only estimate.

AllCardinalityConnectedUnderInputs.uniform_bound chooses s from the
unconditional large-cardinality theorem before selecting the finite
geometric parameter bundles for the remaining cardinalities 3<=r<s.
Only after these choices and the explicit geometric hypotheses does it
choose N0. An exact disjoint cardinality split and a fixed-factor
absorption give exponent min(1,2-eta), with one N0 for all actual grounds,
lengths in the critical band and all cardinalities. The final geometric
margins are epsilon/64 and epsilon/256 for two existing coarse parameter
bundles of order s, and sizeCap(epsilon/262144) for the existing pair-input
bundle. These premises are exactly previously recorded geometric
properties, not a desired activity bound. companion_T16_1 supplies the
literal printed exponent min(4/5,2-eta) by monotonicity.

Finding P1-MATH-0138 records the improved exponent and the coordinatewise
participation argument. Unconditional coverage remains 87/167; conditional
coverage increases from 22 to 23; confirmed improvements increase from
137 to 138. T16.2 and T16.3, sharp main15.10 and the final stopped expansion
are not claimed here. No original manuscript byte, external dependency,
axiom or Palomar registration is changed.

Verified under Lean v4.36.0-rc2: full build passed (13533 jobs); direct axiom audit passed for 10397 declarations using only propext, Classical.choice and Quot.sound; all 8755 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 12.86 GiB.


## P1-MATH-0139 — All-cardinality positive core exponent1

The positive all-cardinality high-nullity core bound in companion
T16.2 improves from N^(-4/5+epsilon) to N^(-1+epsilon) under the same finite
geometric properties. Every positive-projection core has no singleton
canonical components. Its bounded cardinalities>=3 therefore have the
completed actual seed-catalog rate1 directly, while its high-nullity pairs
have rate1 by excluding every aligned height>=3 and using the two literal
boundary populations plus the full nonaligned activity. This replaces the
exceptional activation event and high-moment Holder argument. The
sufficiently large cardinality sector is independently unconditional at
rate3/2 from the complete multi-anchor budgets and actual relative-rank
amplification. The formal scope includes all eta>=0 and even t>=2 with
t>=eta+2, all actual dyadic subgrounds and all affine-incompatible systems
with joint mass zero. The cutoff and finite geometric bundles precede N.


## Complete all-cardinality positive core theorem

Companion T16.2 is complete conditionally, with the stronger positive
joint-mass exponent1 instead of4/5. The bound is uniform over all actual
cardinalities, all actual dyadic subgrounds and all actual t-cores whose
relative nullity lies in (L/2,eta*L]. The source's compatible population is
included; the formal inequality also permits incompatible systems, which
have actual joint mass zero. It holds for even t>=2, eta>=0 and t>=eta+2,
thus includes the source's eta>1 regime without imposing that unnecessary
restriction. Only the same three existing finite geometric properties
remain explicit theorem arguments. No desired mass estimate is a premise.

CoreCanonicalComponents proves that a singleton canonical part forces its
coordinate projection to be the zero linear map, so its exact deletion
nullity loss is zero. Consequently every t-core with t>=2 has only
canonical components of cardinality at least two, with no compatibility or
cardinality restriction. This is a structural statement for actual
square-class relation kernels, not the size<256 ten-core moment ratio.

HighNullityPairMassUnderInputs handles the entire size-two population with
relative nullity>L/2. The proved uniform enlarged alignment rank bound
excludes every aligned coefficient height>=3. Exact orientation and
coprimality leave only the literal1:1 and1:2 boundary populations. Their
full centered activities are already bounded unconditionally at rate1.
The entire nonaligned activity has the existing conditional rate1.
Every dependent pair satisfies actual q<=2|c|, including q=0, so positive
union bounds and a fixed-factor absorption give weighted joint mass rate1
for ALL such high-nullity pairs. No Private, good-source, regularity,
selected-unit or affine-compatibility filter is imposed.

LargePositiveCoreTail proves an unconditional sufficiently large
cardinality rank-mass and joint-mass bound of rate3/2. For arbitrary even
t>=2 it verifies all multi-anchor parameter conditions with A=8t,
beta=1-1/(4t), sigma=1-1/(16t). The moderate independent exponent is exactly
-t+1/2. The positive saturated decay parameter selects a finite size s
before N. Multiplying the completed multi-anchor independent budgets by
the actual relative-rank amplification N^(eta+small margin) gives rate3/2
when t>=eta+2, and the actual joint mass is at most that rank weight. Each
block may use a different actual heavy relation. Heterogeneous marginals,
zero marginals and all actual core populations are retained.

FixedPositiveCoreMassUnderInputs proves joint mass rate1 for every
prescribed bounded cardinality range. Sizes>=3 use the completed actual
no-singleton seed catalog and positive extension propagation; size2 uses
the new high-nullity pair estimate. This avoids an exceptional activation
event and a Holder argument with high count moments. The full
AllCardinalityCoreMassUnderInputs.uniform_bound selects the unconditional
large-cardinality cutoff first, the finite coarse and pair geometric
parameter bundles second, and N0 last. It then combines the finite range
at rate1 with the unconditional rate3/2 tail. Final geometric margins are
epsilon/32 for the coarse bundle and sizeCap(epsilon/256) for the pair
bundle. companion_T16_2 supplies the literal source exponent4/5.

Finding P1-MATH-0139 records the improvement. Unconditional coverage stays
87/167; conditional coverage increases23 to24; confirmed improvements
increase138 to139. T16.3 and the final stopped expansion remain open at
this checkpoint. No original manuscript bytes, dependencies, axioms,
Paper C port or Palomar action are added.

Verified under Lean v4.36.0-rc2: full build passed (13543 jobs); direct axiom audit passed for 10407 declarations using only propext, Classical.choice and Quot.sound; all 8765 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 12.83 GiB.


## P1-MATH-0140 — Linear and growing connected range at exponent1

Companion T16.3 improves from exponent4/5 to1 on its full stated
linear range K<=L/(2*(t-2)), under the same finite geometric properties.
The result includes all eta>=0, every actual dyadic subground, affine
incompatibility and zero marginals. The proof constructs an actual positive
t-core after maximizing compatible nullity, proves its exact deletion loss
budget and retains nullity>L/2 in the stated linear range. Summing exact
heterogeneous free-complement weights gives a fixed exponential factor,
without counting deletion orders. The completed positive-core rate1 and
all-cardinality low-nullity rate1 give the full result. A separate proved
uniform cap handles K_N/log(N)->0; an even t is selected before N. For
eta=3/2,t=4 the bound is valid for the literal K<=L/4 range, as in the
source, with the stronger exponent1.


## Complete connected theorem on the literal linear and growing range

Companion T16.3 is complete conditionally under the same three explicit
finite geometric properties, with exponent1 instead of4/5. The uniform
linear-range theorem keeps the source's full cardinality scope
2*(t-2)*K<=L for any fixed even t>=2 with t>=eta+2. One N0 is chosen before
all admissible critical lengths, all such K, all actual dyadic subgrounds
and all actual connected subpopulations of sizes3..K and compatible
nullity<=eta*L. In particular eta=3/2,t=4 gives the literal K<=L/4 range.
The separate sublogarithmic theorem treats every actual integer schedule
K_N/log(N)->0. companion_T16_3 chooses an adequate even t before N and
supplies the printed exponent4/5 for every eta>=0. No fixed-order estimate
is promoted to a growing-order one.

VariableRelationCore.exists_bound proves the actual compatible peeling
construction at arbitrary t. It first chooses a positive-mass subfamily
attaining the compatible-nullity maximum and applies the proved terminating
trace with deletion threshold t-2. The terminal family is a positive actual
t-core. Its nullity is at most the original compatible maximum, and its
loss budget is at most (t-2)*(|I|-|D|). The already proved actual peeling
majorant includes all coordinates outside the maximizing compatible family,
so incompatible original I and zero marginal sites remain included.
weighted_bound transports the result to exact heterogeneous independent
complement weights with fixed factor 2^(t-1)*u per coordinate.

HighNullityCoreCover defines the entire actual positive t-core population
with relative nullity in (L/2,eta*L]. If rho_*(I)>L and
2*(t-2)*|I|<=L, the proved loss budget forces the terminal core into that
population. The positive supersets bound sums all independently weighted
complements, giving exp(sum_x 2^(t-1)*u*p_x) times the actual core joint mass.
There is no deletion-order factor, factorial multiplicity assumption or
compatibility restriction on the original I. All incidence bounds and
complement reconstruction identities are proved in Lean.

HighNullityClosureUnderInputs combines the completed all-cardinality
positive core rate1 with the proved actual mean cap, which bounds the free
complement exponential by a fixed constant. It therefore controls the
ENTIRE high-compatible-nullity activity at rate1 throughout the literal
linear cardinality range, even without connectedness. Its finite geometric
arguments are the already recorded coarse and pair parameter bundles.

GrowingConnectedUnderInputs.uniform_linear_range splits the actual
connected population at rho_*=L. The low sector uses the completed T16.1
at eta=1, valid at all cardinalities with rate1. The high sector uses the
new actual core closure, also with rate1. A fixed-factor absorption
completes the full connected estimate at one common threshold. The final
low-sector coarse margins are epsilon/128 and epsilon/512, with pair cap
sizeCap(epsilon/524288); the core-sector coarse margin is epsilon/128 and
its pair cap is sizeCap(epsilon/1024). All cutoffs and finite geometric
parameters precede N. uniform_sublog_range derives the literal linear
budget uniformly in every critical length from K_N/log(N)->0, rather than
assuming it silently. The final wrapper explicitly constructs an even t.

Finding P1-MATH-0140 records the stronger growing-range exponent and exact
heterogeneous closure. Unconditional coverage remains87/167; conditional
coverage increases24 to25; confirmed improvements increase139 to140.
T16.1,T16.2,T16.3 are now all complete conditionally. The sharper4/3 fixed
connected main15.10, the exceptional active event T15.2 and the final
stopped expansion are not claimed complete. No new literature premise,
axiom, external dependency, manuscript-byte edit or Palomar action is added.

Verified under Lean v4.36.0-rc2: full build passed (13551 jobs); direct axiom audit passed for 10415 declarations using only propext, Classical.choice and Quot.sound; all 8774 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 12.80 GiB.


## Full fixed absolute activity and the nonconnected quadratic tail

Preparatory progress for main Theorem6.4: full actual absolute centered
activity at every prescribed fixed order>=3 now has rate1, under the same
three existing finite geometric properties. The result is uniform over
every fixed order range3..R and every actual dyadic subground. It includes
all disconnected systems, affine incompatibility and zero marginals.
Main6.4 remains IN PROGRESS: its quadratic factorial-moment correction,
ordinary Touchard correction and all higher factorial cumulants are not
completed by this activity estimate alone. Coverage remains87/167
unconditional and25 conditional; improvements remain140.

BoundedComponentActivity.population is the actual finite ambient candidate
population of all subsets of G with sizes2..R. Its sum_bound proves the
finite cardinality-fiber mass bound. finite_bound controls every actual
nonconnected nonempty family of size<=R by the quadratic positive polymer
tail W^2*exp(W)/2, where W is that population's total absolute centered
activity. The proof restricts to nonzero coefficients, uses actual canonical
components with cardinalities>=2, proves their union recovers the original
family, and applies exact centered factorization. At least two components
are forced by nonconnectedness. No decomposition multiplicity or
independence assumption is supplied as a premise.

NonconnectedActivityUnderInputs.uniform_bound combines this exact finite
bound with the completed all-order coarse absolute mass rate2/3. A fixed
small margin min(epsilon/4,1/12) ensures the component population tends to
zero, so its exponential is bounded by exp(1). The squared mass gives the
FULL nonconnected rate4/3 after absorbing the proved finite-cardinality
constant. Both actual zero coefficients and zero marginal sites remain
included. All cutoffs and margins precede N.

FullFixedActivityUnderInputs.uniform_range makes an exact connected versus
nonconnected split at each order3..R. The connected sector has the completed
rate1, and the nonconnected sector has the new rate4/3. A fixed factor2
absorption gives rate1 for the entire actual absolute centered mass. Only
existing coarse and pair geometric parameter bundles occur as hypotheses;
no target activity estimate or new literature premise is assumed.

This checkpoint adds3 modules,4 theorems and1 definition. It supplies a
finite-order input for the future main6.4 moment correction, without
claiming that correction or a growing-order estimate. No new mathematical
finding, original manuscript-byte edit, dependency download, axiom,
Paper C port or Palomar registration is added.

Verified under Lean v4.36.0-rc2: full build passed (13557 jobs); direct axiom audit passed for 10419 declarations using only propext, Classical.choice and Quot.sound; all 8779 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 12.78 GiB.


## P1-MATH-0141 — Fixed quadratic factorial remainder at exponent1

The exact-parameter fixed factorial-moment remainder in main6.4
improves from N^(-4/5+epsilon) to N^(-1+epsilon) under the same finite
geometric properties. It holds on every actual dyadic subground with
heterogeneous marginals, affine incompatibility and zero marginals included.
The full higher centered activity has rate1; disconnected contributions
have rate4/3 through their actual canonical-component quadratic tail.
A finite pointed-incidence calculation controls collisions and deletion of
the actual pair indices at cost O(1/N). The exact cardinality convolution
then isolates the pair correction. Its diagonal squared-marginal term is
retained, so the coefficient is the full second factorial cumulant. All
orders and finite constants precede N. This finding concerns the factorial
clause only; the remaining ordinary-moment and higher-cumulant clauses of
the multi-conclusion theorem are not claimed complete at this checkpoint.


## Exact fixed quadratic factorial correction at exponent1

The exact ACTUAL-PARAMETER factorial-moment clause of main Theorem6.4 is
now proved conditionally, with remainder exponent1 instead of4/5. For every
fixed r>=2 it gives E(Z_G)_r=mu_G^r+choose(r,2)*mu_G^(r-2)*a_G+O(N^(-1+epsilon)),
where mu_G is the exact actual heterogeneous mean and a_G is the exact
second factorial cumulant, including its diagonal correction. One threshold
precedes all critical lengths and all actual grounds G contained in the
full dyadic block. No local regularity, separation or affine compatibility
filter is imposed. Only the same three finite geometric properties remain
explicit theorem arguments. Finding P1-MATH-0141 records the improvement.

Main6.4 remains IN PROGRESS because the separate ordinary Touchard correction,
uniform boundedness clause and arbitrary higher factorial cumulants have
not yet been assembled under these geometric inputs. Its optional nominal
parameter reformulation is also not claimed here. Unconditional numbered
coverage remains87/167 and conditional coverage remains25. Confirmed
mathematical improvements increase140 to141. The exact factorial clause is
not counted as the whole multi-conclusion numbered theorem.

ElementarySymmetricApproximation proves the actual collision error without
replacing the individual marginals by a common probability. Its pointed
incidence identity expresses (r+1)*e_(r+1) as the sum over r-element sets of
their actual product times the sum of weights outside that set. The exact
factorial increment and induction give 0<=mu^r-r!*e_r<=r^2*kappa*M^r when
all weights are nonnegative, individually<=kappa, and the mean<=M with
M>=1. The raw elementary error follows by division by r!, and deletion of
at most s actual indices adds only s*r*kappa*M^r. These are finite real
inequalities at every order, proved with all repeated-index contributions.

QuadraticMomentApproximation isolates the exact cardinality0,1,2 layers
of the actual inverse-centering convolution. The empty layer is the actual
elementary independent weight, the singleton layer vanishes, and the pair
layer retains its actual complementary elementary weight. The entire higher
layer is bounded by M^r times the sum of ALL absolute centered coefficients
at orders3..r. The deletion estimate controls the pair-layer replacement by
the full actual mean. The proved factorial/choose identity supplies exactly
choose(r,2). The diagonal sum of individual squared marginals is retained,
yielding the actual second factorial cumulant rather than a distinct-index
covariance approximation. The resulting finite error is explicit in kappa,
the full pair absolute activity and the full higher-order activity. No
probabilistic or arithmetic conclusion is supplied as a hypothesis.

SubpowerPairAbsoluteActivity proves an unconditional subpolynomial bound
for the ENTIRE absolute pair activity. It uses the already proved actual
joint-mass subpower bound and the independently bounded actual mean. Zero
marginals and incompatible pairs are included. This weak input suffices
because the pair-layer deletion error contains an extra factor kappa=O(1/N).

FixedQuadraticFactorialMomentsUnderInputs combines the complete higher
absolute activity rate1 with the unconditional pair subpower bound, actual
marginal cap and actual mean cap. It instantiates the finite quadratic
inequality, transports the exact subset moment to the actual infinite-law
factorial moment and identifies the full second factorial cumulant using
the proved heterogeneous covariance formula. All finite r-dependent
constants are absorbed after r is fixed. The final coarse geometric margins
are epsilon/128 and epsilon/512, with pair capsizeCap(epsilon/524288);
the nonconnected coarse margin is min(epsilon/32,1/12)/8, with its existing
pair capsizeCap(min(epsilon/32,1/12)/8192). These are existing finite input
properties, selected before N. No BCN premise or target moment bound is used.

This checkpoint adds4 modules and13 theorems. No original manuscript byte,
external dependency, new axiom, Paper C port or Palomar registration changes.

Verified under Lean v4.36.0-rc2: full build passed (13565 jobs); direct axiom audit passed for 10432 declarations using only propext, Classical.choice and Quot.sound; all 8792 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 12.76 GiB.


## Extension of P1-MATH-0141 — Exact ordinary Touchard correction at exponent1

The exact-parameter factorial AND ordinary fixed-moment remainders
in main6.4 improve from N^(-4/5+epsilon) to N^(-1+epsilon) under the same
finite geometric properties. The bounds hold on every actual dyadic
subground with heterogeneous marginals, affine incompatibility and zero
marginals included. The factorial proof uses full higher centered activity
at rate1, a nonconnected quadratic tail at rate4/3, and finite pointed
collision/deletion inequalities retaining the complete diagonal correction.
The ordinary proof uses the exact Stirling transform and the genuine
Touchard polynomial, whose evaluation is proved equal to the Poisson
ordinary moment and whose actual second derivative gives the displayed
quadratic coefficient. A common threshold is taken after all finitely many
orders and geometric bundles. Uniform boundedness of every fixed ordinary
moment is also proved directly, without the final law approximation. The
arbitrary higher factorial-cumulant clause is not claimed complete yet.


## Exact ordinary fixed correction and bounded count moments

Main6.4 now also has its exact ordinary Touchard correction and uniform
boundedness of every fixed ordinary moment under the same three existing
finite geometric properties. The ordinary remainder is stronger, with
exponent1 instead of4/5, on every actual dyadic subground. Finding141 is
EXTENDED to the factorial AND ordinary moment corrections; it is not counted
a second time. Main6.4 remains IN PROGRESS until arbitrary higher factorial
cumulants and the optional nominal-parameter reformulation are checked.
Numbered coverage stays87/167 unconditional and25 conditional; confirmed
improvements stay141.

TouchardCountMoments.touchard is the actual finite Stirling polynomial.
ordinary_eq_factorial transports the exact natural power/falling-factorial
identity to the actual infinite count moments. poisson_hasSum proves that
its evaluation is the ordinary moment of the genuine Poisson mass sequence,
using the completed actual Poisson factorial-moment sums. second_derivative
uses the actual iterated polynomial derivative and the exact descending
factorial/choose identity. Thus the correction really is a_G*T_r''(mu_G)/2,
not a separately named surrogate polynomial. count_zero proves the actual
order-zero moment equals1, including the empty ground.

TouchardApproximation.finite_bound transfers any finite collection of exact
quadratic factorial errors to the ordinary correction, with the explicit
sum of nonnegative Stirling coefficients as its factor. FixedMomentInputs
packages precisely the previously listed five finite coarse/pair geometric
arguments; its Hypotheses fields contain ONLY those geometric properties.
No desired moment estimate is included. Its uniform_fixed theorem is a
proved wrapper around the completed actual factorial correction.

FixedQuadraticOrdinaryMomentsUnderInputs.uniform_fixed selects the finite
geometric bundles for all factorial orders up to the prescribed r BEFORE N.
It proves the order0 and1 corrections exactly, takes a common maximum of the
finitely many actual thresholds, and absorbs the fixed Stirling coefficient
sum. It gives the literal Touchard conclusion with remainder N^(-1+epsilon)
for every fixed r>=0, every critical length and every actual dyadic subground.
All exact actual means, diagonal corrections, zero marginals and affine
incompatibility are preserved.

FinitePairActivityInputs packages the already proved entire sharp pair
activity bound into one existing finite pair-input bundle with source
capsizeCap(1/100). Its uniform_cumulant theorem combines that rate2/3 with
the full squared-marginal diagonal sum to prove the same rate2/3 for the
absolute exact second factorial cumulant, on all actual dyadic subgrounds.
The reused diagonal inequality is itself unconditional; no BCN hypothesis
is assumed in either new theorem. This provides the required boundedness
of the exact quadratic parameter independently of the final law approximation.

BoundedFixedMomentsUnderInputs.uniform_factorial combines the exact
quadratic factorial correction at a fixed positive error margin, the
second-cumulant decay and the unconditional actual mean cap to obtain a
constant uniform factorial-moment bound. uniform_ordinary applies the proved
finite power/falling-factorial inequality to obtain the corresponding
ordinary bound at every fixed r>=2. uniform_low handles r=0 and1 without any
geometric hypothesis, from the exact zero moment and actual mean cap.
No Poisson approximation theorem is used to prove moment boundedness.

This checkpoint adds6 modules,13 theorems and3 definitions/structures.
The all-order factorial-cumulant conclusion is still separate work. No new
literature property, axiom, original manuscript edit, dependency download,
Paper C port or Palomar registration is added.

Verified under Lean v4.36.0-rc2: full build passed (13577 jobs); direct axiom audit passed for 10445 declarations using only propext, Classical.choice and Quot.sound; all 8808 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 12.72 GiB.


## Completion of P1-MATH-0141 — All fixed moments and logarithmic cumulants at exponent1

Every scalar fixed-moment and higher-factorial-cumulant remainder
in main6.4 improves from N^(-4/5+epsilon) to N^(-1+epsilon) under the same
finite geometric properties. This includes exact actual parameters, the
optional nominal factorial reformulation, the genuine ordinary Poisson
Touchard correction and all actual logarithmic factorial cumulants of fixed
order>=3. All fixed ordinary moments are uniformly bounded independently
of the final law approximation. Actual-parameter statements hold on every
dyadic subground with heterogeneous marginals, zero marginals and affine
incompatibility included. The factorial proof uses the complete higher
centered activity rate1 and exact collision/deletion bounds with the full
diagonal correction. The ordinary correction follows by the exact Stirling
transform and actual second derivative of the Poisson Touchard polynomial.
The all-order cumulants are defined by the actual formal logarithm; its
moment recurrence is proved, and the exact quadratic-model residual is
second order in a. A finite induction combines the fixed moment errors
with a^2=O(N^(-4/3+epsilon)) to obtain all higher cumulants at rate1. The
finite order cutoffs, constants and geometric bundles all precede N.
No growing-order conclusion or later sharp4/3 remainder is asserted.


## Complete main Theorem6.4 at the stronger scalar exponent1

Main Theorem6.4 is now COMPLETE CONDITIONALLY under only the same three
explicit finite geometric properties. ALL literal conclusions are proved:
the exact actual-mean/full-second-cumulant factorial correction, its optional
nominal-mean/nominal-second-correction reformulation, uniform boundedness of
every fixed ordinary moment, the genuine Poisson Touchard second-derivative
ordinary correction, and every actual factorial cumulant of fixed order>=3.
ALL scalar remainders improve from exponent4/5 to exponent1. Finding141 is
extended to the complete theorem without incrementing the improvement count.
Unconditional coverage remains87/167; conditional results increase25 to26;
confirmed mathematical improvements remain141.

Every actual-parameter conclusion holds on every actual subground of the
full dyadic block, with exact heterogeneous marginals, zero marginals and
affine incompatibility included. The nominal reformulation concerns the
full original count, as in the source. Every order, finite collection of
geometric parameter bundles and fixed constant is selected before N. No
claim uniform in an order growing with N is made. Earlier BCN-dependent
auxiliary estimates are retained as historical preparatory declarations;
they are NOT inputs to this completion. Its only unproved mathematical
arguments are the chosen-source surface cover, ordinary surface cover and
normalized curve uniformity already recorded in the literature ledger.

The previously completed fixed factorial correction at exponent1 uses the
full higher centered activity and exact heterogeneous collision/deletion
bounds, retaining the squared-marginal diagonal term in the actual second
factorial cumulant. The completed ordinary correction transports the exact
Stirling identity to the actual count, identifies the genuine Poisson
Touchard polynomial and differentiates that polynomial twice. The proved
actual second-cumulant rate2/3 and actual mean cap give uniform boundedness
of all fixed factorial and ordinary moments without the final law
approximation; orders0 and1 are separately unconditional.

FormalFactorialCumulants supplies the missing ALL-ORDER definition and
algebra. Its cumulants are r! times coefficient r of the actual formal
logOf series, rather than a recursively named substitute. Substituting the
proved derivative of log(1+X) gives derivative(logOf f)*f=derivative(f) for
constant coefficient1. Extracting coefficients, multiplying by factorials
and proving the exact choose/factorial identity yields the complete
moment-cumulant recurrence. It proves the order0,1,2 formulas and the full
order3 and4 formulas. No logarithm, derivative or cumulant identity is
assumed as an external input.

AllFactorialCumulants constructs the actual factorial generating series
from E(Z_G)_r/r!. Its coefficient is proved equal to the actual r-subset
joint-mass sum, and its constant coefficient is proved1. The formal moments
recover the actual infinite-law factorial moments at every order. The
logarithmic cumulants have first coefficient equal to the actual mean and
second coefficient equal to the full actual second factorial cumulant.
Its third and fourth coefficients are proved exactly equal to the existing
complete heterogeneous third and fourth cumulants. The actual all-order
recurrence is transported from the formal logarithm theorem.

QuadraticMomentRecurrence isolates the first two cumulants in that recurrence.
The quadratic moment model has zero order3 residual. At every order n>=4
its exact residual is -(n-1)*choose(n-2,2)*mu^(n-4)*a^2. This identity is
proved algebraically, with all natural-index boundary cases. The module also
proves uniform finite moment envelopes and the residual bound on bounded
nonnegative means.

QuadraticCumulantBound.Data is FINITE ALGEBRAIC DATA, used only inside the
proof: exact mean and second cumulant, common quadratic moment error tau,
0<=tau<=1 and a^2<=tau. It is not an external geometric hypothesis. Its
proved step_bound controls the current cumulant by previous cumulants,
explicit finite moment envelopes and the quadratic residual. The exact
budget is nonnegative. FiniteCumulantControl proves by strong induction that
for each fixed r>=3 and mean cap M there is a constant B, chosen BEFORE the
series and tau, with |kappa_r|<=B*tau. All earlier-cumulant budgets and their
finite index ranges are proved; no higher cumulant bound is supplied as an
unproved premise.

FixedHigherCumulantsUnderInputs DISCHARGES EVERY FIELD of that finite data
for the actual count. It selects the finite geometric bundles for the
already proved factorial corrections at all orders up to r. With
 delta=min(epsilon/4,1/4), tau=N^(-1+delta),
the unconditional mean cap gives M, the proved second-cumulant rate2/3 gives
a^2<=N^(-4/3+delta)<=tau, and the full fixed factorial correction supplies
every moment error. Orders0 and1 are exact. A common threshold precedes all
actual subgrounds and lengths. The finite cumulant constant is absorbed to
give |kappa_r|<=N^(-1+epsilon) for every prescribed r>=3. The geometric
premises are precisely the existing FixedMomentInputs bundles at margin
delta and one finite pair bundle with source capsizeCap(1/100). No desired
moment, cumulant or activity estimate is an external argument.

NominalQuadraticFactorialMomentsUnderInputs proves the source's optional
nominal reformulation at the SAME improved rate1. The exact nominal second
correction differs from the actual second cumulant by mu^2-lambda^2. The
unconditional fixed power-mean bias bounds handle orders r,r-2 and2; the
proved actual second-cumulant decay makes the quadratic parameter bounded.
A fully proved finite parameter-change identity and fixed-factor absorption
then give the nominal factorial correction. The reused power-mean bias
lemma is itself unconditional even though its historical module also
contains separate BCN-dependent results. No BCN hypothesis enters this
proof.

This completion adds7 modules,37 theorems and9 definitions/structures, with
selected Mathlib formal-logarithm imports under the pinned compiler and
Mathlib commit. No new unproved literature property, axiom, dependency
download, original manuscript byte, Paper C port or Palomar action is added.
The sharper4/3 law and moment remainders later in the paper remain separate
work; the complete fixed-order Theorem6.4 is now proved at the stronger
intermediate power1 without using that later approximation.

Verified under Lean v4.36.0-rc2: full build passed (13599 jobs); direct axiom audit passed for 10482 declarations using only propext, Classical.choice and Quot.sound; all 8854 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 12.70 GiB.


## P1-MATH-0142 — Larger joint-plus-centered all-cardinality quantity

The all-cardinality connected bound in companion T16.1 extends to
the larger positive sum of u^|I|*(q(I)+|c(I)|), at the same improved exponent
min(1,2-eta), under the same finite geometric properties. The printed theorem
only bounds u^|I|*|c(I)|. The new joint bound uses the exact compatible-nullity
majorant q(I)<=prod(p_x)*2^rho_*(I), which includes incompatible systems with
q=0. Its sufficiently large cardinality sector has unconditional exponent
2-eta, and its fixed finite sector has the completed rate1. Exact
heterogeneous marginals, zero marginals, arbitrary actual dyadic subgrounds
and a common threshold over ALL cardinalities are retained. The new positive
quantity can control activation events directly; it is not obtained by
assuming a comparison of q with a possibly cancelling centered coefficient.


## Stronger joint-plus-absolute all-cardinality connected activity

Companion T16.1 is strengthened again: the SAME all-cardinality exponent
min(1,2-eta) now bounds the strictly larger actual joint-plus-absolute-
centered sum, not just the centered absolute activity. The result holds on
every actual dyadic subground for every connected family with at least three
members and compatible nullity<=eta*L. All cardinalities share one threshold.
Affine incompatibility and zero marginals remain included. The source's
0<=eta<2 decay regime is included; the inequality is also valid for eta>=2.
Finding P1-MATH-0142 records the larger quantity. Coverage stays87/167
unconditional and26 conditional; confirmed improvements increase141 to142.

CompatibleJointMajorant.pointwise proves the exact actual joint majorant
q(I)<=prod(p_x)*2^rho_*(I), with no cardinality-dependent factor. When q(I)>0,
the exact actual joint rank formula and equality rho_*=rho give the result.
When q(I)=0 the majorant is nonnegative. weighted_bound proves the finite
weighted sum version with the actual individual marginals and any proved
uniform compatible-rank amplification. No rank weight is silently
identified with an incompatible affine probability.

FixedConnectedJointWeightedUnderInputs proves weighted joint rate1 over
every prescribed finite order range3..R. Connectedness gives an actual
positive projection at every coordinate; hence no canonical component is
a singleton. The completed no-singleton joint catalog estimate then applies.
Its only hypotheses are the existing finite coarse geometric parameters,
at margin epsilon/8, selected before N.

ConnectedJointBoundedNullityTail gives the UNCONDITIONAL sufficiently large
cardinality joint tail at exponent2-eta. The actual compatible joint
majorant is multiplied by the completed original participating independent
weight tail, using exact weights u*p_x and their proved uniform marginal
cap. Each coordinate may have a different relation witness; no simultaneous
full-support binary relation or edge-independence assertion is assumed.
The cutoff is chosen before the threshold and all cardinalities are retained.

AllCardinalityConnectedJointUnderInputs.uniform_bound combines that tail
with the finite weighted joint range, yielding min(1,2-eta) at all actual
cardinalities, with one existing coarse bundle at margin epsilon/16.
AllCardinalityTotalActivityUnderInputs.uniform_bound combines it with the
already completed all-cardinality absolute centered bound. It proves the
larger sum of u^|I|*(q(I)+|c(I)|) at exponent min(1,2-eta). Final finite
geometric margins are epsilon/128 and epsilon/512 for the centered coarse
bundles, sizeCap(epsilon/524288) for their existing pair bundle, and
epsilon/32 for the joint coarse bundle. The finite union of these arguments
uses only the same three already recorded geometric properties.

This stronger positive quantity is useful for activation events and for
families obtained after compressing a dependent pair. Those applications
are still separate work, and the distinct separated compressed exponents
in T15.1 are not asserted here. This checkpoint adds5 modules and6 theorems.
No new unproved literature property, axiom, dependency download, original
manuscript edit, Paper C port or Palomar registration is added.

Verified under Lean v4.36.0-rc2: full build passed (13609 jobs); direct axiom audit passed for 10488 declarations using only propext, Classical.choice and Quot.sound; all 8860 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 12.67 GiB.


## P1-MATH-0143 — Whole compressed mass for every dependent pair

The whole unseparated compressed-pair estimate in T15.1 extends from
the two printed channels2:3 and3:4 to EVERY actual dependent source pair,
with the same literal exponent1 and all three actual mass terms. The source
pair remains distinguished and ALL target cardinalities share one threshold.
A primitive compressed extension is canonically connected as an original
family. Its source and compressed nullities are each at most L: either one
is at most2 and the total is at most L+2, or all original deletion losses
are at least3 and the union is a4-core below2L. The completed all-cardinality
original connected/core bounds handle these two cases. Actual source
multiplicity is at most2^|I| and is absorbed into the fixed size weight.
The additional compressed centered product term is bounded by the existing
all-pair independent deficit. This gives an alternative whole-clause proof
without a separate compressed saturation graph. Exact heterogeneous
marginals, affine incompatibility and zero marginals are included. The
separated exponents4/3 and5/4 are not proved or improved by this result.


## Whole compressed-pair mass at all cardinalities

The WHOLE, unseparated clause of companion T15.1 is now proved at its
literal exponent1 under only the same three existing finite geometric
properties. The proof actually covers EVERY actual dependent source pair,
not only pairs in channels2:3 and3:4. For every fixed u>0 and epsilon>0,
parameters are selected before their explicit geometric hypotheses, then
one threshold is selected before N,L, every actual dyadic subground G and
EVERY subpopulation of actual primitive compressed extensions. The sum is

  sum_(e,A) u^(|A|+2) [ q(e union A) + |compressed_c(e,A)| + |c(e union A)| ]
       <= N^(-1+epsilon).

The source pair remains distinguished in this sum. All cardinalities,
nonempty targets, heterogeneous actual marginals, affine incompatibility
and zero marginals are retained. The new finite theorem proves the
coefficient really is the expectation of the centered source INDICATOR
as one block times the centered individual target indicators. Its exact
primitive value is q(e union A)-q(e)*prod_(x in A) p_x, including incompatible
configurations. It is not a homogeneous rank weight treated as a joint
probability or a product of separately centered source endpoints.

PrimitiveCompressionCriterion.primitive_iff proves the exact equivalence
between primitiveness of the actual augmented effective-space family on
{none} union some(A), with EVERY proper subfamily direct, and the explicit
criterion: A is internally direct, relative compressed nullity is positive,
and every proper target subfamily has zero compressed nullity. The internal
directness clause accounts for deletion of the compressed source block.
PairPrimitiveCompression.primitive_iff_augmented specializes this equivalence.
The population also requires the actual source and target index sets disjoint.

RelationLossMonotonicity proves actual deletion-loss monotonicity by zero
extension of relation kernels and inclusion of their coordinate projection
ranges, without a finite-dimensional ambient-space assumption. For a source
pair, its deletion loss equals its nullity. For a target in a primitive
compressed extension, the deletion loss of the original union equals the
compressed nullity. Thus source nullity and compressed nullity are EACH
at most L. Canonical connectedness of the original union is proved: both
source endpoints must lie in one canonical block because their intersection
has positive dimension; any other block would be an internally dependent
subfamily of the internally direct target set.

The original union has the following exhaustive rank dichotomy. If either
source or compressed nullity is at most2, total actual nullity is at most
L+2. Otherwise every original coordinate has deletion loss at least3, so
the union is an actual4-core with total actual nullity at most2L.
ConnectedOneRankOffsetMassUnderInputs proves all-cardinality joint-plus-
absolute-centered mass rate1 below L+2 by the completed bounded-compatible-
nullity theorem with eta=1+epsilon/4. ConnectedFourCoreMassUnderInputs
proves the same rate for all connected4-cores below2L: its large-cardinality
rank tail has unconditional rate3/2 and its finite range has the completed
connected rate1. Neither sector assumes the desired compressed estimate.

DistinguishedPairWeights.fiber_card bounds the ACTUAL number of source
choices for any fixed original union by2^|I|; disjointness makes its target
set uniquely I minus the source. weighted_bound absorbs this multiplicity
by replacing u by2u, retaining every distinguished pair. The compressed
coefficient adds the product term q(e)*prod_A p_x. Each actual primitive
target belongs to the existing source-relative independent deficit family;
q(e)<=2|c(e)| for every dependent pair. Consequently the full source-product
mass is at most2*u^2 times the already completed all-pair deficit, of rate3/2.
The finite full-mass comparison is proved before the arithmetic estimates.

CompressedPairMassUnderInputs.Parameters and Hypotheses are finite bundles
of the SAME ordinary/source surface covers and normalized-curve bounds.
The low-rank coarse margins are epsilon/512, epsilon/2048, epsilon/128,
with pair cap sizeCap(epsilon/2097152). The4-core margins are epsilon/128,
epsilon/512, epsilon/32, with pair cap sizeCap(epsilon/524288). The initial
and finite-order deficit caps are sizeCap(epsilon/4096) and
sizeCap(epsilon/131072). All bundles are ordinary explicit theorem arguments;
no BCN or new unformalized property is introduced. Their finite union has
one threshold independent of the actual ground set, subpopulation and size.

Finding P1-MATH-0143 records the broader all-dependent-pair domain and the
alternative proof of the whole clause. The SEPARATED exponents4/3 and5/4
in the first clause of T15.1 remain open. Therefore T15.1 changes only from
not_started to in_progress; it is NOT counted as a conditional completion.
The homogeneous rank-weight pair-target estimates in T1.12(ii) also remain
open. This checkpoint adds9 modules,36 theorems,6 definitions and2 finite
parameter structures. Coverage remains87/167 unconditional and26 conditional;
confirmed improvements increase142 to143. No original source byte, Paper C
port, dependency download, hidden axiom or Palomar registration is added.

Verified under Lean v4.36.0-rc2: full build passed (13627 jobs); direct axiom audit passed for 10524 declarations using only propext, Classical.choice and Quot.sound; all 8904 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 12.63 GiB.


## P1-MATH-0144 — Exact retained event from four positive seed classes

The exceptional-event conclusion in companion T15.2 admits a shorter
exhaustive positive-seed proof. Every nonretained actual family contains a
nongood dependent pair, an original primitive of size at least3, two disjoint
dependent pairs, or a primitive compressed extension. For two disjoint pairs,
positive deletion loss at every coordinate and the completed fixed
no-singleton joint theorem give rate1 without the sharper separated
homogeneous two-pair bound. The whole compressed-pair rate1 suffices; its
still-open sharp separated clauses are unnecessary here. No separate
contact exclusion is needed for the retained direct-sum conclusion. All
other seed contributions have rate1; the actual nongood pair tail supplies
the final rate4/5. The measurable event is exactly nonretention, and every
actual subfamily off it has rho<=L/3+1. This event also proves the same
quantitative rate4/5 in total variation between the actual normalized
original and retained-modified count laws, improving the earlier Lean
qualitative BCN-based preparation. All actual dyadic subgrounds, affine
incompatibility, zero marginals and all cardinalities are included. The
conditional input scope is only the three existing geometric properties.


## Complete actual retained exceptional event, companion T15.2

Companion T15.2 is now COMPLETE CONDITIONALLY, with its literal actual
measurable exceptional event of probability at most N^(-4/5+epsilon), its
actual direct sum of singletons and at most one compressed good-pair space,
and the explicit bound rho(I)<=L/3+1 for EVERY active subfamily I outside
the event. The same event also gives actual original/modified law total
variation at most N^(-4/5+epsilon). Parameters are chosen before the existing
geometric hypotheses, then one threshold before N,L and EVERY actual dyadic
subground G. The retained good-pair threshold is explicitly H=8*(L+1).
The retained count is the actual count off the event and zero on the event;
its law and the original law are actual normalized probability measures.

NongoodPairSeeds proves that the finite compatible private good partition
at channel cutoff Q=4 is contained in the actual retained goodEdges class.
Only its two possible channels2:3 and3:4 occur; the exact source order and
positive effective pair intersection are proved from the actual pair data.
Every dependent nongood pair therefore belongs to the height-five weak tail
or the finite exceptional class. DependentPairJointActivity gives q(e)<=2|c(e)|
without assuming affine compatibility or positive marginals. The completed
height-five aligned tail has rate4/5 and the existing finite exceptional
class has rate1. NongoodPairJointMassUnderInputs.uniform_bound proves the
whole POSITIVE joint nongood seed sum at the literal rate4/5, uniformly on
all actual dyadic subgrounds, under one existing finite pair bundle with
cap sizeCap(epsilon/128). No desired exceptional-event estimate is assumed.

TwoDependentPairSeeds proves that the union of ANY two disjoint actual
dependent pairs has exactly4 members and every coordinate has positive
deletion loss, by the proved loss monotonicity. It therefore has no
singleton canonical component. The completed fixed no-singleton joint
bound gives its entire actual joint seed sum rate1. This includes
unseparated pairs and arbitrary intersections of their effective spaces;
it does not assume the sharper separated homogeneous two-pair theorem.

RetainedActivationSeeds.cover proves an EXHAUSTIVE finite cover of every
nonretained family at EVERY cardinality by just four positive seed types:
(1) a dependent nongood pair; (2) an original primitive family of at least
three sites; (3) two disjoint dependent pairs; or (4) an actual primitive
compressed extension of a distinguished dependent pair. Extract a minimal
original dependence. A good pair e can be compressed. If the whole family
is not retained, some minimal target set A has positive compressed nullity.
If A is internally direct, it is exactly a primitive compressed extension.
Otherwise extract an original primitive inside A: it either has at least
three sites or is a dependent pair disjoint from e. This dichotomy closes
the finite proof without dropping nonpositive or incompatible configurations.
Each selected seed is proved contained in the original actual ground set.

The exact original-model event of nonretention is contained in activation
of this finite seed family. Actual measure monotonicity and the proved
finite-cylinder activation bound give its probability at most the positive
joint seed sum. Repeated seeds are handled by nonnegative finite union
bounds. The compressed image sum is bounded by the completed three-term
compressed mass with the distinguished pair retained, at fixed weight1.
The all-cardinality original primitive rate1 is passed from its actual
rank majorant, including zero marginals, with no regular-ground restriction.
The four positive estimates share one threshold, giving rate4/5. A separate
contact exclusion is not needed for the stated retained direct-sum conclusion.

RetainedExceptionalEventUnderInputs.companion_T15_2 sets E to the literal
nonretention event. Its measurability is proved via the existing actual
finite-cylinder realization. Outside E, the conclusion is explicitly the
injectivity of the singleton-space addition map OR a retained good pair
e and injectivity of the compressed-space addition map. The existing
retained-subfamily theorem supplies rho(I)<=L/3+1 for every active I.
uniform_totalVariation uses the already proved actual coupling; no retained
signed reference is called a probability law.

RetainedExceptionalEventUnderInputs.Parameters is a finite combination of
the completed compressed-pair parameters, one nongood pair bundle, one
order4 coarse bundle and finitely many original primitive bundles. Its
Hypotheses use nongood cap sizeCap(epsilon/256), order4 margin epsilon/8,
compressed hypotheses at epsilon/2 and the same original primitive inputs.
Only the SAME three recorded geometric properties are ordinary explicit
arguments. No BCN plane estimate or additional unformalized property enters
the completed proof. Earlier BCN qualitative preparations remain historical
declarations; their weak convergence estimate is not used for this rate.

Finding P1-MATH-0144 records the simpler exhaustive positive-seed route,
which uses neither a separate contact exclusion nor the still-open sharp
separated homogeneous estimates, together with the actual quantitative
law-coupling consequence. T15.1 remains in progress because its separated
exponents4/3 and5/4 are open; T1.12(ii)/(iii) homogeneous rank-weight clauses
also remain open. This checkpoint adds6 modules,18 theorems,4 definitions
and2 finite parameter structures. Coverage is87/167 unconditional and27
conditional, with144 confirmed mathematical improvements. No original
manuscript bytes, Paper C port, dependency download, hidden axiom or Palomar
registration is added.

Verified under Lean v4.36.0-rc2: full build passed (13639 jobs); direct axiom audit passed for 10542 declarations using only propext, Classical.choice and Quot.sound; all 8928 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 12.59 GiB.


## Complete modified count and every-order bounds, companion T19.3

Companion T19.3 is now COMPLETE CONDITIONALLY, including restoration
from the actual regular-ground count to the full original dyadic count.
The modified count is constructed on the SAME original infinite prime-sign
space: it equals the regular-ground count when its active configuration is
retained at threshold H=8*(L+1), and zero on the actual nonretention event.
The original and modified laws are actual normalized probability measures,
identified with the pushforwards of those random variables.

ModifiedCountAllTailsUnderInputs.companion_T19_3 selects its finite geometric
parameters before their ordinary hypotheses, and ONE threshold before N,L
and EVERY natural tail order k>=1, factorial order r>=1 and real s>=1.
For the actual regular ground G, n=|G|, p=2^(-L) and mu=n*p, it gives ALL
of the source conclusions together:

  TV(Law(full original count),Law(modified regular count))<=N^(-4/5+epsilon),
  delta=P(actual nonretention on G)<=N^(-4/5+epsilon),
  P(regular count>=k)<=mu^(k-1)/(k-1)!+delta,
  P(modified count>=k)<=mu^(k-1)/(k-1)!,
  E s^modified<=s*(1+p*(s-1))^n,
  E s^modified<=s*exp((s-1)*mu),
  E(modified)_r<=mu^r+r*mu^(r-1).

The all-order inequalities themselves were already proved UNCONDITIONALLY
for the actual direct maximum R and shifted envelope R+1, followed by the
pointwise domination modified<=R+1. Their tail probabilities, finite-cylinder
realizations, observable integrability, binomial subset counts and full
nonnegative subset generator are all actual checked theorems. No fixed-order
asymptotic constant is reused at growing order. The exact falling-factorial
shift retains its repeated-index term r*mu^(r-1). Zero means, empty grounds
and orders beyond the ground size are included by those finite results.

OriginalCountLawCoupling.finite_law proves invariance of the actual count
law under every sufficiently large finite observation cutoff. A common
finite cylinder therefore proves the coupling of actual count laws on
arbitrary finite grounds by their actual disagreement probability.
restore_modified composes this with the actual retained-modification
coupling. The existing unconditional regular-ground restoration error is
O_C(N^(-1+epsilon/2)), while the newly completed literal exceptional event
has exponent4/5. Their sum is absorbed uniformly into N^(-4/5+epsilon).
Thus the TV conclusion is for the FULL original count, rather than only
the already regularized count.

The same earlier heterogeneous envelope statements remain valid on ANY
actual finite ground: replace p^|I| by the product of exact p_x, mu by
sum p_x and the binomial generator by product(1+(s-1)*p_x). In particular,
local affine incompatibility and zero marginals were handled explicitly.
The source regular-ground formulas are obtained by the proved exact
regular marginal identity. No exponential estimate for the full original
count on the exceptional event is asserted; the exponential and factorial
tails here concern the constructed modified variable.

The only unproved inputs for the numerical4/5 coupling rate are the same
three finite geometric properties used in the completed T15.2. They occur
as RetainedExceptionalEventUnderInputs.Hypotheses at epsilon/2. No BCN
plane bound or new unformalized property occurs in the completed proof.
Earlier qualitative BCN preparations remain historical declarations; the
new theorem supplies the literal rate and every-order quantifier order.
No new mathematical finding is added: this completes the missing event
and original-law restoration clauses of the existing T19.3 development.
The existing improvement88 in its ledger remains recorded with its
original validation history.

This checkpoint adds2 modules and5 theorems, with no new definitions or
inputs. Coverage is87/167 unconditional and28 conditional, with144 confirmed
improvements. T15.1 sharp separated clauses and the optimal quadratic-law
rates remain open. No original manuscript bytes, Paper C port, dependency
download, hidden axiom or Palomar registration is added.

Verified under Lean v4.36.0-rc2: full build passed (13643 jobs); direct axiom audit passed for 10547 declarations using only propext, Classical.choice and Quot.sound; all 8933 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 12.57 GiB.


## P1-MATH-0145 — Heterogeneous finite boundary comparison for every cutoff

The finite positive-boundary comparison in companion T17.3 holds
without the printed linear size restriction K<=L/4 and extends to arbitrary
finite actual grounds with unequal exact marginals. For any fixed u>=0 and
any population of positive-joint source pairs, its three terms are the
literal ordinary independent deficit, the distinguished source-relative
independent deficits, and exp(sum_x u*p_x) times a canonical-component
remainder with the empty collection and one source pair explicitly
subtracted. Actual finite source/complement injections and canonical union
recovery prove the comparison. In the printed regular case u=2 this is
exactly R_K<=F+Gdef+exp(2mu)(exp(A_good+A_bad+B_K)-1-A_good), for EVERY K.
Only the subsequent uniform arithmetic estimate uses4K<=L. Incompatibility,
zero marginals and failed extensions remain present. Separating this
unconditional finite theorem from the arithmetic cutoff clarifies precisely
where each hypothesis is needed and supplies a heterogeneous version.


## Complete positive mass outside the retained class, companion T17.3

Companion T17.3 is now COMPLETE CONDITIONALLY, including BOTH its exact
finite positive-boundary inequality and its uniform rate4/5 over the literal
linear range4K<=L. For H=8*(L+1), G=regularStarts(N,L), mu=E Z_G and the
literal actual nonretained low-nullity sum R_K, the checked statements are

  R_K <= F + Gdef + exp(2mu) * [ exp(A_good+A_bad+B_K)-1-A_good ],
  R_K <= N^(-4/5+epsilon), uniformly over every4K<=L.

F and Gdef are the previously constructed literal independent deficits,
with their exact cardinality grouping. A_good=4 sum_good c(e),
A_bad=4 sum_(all regular nongood pairs) |c(e)|, and B_K is the actual
weighted connected centered sum at sizes3..K with compatible nullity<=3L/2.
The finite family defining R_K is EXACTLY the actual subsets I of G with
rho(I)<=3L/2, I nonretained and |I|<=K. The original source's added terms
B/N and a_N^2 are absorbed by the proved uniform N^epsilon slack; the final
rate is therefore stated in the stronger unit-power form without those
additional nonnegative terms.

FinitePolymerRemainder proves an exact finite subset-generator remainder:
remove the empty component collection and exactly one distinguished good
component BEFORE the exponential majorant. Actual union-recoverable
component collections inject into the remaining powerset, so arbitrary
nonnegative component activities have bound exp(sum_all)-1-sum_good.
The exponential Taylor remainder is proved separately, with its explicit
quadratic budget. No independence of canonical components as random
choices, partition count heuristic, or target remainder is assumed.

CanonicalComponentWeights proves actual canonical blocks pairwise disjoint,
their cardinalities sum to |I|, and the EXACT weighted factorization
u^|I|*|c(I)|=product_C(u^|C|*|c(C)|). ActualComponentRemainder handles zero
coefficients by an exact finite filter. Nonzero coefficients have no
singleton canonical part. Every remaining part is connected, has at least
two sites, and inherits its actual nullity cap by monotonicity. Thus the
component remainder includes affine incompatibility and zero marginals;
no cancelling centered expression is replaced by a joint probability.

CenteredSourcePairBound proves 0<=c(e) and |c(e)|<=q(e) for every actual
positive-joint source pair, from the exact heterogeneous joint rank formula
and the pair covariance identity. NonretainedPositiveMass.pointwise_bound
uses the exact inverse centering expansion and separates the empty term,
source-pair terms and residual terms. Source pairs remain distinguished.
For a nonretained I and a source e subset I, the complement I minus e is
PROVED to fail directness after compression; otherwise I would be retained.
RestrictedSeedComplements.fiber_bound therefore charges that source term
to its actual source-relative independent deficit. No factorization of a
failed extension's arithmetic joint probability is assumed.

SeedComplementSum bounds the sum of EVERY contained residual seed, with
its own nonnegative centered activity and independently weighted free
complement. The exact complement map is injective in each source fiber;
its full finite generator is bounded by exp(sum_x u*p_x). Independent
nonretained terms belong to the actual ordinary independent deficit.
NonretainedPositiveMass.finite_bound combines these comparisons with the
nonlinear actual canonical-component remainder on ANY finite actual ground
G, with exact heterogeneous marginals, ANY fixed u>=0 and ANY size cap K.
Source pairs only need positive actual joint probability and membership
in G.powersetCard2. No equal-marginal assumption, regularity premise or
linear size restriction is used in this finite theorem.

RetainedBoundaryPositiveMass.finite_bound specializes this stronger finite
lemma to the actual regular ground, goodEdges and u=2. Exact marginal
identities identify F and Gdef with firstMass and secondMass; the exact
pair split identifies A_good+A_bad. It proves the source finite inequality
for EVERY K, even when4K>L. The linear restriction is needed only by the
arithmetic rate estimates, not by the finite probability/combinatorics.
Finding P1-MATH-0145 records this separation and heterogeneous extension.

RetainedBadPairActivityUnderInputs keeps every nongood centered pair,
including incompatible sources. Direct nongood pairs have zero coefficient;
the actual dependent ones lie in the height-five tail or finite exceptional
sector at Q=4. Their rates4/5 and1 give A_bad rate4/5. The only input is the
existing finite pair bundle at cap sizeCap(epsilon/128).
RetainedComponentActivityUnderInputs supplies ONE common threshold over
ALL4K<=L: A_bad has rate4/5, B_K rate1, A_good+A_bad rate2/3. B_K uses the
completed literal linear connected theorem at t=4, eta=3/2 and weight2;
the whole pair rate uses the existing fixed-cap pair bundle. These are
proved constituent estimates, not desired-bound premises.

PositiveBoundaryMassUnderInputs uses the fixed internal margin
delta=min(epsilon/4,1/12), selected before N. The total component activity
is at most2*N^(-7/12), hence eventually at most1. Its squared exponential
remainder costs N^(-7/6), while A_bad supplies rate4/5 and B_K rate1.
The actual mean is bounded uniformly; the already completed independent
deficits have stronger rates1 and7/6. A final fixed-factor absorption gives
the literal4/5 rate after one threshold, uniformly in K and L.
The final Hypotheses are a finite union of the SAME three previously
recorded geometric properties: three coarse bundles at margins delta/128,
delta/512, delta/128; their pair caps sizeCap(delta/524288) and
sizeCap(delta/1024); the whole-pair cap sizeCap(1/100); and the nongood-pair
cap sizeCap(delta/128). No BCN or new unproved property is introduced.

This checkpoint adds10 modules,27 theorems,10 definitions and2 finite
parameter structures. Coverage is87/167 unconditional and29 conditional,
with145 confirmed mathematical improvements. The complete-law quadratic
approximation still requires combining this result with the stopped
identity, large-boundary tail and reference conversion; no such completion
is claimed here. The sharp4/3 complete-law rate and T15.1 separated clauses
remain open. No original manuscript bytes, Paper C port, dependency download,
hidden axiom or Palomar registration is added.

Verified under Lean v4.36.0-rc2: full build passed (13663 jobs); direct axiom audit passed for 10574 declarations using only propext, Classical.choice and Quot.sound; all 8972 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 12.53 GiB.


## P1-MATH-0146 — Unconditional second-cumulant and quadratic-reference restoration

The second factorial cumulant transfer needed to restore irregular
windows can be proved unconditionally with rate N^(-1+epsilon), without
the bounded higher-moment premise in the earlier regular-set argument.
For H subset G, the exact removed unordered pairs are precisely those
in G touching G minus H. The cumulant identity gives an error bounded by
twice their absolute centered activity plus the full marginal diagonal.
The established unconditional irregular-pair activity and marginal cap
bound these terms with rate1. Together with the exact mean gap and an
unconditional subpower cumulant envelope, this proves rate1 for the sum
of actual-law restoration and quadratic-reference restoration, both for
the full actual mean and for N*2^(-L), with the SAME full actual cumulant.
This removes auxiliary moment and BCN premises from this specific
second-order restoration step; it does not prove unconditional bounds for
all higher-order moment transfers or the complete law approximation.


## Complete first quadratic approximation, companion T17.5

Companion T17.5 is COMPLETE CONDITIONALLY, with BOTH original-law quadratic
approximations in ordinary singleton l1 distance. For every C and epsilon>0,
the finite geometric parameters are chosen first; given their explicit
ordinary hypotheses there is ONE threshold before all N and all critical L:

  distance(Law Z_N, Q(mu_N,alpha_N)) <= N^(-4/5+epsilon),
  distance(Law Z_N, Q(N*2^(-L),alpha_N)) <= N^(-4/5+epsilon).

Law Z_N is the actual normalized pushforward of the original infinite
prime-sign count. alpha_N is its exact second factorial cumulant in BOTH
references. Q is the already constructed actual signed Poisson--Charlier
measure, with its literal singleton coefficients. The new signed atomic
distance is the convergent sum of absolute singleton differences; for two
probability measures it is exactly twice actual total variation. No
probability interpretation of a retained polynomial is assumed.

RetainedStoppedLaw transports the exact finite stopped identity to the
actual original regular-count law using a cutoff containing all windows.
Its boundary is split by actual cardinality into the exact low-nullity
nonretained mass and the large-boundary mass. The finite comparison needs
only N>=2,L>=7, with no arithmetic rate premise. Adding the two actual
independent deficits gives the actual binomial pair reference. The cutoff
chosen by BoundaryCutoff satisfies4K<=L eventually. The completed T17.3
bound has rate4/5, the improved unconditional large-boundary tail has
rate5/3, and the two independent deficits have stronger rates1 and7/6.
Their proved combination yields the original regular law's rate4/5 to
the binomial pair reference.

RetainedBetaCovarianceUnderInputs proves the finite parameter identity
and estimate before taking rates: beta minus the covariance of ALL actual
regular pairs is bounded by the independent product mass of good pairs
plus A_bad/4. The good-pair independent mass has unconditional rate1 via
the literal private2:3 and3:4 channels. All nongood pairs, including
incompatible ones, are kept in A_bad, whose established rate is4/5.
PoissonCharlierConversion then converts the actual binomial reference to
the quadratic reference at the exact regular mean and cumulant. Its
analytic error has size N^-2+|C2|/N; unconditional subpower absolute pair
activity makes this error smaller than the requested4/5 budget. The
quadratic coefficient retains the diagonal subtraction -n*p^2.

RegularSecondCumulantRestoration proves UNCONDITIONALLY that removing the
irregular windows changes the actual second factorial cumulant by at most
N^(-1+epsilon). A finite identity identifies the removed pairs with the
actual edges touching the removed ground, and bounds the correction by
twice their absolute centered activity plus the marginal diagonal.
IrregularPairActivity already bounds the first term with rate1, and the
actual marginal cap gives diagonal O_C(1/N). No bounded higher-moment
premise, BCN premise or geometric input occurs in this theorem. This
replaces the earlier bounded-moment route for this particular transfer;
other higher-order moment transfers are not declared unconditional.
Finding P1-MATH-0146 records the improvement.

RegularQuadraticReferenceRestoration combines this unconditional cumulant
transfer with the exact mean gap, the proved nominal mean bias and the
actual original-law coupling. Its generic signed-reference parameter
bound uses the existing Poisson parameter stability theorem. The actual
cumulant has an unconditional subpower envelope. Choosing internal
margins before N proves that law restoration PLUS reference restoration
has rate1, for BOTH the full actual mean and the nominal mean. Thus the
last step of T17.5 introduces no extra arithmetic input and preserves the
full actual alpha_N in the nominal reference.

The only unproved inputs in T17.5 are a finite union of the SAME three
recorded geometric counting properties: normalized-curve uniformity,
ordinary surface cover and chosen-source surface cover. Parameters consist
of the existing retained-component bundle and finite-pair bundle. At
internal margin d=epsilon/2, the first is used at min(d/24,1/12), and the
second at sizeCap(d/768). Their definitions expose the further finite
constituent margins. No desired law bound, BCN bound or moment bound is
an input. All thresholds precede every critical length; no limiting mean
or phase is fixed.

This checkpoint adds7 modules,25 theorems,1 definition and2 finite parameter
structures. Coverage is87/167 unconditional and30 conditional, with146
confirmed mathematical improvements. Main3.1 keeps its proved scope and
gains the unconditional second-cumulant restoration; main1.1 gains the
conditional4/5 quadratic approximation and stays in progress because its
optimal4/3 rate is still open. No source bytes, dependencies, Paper C port,
new hidden axiom or Palomar registration are added.

Verified under Lean v4.36.0-rc2: full build passed (13677 jobs); direct axiom audit passed for 10599 declarations using only propext, Classical.choice and Quot.sound; all 9000 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 12.49 GiB.


## Exact finite all-pair reconstruction toward main15.13

Main15.13 is now IN PROGRESS with its unconditional exact finite
reconstruction and unconditional large-boundary tail. Its complete
implication from the254 fixed connected-activity estimates is NOT yet
claimed. This checkpoint does not add a completed numbered result.

The literal all-pair class D2 on ANY finite actual ground G is constructed:
I is retained when its original square-class spaces are direct, or its
nullity equals that of one contained pair. Every pair of G is allowed,
including incompatible pairs and pairs with zero covariance. Heredity,
empty-set membership and retention of every pair are proved. For a
positive dyadic ground, every first excluded prefix has positive nullity
at most2L, and every subfamily has compatible nullity at most2L.
This is the full2L boundary, not the smaller good-pair boundary from T17.5.

UnrestrictedRetainedExpansion proves the exact inverse-centering expansion
on this class:

  q(I) = product_I p_x + sum_(e subset I, |e|=2) c(e)*product_(I minus e) p_x.

No positivity or compatibility premise is imposed. If a marginal is zero,
the actual centered coefficient vanishes by the already proved zero-mass
argument. Otherwise the full-support relation criterion proves that all
centered coefficients of size at least3 vanish on a retained family.
A primitive original family has c(I)=q(I)-product_I p_x, including the
incompatible case q(I)=0, and product_I p_x<=|c(I)|. Canonical nullity
additivity separately proves that every primitive family is connected;
its compatible nullity is at mostL on the positive dyadic ground.

AllPairPolynomialExpansion proves an exact finite commutative-ring
identity, retaining EVERY signed pair weight. Specialization identifies
the all-pair reference with the full heterogeneous Bernoulli product plus
its signed covariance corrections. SecondOrderRetainedReference proves
that its difference from the actual D2 retained polynomial is precisely
the negative discarded sum of the independent and signed pair terms.
In particular, no incompatible covariance is replaced by a joint event
probability and no equal-marginal reduction is used.

SecondOrderIndependentDeficit charges the independent mass of discarded
families to primitive sources of size at least3 and failed extensions of
a contained pair. For the latter, nonretention itself proves failure of
directness after compression. The exact complement map is injective in
every source fiber. Arbitrary u>=0, arbitrary finite source ground and all
cardinalities are covered; the primitive independent weight is bounded by
its actual centered activity even for incompatible systems.
SecondOrderPositiveMass removes the empty coefficient and the ENTIRE
one-pair contribution before applying the actual canonical-component
generator. The resulting finite probability bound holds for EVERY K.

SecondOrderStoppedLaw.finite_bound is an unconditional bound for the
actual ORIGINAL normalized count law, at any positive dyadic ground,
L>0 and arbitrary K. Write A=sum_pairs 4|c(e)|, T=sum_(connected C,
3<=|C|<=K,compatible-nullity<=2L) 2^|C|*|c(C)|, P=sum_(primitive D,
|D|>=3)2^|D|*|c(D)|, D=the literal all-pair failed-extension deficit
at weight2, and M=sum_x2p_x. Then its exact checked bound is

  distance(Law Z_G, embed B2) <=
    2 exp(M)*P +16 D + exp(M)*(exp(A+T)-1-A) +largeBoundaryMass.

All quantities on the right are explicitly defined finite actual sums.
The original law is transported through an actual containing finite
cylinder and the exact stopped expansion, whose suffix remains positive.
No eventwise polynomial is treated as a probability law.

SecondOrderBoundaryCutoff evaluates the already defined least cutoff at
N^2. It is PROVED to be o(log N), and the log-budget tail is then N^-6.
The literal2L boundary costs O_C(N^2), giving the unconditional final
large-boundary bound2^(2C)*N^-4, uniformly for all G in the dyadic block.
All irregular windows, exact heterogeneous marginals, zero masses and
incompatible systems are retained. No growing-order moment premise is
used for this tail.

This checkpoint adds9 modules,36 theorems and10 definitions. Coverage
remains87/167 unconditional and30 conditional; confirmed mathematical
improvements remain146. These are exact proof constructions and do not
receive a new correction identifier. The next step is to insert the
source254 fixed connected-activity hypotheses, combine the proved tails,
pair activity and pair deficits, and perform the existing sharp analytic
conversion. Main15.13 stays in progress until that implication is checked.
No dependency download, source-byte change, Paper C port, hidden axiom
or Palomar registration is introduced.

Verified under Lean v4.36.0-rc2: full build passed (13695 jobs); direct axiom audit passed for 10635 declarations using only propext, Classical.choice and Quot.sound; all 9046 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 12.44 GiB.


## Complete finite transfer to the full law, main15.13

Main15.13 is now COMPLETE CONDITIONALLY as the literal theorem stated in
the source: for1<beta<=4/3, the254 fixed connected-activity estimates at
orders3 through256 imply the complete original-law quadratic estimate
with rate N^(-beta+epsilon). The same three previously recorded geometric
counting properties remain explicit ordinary arguments for the already
proved all-pair deficit, pair activity and connected tail. No new
geometric counting property is introduced.

The SOURCE FIXED-ORDER ASSUMPTION is explicit and has not been discharged:
FiniteConnectedActivity254.Hypothesis C beta quantifies ONLY r=3,...,256.
For every such r and every positive accuracy it supplies a nonnegative
constant A_r and a threshold before all critical N,L, bounding the sum
of |c(I)| over ALL actual connected r-site families with compatible
nullity<=2L by A_r*N^(-beta+accuracy). The constants may depend on r,C
and accuracy, exactly as in the printed big-O hypothesis. It assumes
neither the desired law bound nor a growing-order activity bound.
This completion proves the stated implication; it is NOT recorded as a
proof of those254 activity estimates, main15.10, main15.14 or main1.1.

FiniteConnectedActivity254.uniform_weighted chooses the254 constants
and thresholds before N using a finite index type. Exact cardinality
filters cover every family of size3..256, and finite fixed weights are
absorbed with a smaller accuracy. There is then ONE threshold for the
entire finite range. PrimitiveConnectedGeometry proves that primitive
original families are connected and have compatible nullity<=L, so the
same hypotheses control primitive sizes3..256. The already proved
unconditional primitive tail supplies all larger sizes with power7/5.
The complete primitive sum consequently has rate beta.

FiniteConnectedClosureUnderInputs combines the exact small-size estimate
with ConnectedTailUnderInputs at the literal cutoff from
SecondOrderBoundaryCutoff. The latter cutoff is proved o(log N). The
connected tail at sizesSTRICTLY GREATER THAN256 has power83/60, which is
strictly stronger than4/3. Every actual connected family of size3..K
and compatible nullity<=2L is retained, including incompatible systems.
Both the complete connected sum and all-cardinality primitive sum have
rate beta after one threshold, uniformly over every G in the full dyadic
ground. No unproved estimate at sizes>256 is added to the hypothesis.

The previous unconditional finite reconstruction theorem remains the
probabilistic mechanism. D2 contains direct original families and families
with exactly the nullity of a contained pair; ALL original pairs are
allowed. Its boundary has nullity<=2L. On D2, inverse centering is exactly
q(I)=product_I p_x+sum_pairs c(e)*product_complement p_x. The retained
polynomial differs from the full heterogeneous Bernoulli-plus-signed-pair
reference by the explicit discarded independent and pair terms. Failed
pair complements are proved non-direct after source compression. The
finite bound uses actual primitive centered mass, the actual all-pair
extension deficit, and exp(A2+T)-1-A2, with the whole linear pair activity
subtracted BEFORE the absolute component estimate. It holds for every K
and exact heterogeneous marginals, including zeros and incompatibility.

FiniteCompleteLawTransferUnderInputs uses a fixed internal accuracy
delta=min(epsilon/8,1/24). Absolute pair activity has rate2/3, the complete
connected remainder has rate beta>1, the all-pair independent deficit has
rate3/2, and the actual large-boundary mass has unconditional rate4.
The total component activity x is at most5*N^(-2/3+delta), hence eventually
at most1. The proved exponential remainder costs T+x^2*exp(x)/2. Its
squared pair term has rate4/3, so beta<=4/3 is exactly sufficient.
A uniformly bounded actual mean controls all free complements. Finally
the already proved signed heterogeneous Poisson--Charlier conversion
has rate5/3 and uses the EXACT actual mean and second factorial cumulant,
including the marginal diagonal. Fixed constants are absorbed before
taking the final threshold.

Parameters are a finite connected-tail bundle, a finite all-pair-deficit
bundle, and two finite-pair bundles for activity and conversion. At the
chosen delta, connected hypotheses use coarse margin delta/128 and
pair caps sizeCap(delta/32768), sizeCap(delta/1048576). The all-pair-deficit
hypotheses use caps sizeCap(delta/2048), sizeCap(delta/65536). Pair activity
and conversion use sizeCap(1/100). The underlying bundle definitions
expose every constituent ordinary surface cover, chosen-source surface
cover and normalized-curve bound. No BCN or bounded-moment assumption
occurs. All parameters, constants and fixed orders precede N; the final
threshold precedes ALL critical lengths and ALL dyadic subgrounds.

article_15_13 specializes the stronger subground theorem to the original
full count law. The source-count law is an actual normalized pushforward,
and the reference is the actual signed Poisson--Charlier measure; distance
is the convergent ordinary sum of absolute singleton differences. The
finite suffix count remains an actual positive kernel, never a freely
expanded signed approximation to a probability.

This completion adds3 modules,5 theorems,2 definitions and4 finite
parameter structures. Coverage is87/167 unconditional and31 conditional;
confirmed mathematical improvements remain146. This is completion of
the source implication and introduces no new correction identifier.
The optimal4/3 activity inputs and main15.14 reconstruction still require
their own proofs. No dependency download, original source-byte change,
Paper C port, hidden axiom or Palomar registration is introduced.

Verified under Lean v4.36.0-rc2: full build passed (13701 jobs); direct axiom audit passed for 10640 declarations using only propext, Classical.choice and Quot.sound; all 9057 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 12.42 GiB.


## P1-MATH-0147 — Subpower moments suffice for complete weighted pair leakage

The pair-leakage argument in companion T22.6 does not need uniformly
bounded fixed moments. The unconditional subpower bounds for every fixed
ordinary moment suffice. A finite Holder estimate with exponents1/8 and7/8,
using the existing exceptional probability at fixed margin1/120, bounds
ANY nonnegative active-set observable f(A)<=|A|^j by N^(-83/120) on the
exceptional event. The SAME finite geometric input bundle is chosen before
ALL fixed degrees j and before the final relative tolerance. The actual
pair count is polynomially bounded, so each H_r has this rate. An
unconditional4^r generator bound and an unconditional positive lower bound
for the actual correction scale then prove the complete2^r-weighted
little-o estimate by a fixed-cutoff argument. This removes BCN and
order-dependent bounded-moment geometry from this proof route. It does
not claim a stronger fixed-order exponent than the printed7/10; the
weaker83/120 already exceeds2/3 and proves the complete source claim.


## Complete modified moments and pair leakage, companion T22.6

Companion T22.6 is COMPLETE CONDITIONALLY, including its exact modified
binomial-moment identity, nonnegativity of all four deficits, the zero
pair terms at order1, and BOTH weighted estimates. Let n=|regularStarts|,
p=2^-L and beta=sum_good q(e). With the literal actual modified count and
the actual exceptional event E'=nonretention, for every r>=1:

  E choose(modified Z,r) = choose(n,r)*p^r -F_r -L'_r
    +beta*choose(n-2,r-2)*p^(r-2) -G_r -H_r,

where the last three terms are zero for r=1. F_r and G_r are exactly the
previous cardinality coefficients; L'_r and H_r are the actual Bochner
expectations, restricted to E', of the direct and compressed-pair subset
counts. All four are proved nonnegative. The finite identity is
UNCONDITIONAL for N>=2,L>0 and EVERY r>=1, with no upper order restriction.

RetainedSubsetCounts constructs the literal deterministic direct and
compressed-family counts. On ANY retained configuration their sum is
choose(|A|,r), by the already proved disjoint direct/pair decomposition.
Every source pair remains distinguished. RetainedPairCountSource.formula
identifies the pair count EXACTLY with sum_e 1_(e subset A) times the
number of U in the source Gamma_e(r-2) contained in A minus e. Thus it is
the printed J_e times admissible-complement count, even on the bad event;
it is not a replacement random variable having the same mean.

SelectedSubsetCounts proves the finite activation/expectation identity
for any prescribed subset class. ActiveSetCylinder transports EVERY
observable and event of the actual active set through a finite cylinder
containing all original windows. These identities give the exact direct
and pair means, including the source Gamma counts, heterogeneous actual
joint events and affine compatibility. The regular marginal identity
then yields the printed nominal powers, with F_r and G_r explicitly
subtracted. The modified count is literally zero on nonretention.
Integrating its pointwise subset-count decomposition gives the source
identity, including both exceptional-event leakages. No moment transfer
or probability interpretation of a retained polynomial is assumed.

The source weighted G estimate has the stronger UNCONDITIONAL rate7/6:

  sum_(r>=0) 2^r*G_r <= N^(-7/6+epsilon).

The exact finite cardinality grouping identifies this sum with the
already proved independent secondMass. Terms at r<2 and r>n vanish,
so the displayed infinite series is literally the finite source sum.
The same convention applies to H_r: its small and large terms vanish,
all terms are nonnegative, and the ordinary real series equals its
finite support sum for every N,L.

ExceptionalEventHolder proves the actual finite eighth-moment Holder
inequality. ActiveSetExceptionalMoment then bounds the contribution
on nonretention of ANY nonnegative active-set observable f(A)<=|A|^j by

  (E Z_G^(8j))^(1/8) * P(E')^(7/8).

The completed exceptional-event theorem at the FIXED margin1/120 gives
P(E')<=N^(-4/5+1/120). The previously proved UNCONDITIONAL subpower
moment bound gives E Z_G^(8j)<=N^(1/120) for each fixed j. Thus the
exceptional contribution is at most N^(-83/120). Its threshold is chosen
before all critical L, all dyadic subgrounds G, and EVERY f satisfying
the pointwise bound. The SAME finite exceptional-event input bundle is
chosen BEFORE ALL fixed degrees j. No uniformly bounded higher moments,
BCN premise or degree-dependent geometric property is needed.

For the actual pair count, a finite combinatorial estimate gives
P_r(A)<=|A|^(r+2). Therefore the same single input bundle proves, for
EVERY fixed r, H_r<=N^(-83/120). The exponent83/120 exceeds2/3 by1/40;
it is sufficient for the requested little-o. P1-MATH-0147 records this
weaker-moment route and its stronger quantifier/input scope, not an
improvement over the source's fixed-order numerical exponent7/10.

RetainedPairMomentGenerator proves the exact shifted-binomial generator
bound for the UNRESTRICTED positive pair moments:

  sum_(r=0..n) u^r E P_r <= u^2*beta*(1+u*p)^(n-2)
    <=u^2*beta*exp(u*E Z_regular), for u>=0,n>=2.

Since H_r<=E P_r, it also bounds every exceptional subseries.
RetainedGoodPairScale bounds beta by a constant times the literal nominal
second factorial correction a_N=E(Z_N)_2-(N*2^-L)^2, UNCONDITIONALLY.
It uses the homogeneous principal-channel upper bound and the existing
unconditional positive lower bound a_N>=c_C*L*N^-2/3. Consequently the
ENTIRE4^r-weighted H sum is at most A_C*a_N, without geometric premises.
The actual mean cap and eventual regular cardinality>=2 are discharged.

WeightedLeakageCutoff splits the2^r sum at an arbitrary fixed J. Its
finite part is controlled by the fixed-order rate83/120; the remaining
part is at most2^-J times the4^r generator. Choose J after a positive
tolerance eta, then absorb the finite constant using the gap1/40 and
the proved lower bound for a_N. This yields the full uniform statement:

  for every eta>0, eventually for EVERY critical L,
  sum_(r>=0) 2^r*H_r <= eta*a_N.

The SAME finite geometric bundle was chosen before eta and before every
fixed order. No growing-order moment estimate is assumed or invoked.
ModifiedMomentDecompositionUnderInputs.companion_T22_6 assembles all
source clauses with this quantifier order. Its only unproved inputs are
the SAME three recorded geometric counting properties, through the
existing RetainedExceptionalEventUnderInputs.Hypotheses at1/120.
Every constituent finite cap is exposed in that bundle definition.

This checkpoint adds16 modules,50 theorems and15 definitions. Coverage
is87/167 unconditional and32 conditional, with147 confirmed mathematical
improvements. Main1.1's optimal4/3 bound, main15.10 and main15.14 remain
open; the completed T22.6 does not silently discharge them. No dependency
download, original manuscript-byte change, Paper C port, hidden axiom or
Palomar registration is added.

Verified under Lean v4.36.0-rc2: full build passed (13733 jobs); direct axiom audit passed for 10690 declarations using only propext, Classical.choice and Quot.sound; all 9122 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 12.36 GiB.


## Complete primitive mass at four blocks and all fixed orders, main15.5

Main Proposition15.5 is COMPLETE CONDITIONALLY, including its formerly
open r=4 case. For every fixed r>=4 and positive epsilon, one finite
bundle of the SAME three existing geometric counting properties gives
one threshold before every critical length L, dyadic subground G and
actual primitive subpopulation F of size r. Both source bounds hold:

  mass(F)=sum_I (product_(x in I) actual p_x)*2^rho(I)
    <=N^(-4/3+epsilon),
  mass(F)<=N^(-2r/(r+2)+epsilon).

The SECOND bound now holds on the WHOLE primitive population: the dense
nullity restriction is unnecessary. At r=4 the two exponents coincide.
For every fixed r>=5 the existing stronger UNCONDITIONAL elementary
bound N^(1-r/2+epsilon) already gives both inequalities on the whole
population. The new conditional proof is needed only at r=4. All exact
heterogeneous marginals, including zero marginals and irregular windows,
are retained. No affine compatibility or positive joint-event premise
is imposed, and no fixed-order result is used at a growing order.

For r=4 below rho<L/2, the proved independent primitive mass has power2;
the rank factor costs only N^(1/2+o(1)), giving the UNCONDITIONAL stronger
rate3/2. The dense sector rho>=eta*L, for each fixed eta>0, has power4/3
under the existing two-target geometric inputs. Its four sectors are
literal finite families, and the proof tracks every source set before
using its uniform two-target extension bound.

FixedAnchorDegreeBudget allows any fixed polynomial width prefactor.
FixedOrderAnchorMass counts actual good-anchor CRT covers at FIXED order
r. The assignment cost is N^(t/A+epsilon), instead of the all-order
factorial-series cost N^(2t/A+epsilon). Its heterogeneous independent
mass therefore has exponent -t*beta+t/A. The threshold depends on r;
this does not alter the existing all-cardinality statement. Furthermore
SelectedAnchorRelation needs only the t selected anchors to have large
kernels. It does not require every value of the source window to have
a large kernel. These are explicit improvements recorded by extending
P1-MATH-0073; no new correction identifier is needed.

Choose A=6, beta=9/10 and t=4. The actual moderate certificate sector has
UNCONDITIONAL rank-weight power29/15, stronger than4/3. The actual
saturated pairs have at most N^(1+4/6+epsilon) source choices, by the
already proved literal outgoing-degree theorem. Fixing each such source
pair leaves exactly two dense primitive targets. The restricted
extension theorem gives a uniform cost (K_C/N)^2*N^(-1+epsilon), so the
complete saturated mass has rate4/3.

For the small-kernel sector, the proof uses the already proved enlarged
population Bad of windows having two values with EACH K_(L+1)<=N^(2/3).
Its cardinality is N^(2/3+epsilon). Marking one such source and any other
source gives at most N^(5/3+epsilon) source pairs; the same two-target
estimate gives rate4/3. This enlarged population has sufficient size
control; the more specific product-cap population is unnecessary here.

WindowSquareKernelBound proves the exact finite inequality

  a_Y(v)^2*K_H(v)<=v

for every positive integer v and ALL cutoffs H,Y. It follows by removing
the actual square factor, preserving its full parity vector, and bounding
the actual remaining odd kernel by the quotient. Consequently, outside
Bad, at most ONE value has a_Y(v)^2>N^(2/3), eventually. No smoothness
assumption, pairwise separation or unproved square-part count is used.

RestrictedSupportRank proves a finite binary-code estimate: if every
word has at most d nonzero coordinates outside S, the actual code rank
is at most |S|+d. The physical code projects onto every actual effective
relation. A primitive projects injectively onto each whole block. If
neither a moderate four-anchor certificate nor a saturated pair exists,
every physical relation selects at most three large-kernel coordinates
in each block. Thus EVERY window has at least rho-3 small-kernel
coordinates. Dense rho is eventually at least15, so deleting the one
possible large square part leaves eleven literal distinct small-kernel
values with controlled square parts.

With m=11, A=6, beta=9/10, u=2/3, the completed several-small-kernel
window theorem bounds this actual Rare population by N^(5/6+epsilon).
Any two-source subset of an all-Rare four-window primitive lies in
Rare.powersetCard2, of cardinality at most N^(5/3+epsilon). The SAME
restricted two-target theorem supplies rate4/3 for this last sector.
The four exact sectors cover every dense primitive family. Fixed
constants and smaller margins are absorbed before the final threshold.

RestrictedDensePrimitiveMassUnderInputs proves a reusable, stronger
source-population statement: for any fixed s>=1 and source-population
exponent sigma, actual dense primitive extensions of size s+2 over at
most N^sigma prescribed source sets have rank mass
N^(-1-s+sigma+epsilon). It constructs the parameter bundle from the
proved two-target theorem; it does not assume a desired family mass.
The same bundle, chosen before N,L and all source/subfamily choices,
controls the three source-restricted sectors of the four-block proof.

Only P1-GEO-CHOSEN-SOURCE-SURFACE-COVER,
P1-GEO-ORDINARY-SURFACE-COVER and P1-GEO-NORMALIZED-CURVE-UNIFORM remain
unproved ordinary arguments. No BCN, bounded moments, target primitive
mass or new literature property is assumed. The finite anchor, code,
square and source-cover results are unconditional. This checkpoint adds
13 modules,30 theorems and8 definitions. Coverage is87/167 unconditional
and33 conditional; the existing finding73 is extended and the confirmed
finding count stays147. The sharp triple activity, main15.10 reduction,
main15.14 reconstruction and optimal main1.1 remain open. No dependency
download, Paper C port, original source-byte edit, new axiom or Palomar
registration is introduced.

Verified under Lean v4.36.0-rc2: full build passed (13759 jobs); direct axiom audit passed for 10720 declarations using only propext, Classical.choice and Quot.sound; all 9160 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 12.31 GiB.


## P1-MATH-0148 — Coarse higher activity suffices for the sharp incompatible remainder

The sharp incompatible connected remainder of main15.10 needs no
optimal triple activity exponent. Separate all pair sources in the exact
proper-source expansion and use the already proved all-cardinality pair
deficit of rate3/2. Singleton coefficients vanish. Every higher source
has the earlier coarse full absolute activity rate1, while its failed
independent complement costs1/2 unconditionally. Their product has rate3/2.
A finite size split proves the sharp incompatible bound uniformly over
every prescribed bounded order range. The coarse activity dependency
chain predates this theorem, so no induction on the target sharp rate or
circular sharp input is used. The whole connected reduction to A3 then
follows from the actual finite seed cover and completed primitive4/3 mass.
The optimal41/30 triple estimate is still needed for the later optimal
law consequence; it is removed only from this incompatible-sector proof.


## Complete reduction of connected activities to triples, main15.10

Main Proposition15.10 is COMPLETE CONDITIONALLY, including BOTH the
reduction to the actual third absolute activity and the sharp3/2
incompatible remainder. For each fixed R, every positive epsilon has
one finite bundle of the same three geometric properties and one
threshold before all critical lengths, all orders3<=r<=R, all dyadic
subgrounds G and every actual connected subpopulation F of size r:

  sum_(I in F)|c(I)| <= N^epsilon*A3(G)+N^(-4/3+epsilon),
  sum_(I in F,q(I)=0)|c(I)| <=N^(-3/2+epsilon),

where A3(G)=sum_(D subset G,|D|=3)|c(D)| is the literal actual third
absolute centered activity. article_15_10 specializes the stronger
bounded-range result to each fixed r>=4 and the entire connected
population. It assumes no desired bound for A3, no count-law estimate
and no sharp fixed-order connected activity input. Exact heterogeneous
marginals, zero-marginal sites and every affine incompatibility remain
in the original model throughout.

IncompatibleHigherDeficit first separates all actual PAIR sources from
the proper-source expansion. Singleton centered coefficients vanish
exactly. Every pair contribution is charged to the already proved
all-cardinality pair deficit, of rate3/2. Only proper sources of sizes
at least3 remain. FixedActivityInputBundle supplies their complete
absolute activity at the already proved COARSE rate1, using the existing
fixed-moment geometric bundle. The independent non-direct complement
cost has UNCONDITIONAL rate1/2 uniformly over bounded source sizes.
Multiplication gives rate3/2 for ALL remaining sources. The independent
connected-family term is at most N^(-r/2+epsilon), sufficient already
at r=3. One finite cardinality split and fixed-constant absorption give
one threshold for all3<=r<=R.

This proves the source's sharp incompatible remainder WITHOUT the
optimal arithmetic triple exponent41/30 and without an induction on
the new sharp connected rate. The printed proof invokes that stronger
triple input. The weaker coarse full-activity theorem suffices once the
pair deficit is separated before applying the half-power complement
bound. P1-MATH-0148 records this reduction of mathematical prerequisites.
No target sharp estimate is assumed, directly or through an interface.
The coarse activity proof uses earlier independent modules and does
not depend on this new sharp incompatible theorem.

VariableConnectedSeedCatalog proves the same exhaustive actual seed
cover with an arbitrary fixed small-intersection threshold eta, rather
than the previous hardcoded1/12. The catalog contains primitive seeds,
connected triples, low-intersection two-pair seeds, dense pair crossings
and minimal direct-crossing seeds. The exact finite cover precedes all
probability and asymptotic estimates, and includes all connected
original-window families, whether compatible or not.

SharpConnectedSeedCatalogUnderInputs chooses eta=epsilon/8 BEFORE N.
Primitive seeds of size>=4 use the newly completed main15.5 rate4/3;
primitive triples are included in the positive connected triple mass.
That positive triple mass is already bounded by A3 with coefficient1
and an error of rate3/2. Dense pair crossings and every fixed minimal
direct crossing have rate5/3. Low-intersection two-pair seeds have
rate4/3 minus eta; this fixed loss is absorbed in the requested margin.
The finite primitive/direct size ranges are assembled before choosing
N. The complete seed mass is bounded by N^epsilon*A3+N^(-4/3+epsilon).
No sharper pair-target rank estimate or separated compressed all-order
hypothesis is added.

VariableSeedMassPropagation retains actual positive joint moments and
extends every seed of bounded size to the prescribed fixed target size.
Its only constant is the actual target factorial, and its power loss
can be any fixed positive margin. CompatibleTripleJointBound bounds
|c(I)| by2^|I|*q(I) only on the positive joint-event sector. Both finite
constants are absorbed with smaller fixed margins. The remaining
zero-joint-event sector uses the NEW independent3/2 proof, instead of
applying a positive joint bound to an incompatible event. This gives
the complete actual centered-activity reduction, with no compatibility
substitution or signed retained polynomial used as a probability.

The compatible parameter bundle at margin z contains finitely many
primitive and direct two-target bundles, one triple pair bundle at
sizeCap(z/8192), a low-pair bundle at sizeCap(z/32768), and dense/direct
pair bundles at sizeCap(z/16384). SharpIncompatibleActivityUnderInputs
at margin z contains the existing fixed-moment bundle, plus the exact
finite all-pair deficit initial and entry bundles at sizeCap(z/8192)
and sizeCap(z/262144). The final combined theorem calls these compatible
and incompatible bundles at epsilon/8 and epsilon/2 respectively.
Every constituent hypothesis is one of the SAME chosen-source surface
cover, ordinary surface cover and normalized-curve count properties.
They remain ordinary explicit arguments, never global axioms.

This checkpoint adds8 modules,10 theorems,2 definitions and6 finite
parameter structures. Main15.10 changes from in_progress to conditional.
Coverage is87/167 unconditional and34 conditional; confirmed improvements
increase147 to148. The optimal arithmetic triple bound, main15.14's
optimal law consequence, main1.1 and Palomar remain open. No dependency
download, Paper C port, original source-byte change, new literature
property or hidden axiom is introduced.

Verified under Lean v4.36.0-rc2: full build passed (13775 jobs); direct axiom audit passed for 10730 declarations using only propext, Classical.choice and Quot.sound; all 9178 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 12.26 GiB.


## P1-MATH-0149 — Both first quadratic approximations have the stronger rate one

Both first quadratic approximations of companionT17.5 have the
stronger error N^(-1+epsilon), under the same three existing explicit
geometric properties. The actual original law on every dyadic subground
first satisfies the full symbolic reconstruction N^epsilon*A3+N^(-4/3+epsilon).
The already proved coarse full third activity of rate1, with fixed smaller
margins, gives the numerical rate1. Unconditional restoration then gives
both full-model exact-mean and nominal-mean references with the same full
actual second factorial cumulant. This avoids limiting the first-law
estimate to the4/5 exceptional-event coupling rate. It neither proves nor
assumes the optimal triple activity or the optimal4/3 law remainder.


## Symbolic law reconstruction and stronger first quadratic rate

The full SYMBOLIC estimate of main15.14 is proved for the actual original
count law, exact mean and actual second factorial cumulant:

  ||Law(Z_G)-Q(mu_G,kappa2_G)||_1
    <=N^epsilon*A3(G)+N^(-4/3+epsilon).

Here G is ANY subset of the dyadic block and A3(G) is the actual sum of
absolute original centered coefficients on G.powersetCard3. One finite
bundle of the SAME three geometric properties and one threshold precede
all critical lengths and all subgrounds. The source specialization
article_15_14_symbolic uses the entire original dyadic block. No desired
law approximation, sharper triple activity, finite connected-rate
hypothesis or uniformly bounded growing moment is assumed.

Main15.14 changes from not_started to IN_PROGRESS, not conditional or
proved: its final optimal4/3 law consequence still needs the unproved
sharp arithmetic triple estimate41/30 (or a sufficient substitute).
The complete symbolic inequality does not establish that numerical
optimal rate by itself. Main1.1 also remains in_progress.

TripleControlledFixedActivity uses the newly completed main15.10 at
ALL orders3..256, with one finite cardinality split. It sums arbitrary
fixed nonnegative weights while keeping A3(G) symbolic. Fixed constants
are absorbed using smaller margins. No connected-activity rate is
supplied as an external input. The exact chosen geometric parameters
precede N and every actual subpopulation.

TripleActivityClosureUnderInputs closes BOTH the entire connected
remainder up to SecondOrderBoundaryCutoff and the all-cardinality
primitive deficit sum, each with the same symbolic bound. Bounded
primitive families are genuinely connected, so the finite theorem
applies to them. The existing UNCONDITIONAL primitive tail has rate7/5.
The actual connected tail at sizes STRICTLY>256 has rate83/60 under
its existing finite geometric bundle. Both exceed4/3. The literal
cutoff is already proved o(log N); no bounded-order constant is used
at that growing order. One finite bundle and common threshold handle
both complete sums and every dyadic subground.

TripleActivityLawReconstructionUnderInputs then applies the already
proved unconditional finite second-order stopping inequality to the
original normalized count pushforward. D2 retains all pairs, with every
signed pair coefficient and exact heterogeneous marginal, including
zeros and all affine incompatible cases. Its suffix kernel remains a
positive actual probability kernel. Its comparison reference is a
signed measure; no retained polynomial is declared to be a probability.

Write a for the complete weighted pair activity and b for the higher
component activity. The nonlinear error is bounded BEFORE the pair
term is restored:

  exp(a+b)-1-a <= b+(a+b)^2*exp(a+b)/2.

The linear b and the primitive deficit stay symbolic. Only the earlier
coarse full activity A3(G)<=N^(-1+delta) is used to show that a+b<=1 and
that its square costs N^(-4/3+4delta). In fact a<=4V, b<=2V for
V=N^(-2/3+2delta); thus (a+b)^2<=36V^2. There is no loss of the linear
A3 term through an unjustified optimal numerical substitution.
The complete pair deficit has rate3/2, the large actual stopped boundary
has unconditional rate4, and the exact heterogeneous signed-reference
conversion has rate5/3. All suffice at this precision.

The internal accuracy is delta=min(epsilon/16,1/48), fixed before N.
The final parameter bundle consists of the symbolic connected/primitive
closure, the earlier coarse order3 activity bundle, the finite full
pair-deficit initial and entry bundles at sizeCap(delta/2048) and
sizeCap(delta/65536), and pair/conversion bundles at sizeCap(1/100).
The coarse order3 bundle is used at4delta. Each underlying condition is
one of P1-GEO-CHOSEN-SOURCE-SURFACE-COVER,
P1-GEO-ORDINARY-SURFACE-COVER or P1-GEO-NORMALIZED-CURVE-UNIFORM.
They remain ordinary explicit arguments, not global axioms. No BCN,
sharp A3 bound or target law estimate is hidden in the bundle.

The same uniform_estimates theorem returns both the proved coarse A3
bound and the symbolic reconstruction after the SAME threshold. This
has a new numerical consequence. QuadraticRateOneUnderInputs.uniform_exact
chooses smaller fixed margins and proves, on every original subground,

  ||Law(Z_G)-Q(mu_G,kappa2_G)||_1 <=N^(-1+epsilon).

Applying this to the original regular subground and then using the
already proved UNCONDITIONAL law/mean/second-cumulant restoration gives
BOTH full-model approximations, with exact or nominal mean and the SAME
full actual second factorial cumulant, at rate1. This strengthens the
printed rate4/5 in companionT17.5. P1-MATH-0149 records the improvement.
No new optimal triple estimate is needed for this stronger first
approximation, and neither the optimal4/3 remainder nor its lower bound
is asserted. The old4/5 declarations remain valid.

This checkpoint adds4 modules,7 theorems and4 parameter structures.
Main15.14 is in_progress; companionT17.5 remains conditional with the
stronger rate1, and main1.1 gains the same checked numerical bound.
Coverage stays87/167 unconditional and34 conditional; confirmed
improvements increase148 to149. No dependency download, Paper C port,
original source-byte edit, new literature input, hidden axiom or Palomar
registration is introduced.

Verified under Lean v4.36.0-rc2: full build passed (13783 jobs); direct axiom audit passed for 10737 declarations using only propext, Classical.choice and Quot.sound; all 9189 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 12.23 GiB.


## P1-MATH-0150 — Stronger fourth-cumulant reduction from a global compressed-pair count

The first fourth-cumulant identity is valid with the stronger error
N^(-5/3+epsilon), under the same finite geometric properties. The actual
good-good apart product cost is unconditionally N^(-7/3+epsilon), stronger
than the printed11/6: two compressed pairs, with all four actual offsets,
map injectively into a global dependent-block pair population of size
N^(1+epsilon). The finite cover from unordered disjoint non-direct edge
pairs is checked using exact nullity and actual effective spaces. The
remaining products are bounded by A2*(Aweak+Aexceptional), giving power5/3
for the complete literal apart cost. Repeated/shared-edge costs have5/3;
coarse full A3 of rate1 already gives rate2 for repeated-index cumulant
terms. Neither the first identity nor the incompatible3/2 comparison
requires the still open optimal triple41/30 estimate. The other two
source errors remain3/2.


## Complete fourth-cumulant identities with a stronger first error

Main Lemma16.1 is complete conditionally for the actual full original
count, including all three literal identities and K4positive>=0. In fact
its first error has the stronger power5/3:

  |kappa4-24*K4| <=N^(-5/3+epsilon),
  |K4-K4positive| <=N^(-3/2+epsilon),
  |kappa4+3*alpha^2-(3*alpha^2+24*K4positive)| <=N^(-3/2+epsilon).

Here alpha is the actual second factorial cumulant, K4 sums the actual
original centered coefficients over all connected quadruples of the full
dyadic block, and K4positive retains precisely those with positive actual
joint probability. Every heterogeneous marginal, repeated index, zero
marginal and incompatible affine configuration is retained. One finite
bundle of the SAME three geometric properties and one threshold precede
all critical lengths. No optimal triple estimate, target cumulant bound,
abstract non-direct-cost assumption or BCN premise is used.

The key new unconditional estimate is a GLOBAL count of two actual
compressed pairs, rather than a fixed-source exceptional-target count.
For fixed channels (a,b),(c,d), with positive ordered entries, both
actual unit relations and a nonzero intersection between their actual
effective spaces, all literal ordered source quadruples have cardinality
at most N^(1+epsilon), after all four offsets have been summed.
Each first source pair is uniquely recovered from its compressed anchor
when its two offsets are fixed. The host key consists of the two anchors.
Its two compressed blocks are actual unions of dilated original window
values, of height between N/2 and 3(b+d)N, and width (b+d)(L+1).
Their even square-class spaces equal the sums of the two original spaces.
The existing unconditional dependent-block pair count applies to these
literal blocks, including equal compressed centers. The four offset
patterns cost only a fixed polylogarithmic factor. No branching statement
for a new assumed population is inserted.

For the actual good-good apart products, a finite cover is proved from
unordered pairs of disjoint edges to these source quadruples. Non-direct
nullity is equivalent to a nonzero intersection of the two total spaces,
because the edge vertex sets are disjoint. All finite retained channels
are summed after their parameters have been fixed. Thus their actual
unordered population also has cardinality N^(1+epsilon), uniformly in the
private threshold H. At H=2Q(L+1), each good actual centered coefficient
has size N^(-5/3+epsilon), by the existing private-channel ratio and exact
heterogeneous marginal cap. Their complete product mass consequently has
the stronger UNCONDITIONAL power7/3, replacing the source proof's11/6.

The complement is controlled by an exact nonnegative finite cover. Every
product involving an edge outside the good class is charged to
A2*(Aweak+Aexceptional), with no missing repeated bad edge or implicit
sign assumption. The exact actual pair activity decomposition identifies
the complement weight. Choosing the partition's fixed small parameter
after epsilon and before N gives rate5/3 for the entire literal
nonDirectApartCost. This step uses the existing finite geometric inputs
for the actual pair, weak and exceptional activities; its good-good
part remains unconditional.

Repeated-edge and shared-vertex products have rate5/3 under the same
finite inputs, using the unconditional actual covariance-row bound and
marginal cap. The exact fourth repeated-index remainder has rate2:
its costs are p_*A3, p_*^2 A2 and p_*^3 mu. The already established coarse
FULL third absolute activity of rate1 suffices. The unproved optimal
triple rate41/30 is unnecessary for this lemma. Combining these finite
costs with the exact connected fourth-cumulant identity proves the
stronger first error5/3. Incompatible connected quadruples have rate3/2
by the already completed sharp incompatible activity theorem; its proof
also uses only coarse higher activity. Compatible original coefficients
are nonnegative, yielding the other two source identities.

FourthConnectedCumulantUnderInputs.Hypotheses makes all finite inputs
explicit: coarse order3 activity at epsilon, four sharp-pair bundles at
sizeCap(1/100), and one actual partition bundle at sizeCap(epsilon/2048).
The final Lemma16.1 bundle uses this at epsilon/2 and the existing sharp
incompatible order4 bundle at epsilon/2. These reduce to ordinary
arguments for P1-GEO-CHOSEN-SOURCE-SURFACE-COVER,
P1-GEO-ORDINARY-SURFACE-COVER and P1-GEO-NORMALIZED-CURVE-UNIFORM.
They are not global axioms. The earlier BCN preparatory declarations
remain valid but are no longer needed by the completed source theorem.

P1-MATH-0150 records the stronger global compressed-pair count, the
unconditional good-good cost7/3, the complete apart cost5/3, and the
improved first cumulant error5/3. The second and positive-quartic errors
retain3/2, because the incompatible contribution is controlled at that
rate. Main16.2 and the optimal4/3 law lower bound remain open at this
checkpoint. This does not claim completion of the optimal upper bound,
sharp triple arithmetic, both documents or Palomar preparation.

No original manuscript byte, dependency, external literature input,
Paper C port, new axiom or Palomar registration is introduced. Coverage
is87/167 unconditional and35 conditional; confirmed improvements150.

Verified under Lean v4.36.0-rc2: full build passed (13805 jobs); direct axiom audit passed for 10760 declarations using only propext, Classical.choice and Quot.sound; all 9222 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 12.18 GiB.


## Optimal-power lower inequality for the full exact quadratic reference

The lower inequality displayed in main Theorem16.2 and the optimal
quadratic lower clause of main1.1 are now proved for the actual full
original law and exact actual mean/second factorial cumulant:

  ||Law(Z_N)-Q(mu_N,alpha_N)||_1 >=c*N^(-4/3-epsilon), c>0.

This is the ordinary full singleton l1 distance of the actual original
probability measure and the literal quadratic Poisson signed measure.
No retained finite polynomial, formal coefficient norm, truncated law,
assumed norm comparison or positivity of the reference replaces it.
All original heterogeneous marginals and affine incompatibilities are
retained. One finite bundle of the SAME three geometric properties is
chosen before N and before all critical lengths. The already open optimal
triple activity and optimal upper law rate are NOT inputs to this lower
bound. Main16.2 moves from not_started to IN_PROGRESS: its lower inequality
is complete, but its concluding identification of the optimal power also
refers to the still open optimal upper bound. Main1.1 stays in progress.
Neither row is counted complete at this checkpoint.

PositiveQuarticObstructionUnderInputs uses completed main16.1 at the
FIXED margin1/12 and the unconditional actual alpha lower bound
alpha>=d*L*N^(-2/3). Its error is N^(-17/12), smaller than alpha^2 at
power4/3. After a common threshold, the actual coefficient satisfies

  kappa4+3alpha^2 >=2alpha^2 >=d'*L^2*N^(-4/3).

The compatible connected contribution is nonnegative. This inference
uses only the earlier coarse third activity through main16.1; the
still open41/30 triple estimate is unnecessary.

The fourth Charlier polynomial is literal:

  H4(k;mu)=(k)_4-4mu(k)_3+6mu^2(k)_2-4mu^3 k+mu^4.

Its uniform envelope |H4|<=(1+M)^4(1+k)^4 is proved whenever0<=mu<=M,
without a lower positive mean premise. OriginalLawPolynomialMoments
identifies EVERY actual singleton test sum with the finite observation
expectation and original infinite count integral. In particular the
exact H4 sum is kappa4+3alpha^2, including all repeated-index terms.
FourthCharlierReference proves its sum against Q(mu,alpha) is exactly0
for EVERY mu>=0 and real alpha, using genuine convergent factorial
moment sums, not a formal generating function assertion. General shifted
Poisson factorial sums and the quadratic factorial correction are
proved at every fixed order.

PoissonPolynomialMoments gives a positive summable envelope for the
absolute quadratic signed reference, uniformly over0<=mu<=M and|alpha|<=1.
It compares mass(mu,k) with exp(M)*mass(M,k) and controls both genuine
shifted sequences in the second difference. Every polynomially weighted
absolute series is summable and has a uniform finite bound. The actual
mean is uniformly bounded, and the already proved sharp pair bound
makes the actual |alpha|<=1. The earlier bounded fixed ordinary moments
supply the corresponding actual-law bound.

PolynomialTestTruncation proves a general signed-sequence estimate from
a FIXED higher moment, with all summability discharged. If|f(k)|<=K(1+k)^d,
r>=d and R>=1, then

  |sum a_k f(k)| <=K R^d sum|a_k|
                    +(K/R^(r-d))*sum|a_k|(1+k)^r.

Its proof splits the pointwise envelope at1+k=R, before taking the true
convergent infinite sums. It never applies a bounded-test inequality
directly to an unbounded polynomial. FourthCharlierLawDistance applies
this to the literal difference of the actual-law and quadratic-reference
singleton sequences. The unweighted sum is proved equal to the exact
SignedAtomicDistance.distance of those actual signed measures.

For a prescribed epsilon>0, set delta=epsilon/8 and
r=4+ceil((7/3)/delta). This integer is FIXED before N. At R=N^delta,
the weighted tail has power at least7/3 and is absorbed into half the
positive quartic coefficient. The low part costs R^4=N^(epsilon/2).
Dividing gives a positive constant times N^(-4/3-epsilon/2), hence the
stated lower bound with epsilon. The single moment bundle is used at
accuracy1/2, its pair and alpha bundles at sizeCap(1/100), and the quartic
bundle at1/12. All are finite and reduce to the same three explicit
geometric properties; no uniformly bounded growing-order moment is
assumed, and no target law lower bound occurs among the premises.

This checkpoint adds8 modules of actual polynomial sums, reference
moments, a general truncation inequality and the assembled optimal-power
lower inequality. It introduces no further mathematical improvement ID:
the needed removal of the optimal triple premise is already recorded in
P1-MATH-0150. No original source byte, dependency download, Paper C port,
new literature input, hidden axiom or Palomar registration is introduced.
Coverage remains87/167 unconditional and35 conditional, with150 confirmed
improvements. The optimal numerical upper rate and main15.14 final
numerical consequence remain open.

Verified under Lean v4.36.0-rc2: full build passed (13821 jobs); direct axiom audit passed for 10784 declarations using only propext, Classical.choice and Quot.sound; all 9249 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 12.14 GiB.


## P1-MATH-0151 — Fixed-height law hierarchies need only the first rate-one approximation

Every fixed-height explicit quadratic and Hermite original-law
hierarchy follows already from the first exact quadratic approximation
of rate1 and the actual finite-channel cumulant profiles. The source
proof invokes the optimal exact-reference4/3 rate, which is unnecessary
because (h+1)/(h+2)<1 at each fixed height. The complete actual signed
remainders, moving TV equivalents, probability witnesses and optimal
powers h/(h+1) are verified. The actual weak/exceptional/private pair
partition also suffices without the stronger homogeneous nonaligned
main18.2 rank sum on incompatible configurations. Thus main1.4,18.1
and18.3 are complete under the existing finite geometric properties,
independently of the still open optimal triple arithmetic and exact-
reference optimal upper bound. The exact-parameter Hermite4/3 assertion
and main19.1 full completion remain open.


## Complete explicit references and fixed-height original-law hierarchies

Main Corollary1.4, Theorem18.1 and Corollary18.3 are complete
conditionally, for the ACTUAL FULL original law and the literal finite
channel coefficients. One finite bundle of the SAME three geometric
properties precedes N and every critical length. No optimal triple41/30,
optimal exact-reference4/3 law bound, target truncation remainder or
homogeneous nonaligned-rank estimate is assumed.

ExplicitQuadraticApproximationUnderInputs.article_1_4 gives the complete
source two-channel reference: its full original-law singleton l1 error
is N^(-4/5+epsilon), the actual signed reference is eventually a probability,
and every singleton has exactly the printed Poisson--Charlier mass.
The coefficient is the literal finite S_23+S_34 expression and its mean
is the nominal N*2^(-L). The proof combines the already completed actual
pair profile with the stronger first quadratic rate1; it does not use
the still open optimal quadratic upper bound. Reference probability
status and its mass formula were already unconditional and are included
in the assembled source theorem after the same threshold.

For EVERY fixed height h>=3, the complete cumulant hierarchy is proved:

  |alpha-coefficient_h| <=N^(-1+1/(h+1)+epsilon),
  |alpha-coefficient_h-heightMass_(h+1)|
       <=N^(-(h+1)/(h+2)+epsilon).

All finite lower-order terms in each exact signed channel polynomial
are retained. Alpha is the actual full second factorial cumulant,
already identified with Var(Z)-E(Z), and heightMass is exactly
lambda^2/N times the full height sum T_(h+1)(L). The source exponent
identity -1+1/(h+2)=-(h+1)/(h+2) is itself checked.

FixedHeightPrivateChannels proves actual reduced-channel uniqueness
from the two exact unit alignments. At4Q^2(L+1)<N the integer determinant
between two distinct reduced slopes cannot vanish on an actual dyadic
source pair. Coprimality then identifies the two channels. Hence their
actual unordered private edge families are pairwise disjoint. Their
union is a literal subset of the actual pair powerset, and its absolute
sum equals the sum over channels with no multiplicity assumption.
An exact sigma/product index bijection identifies the sum of main terms
with the source finite-height coefficient.

The full signed-pair remainder outside that private union is bounded by
the ACTUAL weak plus exceptional activities of the finite pair partition.
This includes all nonaligned, incompatible, locally defective and boundary
pairs. Independent nonzero-cardinality families have zero centered
coefficient, as proved earlier. The fixed-height weak tail is bounded
unconditionally at power1-1/(h+1). The complete exceptional class has
power1 under the recorded geometric inputs, without a homogeneous-rank
substitute on incompatible pairs. Each retained channel's joint main
term, independent correction and sign gap have power1. The diagonal
sum of the exact squared marginals has power1 as well. These facts
assemble the literal coarse cumulant profile. No target profile is
provided as a premise.

FixedHeightQuadraticLawUnderInputs proves both the original-law coarse
approximation and the COMPLETE first-omitted-height signed remainder.
In the latter, the exact signed measure Law(Z)-Q(lambda,coefficient_h)
is compared with (heightMass_(h+1)/2)*Pi_lambda*Delta^2. The remainder is
N^(-(h+1)/(h+2)+epsilon) in the ordinary full singleton l1 metric.
The exact reference-increment and signed-measure translation identities
are checked before applying the metric estimate. The first quadratic
rate1 suffices at every fixed height because (h+1)/(h+2)<1. Neither
optimal4/3 reconstruction nor sharper triple activity is needed.

The actual original-law leading distance equivalent is also proved.
For fixed h,C, ONE finite geometric bundle, chosen at the positive margin
1/(2(h+1)(h+2)), precedes EVERY tolerance tau>0. After its corresponding
common threshold and for ALL critical L, an actual probability witness
Q_h for the literal reference satisfies

  |TV(Law(Z),Q_h)/(phaseMass_(h+1)*norm(Pi_lambda*Delta^2)/4)-1|<=tau.

The phase retains L mod(h+1), the moving nominal mean, and the Poisson
second-difference norm at that same mean. The leading denominator is
proved positive. The smaller actual-law error at height h+1 is compared
with the already established exact gap of adjacent references. A uniform
power separation and the positive full phase lower bound make that
error negligible. The reverse triangle inequality is applied to actual
signed distances; the factor2 between l1 and actual total variation
is retained. A separate quantitative lower bound
c*N^(-1+1/(h+1)), c>0, for the actual full law-to-reference l1 distance,
together with the coarse upper estimates at every positive loss,
proves the claimed optimal power h/(h+1). These are original-law
conclusions, rather than distances only between constructed references.

FixedHeightHierarchyUnderInputs.article_18_1 assembles both literal
remainder statements, actual probability status and the full moving
TV equivalent, with one finite bundle and common threshold. The earlier
phase constants give the source c_b(r), including its positivity.

TwoChannelReferenceUnderInputs specializes the source hierarchy at h=4
and h=5. The two-channel signed remainder has power5/6 and the leading
correction is precisely M5. The exact closed M5 formula, the identity
coefficient5=twoChannelCoefficient+M5 and both finite S_35/S_45 formulas
were already proved and remain literal. The actual-law TV equivalent
at h=4 has the printed coefficient17(r+4)/(1200*2^(r/5)), the moving
lambda^(9/5), the actual norm and L*N^(-4/5). At h=5 it has the moving
height6 phase; its printed c6(r)=(r+5)/(45*2^(r/6)) and lambda exponent11/6
are identified exactly. Thus both the two-channel optimal power4/5 and
the four-channel optimal power5/6 concern their specified original-law
references, with all residues varying after the same threshold.

ExplicitHermiteLawUnderInputs additionally proves the entire explicit
fixed-height Hermite part of main19.1: every fixed h>=3 has original-law
rate h/(h+1) and exactly the same moving TV equivalent as its quadratic
reference. Actual independent-Poisson Hermite probabilities are supplied
by the earlier unconditional construction. The unconditional quadratic/
Hermite error has power4/3 and is negligible on every first omitted
height. Main19.1 nevertheless stays IN_PROGRESS: its exact-parameter
Hermite error4/3 still needs the unproved optimal exact-reference upper
bound. No optimal Hermite lower bound is asserted.

P1-MATH-0151 records the weaker dependency of this whole fixed-height
hierarchy and explicit reference completion: the already proved first
quadratic rate1 plus actual pair-profile remainders suffice. The optimal
triple arithmetic, exact quadratic4/3 upper bound, and the stronger
homogeneous nonaligned main18.2 statement remain open and independent
of this completion. This is not a proof of those missing statements.

The same existing finite geometric properties remain ordinary explicit
arguments: normalized curve count, ordinary surface cover and chosen-
source surface cover. No BCN, new literature input, manuscript byte edit,
dependency download, Paper C port, hidden axiom or Palomar registration
is introduced. Coverage increases from87 unconditional35 conditional
to87 unconditional38 conditional; confirmed improvements151.

Verified under Lean v4.36.0-rc2: full build passed (13837 jobs); direct axiom audit passed for 10816 declarations using only propext, Classical.choice and Quot.sound; all 9288 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 12.09 GiB.


## Complete homogeneous weighted nonaligned pair statement

Main Lemma18.2 is complete conditionally, including its literal
HOMOGENEOUS rank-weight sum and actual covariance consequence:

  sum_(ordered regular separated nonaligned)(2^rho-1)<=N^(1+epsilon),
  sum_(same ordered pairs)|q(x,y)-p_x*p_y|<=N^(-1+epsilon).

The first statement is proved for the actual effective relation nullity,
without any compatibility filter or actual probability weight. A separate
exact regular-rank identity also expresses it with the arithmetic full
source rank deficit pairLoss=2L-rank(S_x+S_y). The literal source population
regularPairs uses both actual regular-start memberships, the strict
integer absolute separation |x-y|>L, and the source nonalignment predicate.
No affine-incompatible or zero-joint-probability pair is discarded.

The proof composes already established arithmetic results, rather than
introducing a new geometric estimate. NonalignedSourceResidualUnderInputs
already bounds the GENUINE positive arithmetic weight2^pairLoss-1 over
ANY actual dyadic nonaligned ordered family, including all local kernels.
It is not a bound merely on compatible probabilities. Effective relative
nullity is at most that full source loss, and equals it on regular starts.
Fixed smaller margins and constant absorption give the source homogeneous
bound after one common threshold. This closes the previously missing
statement/population bridge in the main18.2 ledger row.

PairRankCovarianceBound additionally proves the exact finite inequality
for EVERY actual two-element original family e at positive length:

  |c(e)| <=prod_(x in e)p_x * (2^rho(e)-1).

If any marginal is zero, its actual centered coefficient is zero. If the
joint is positive, the exact affine formula gives equality. If the joint
is zero but both marginals are positive, nullity cannot vanish by exact
direct factorization. Thus2^rho-1>=1 and bounds its negative coefficient.
This handles incompatible pairs explicitly and retains heterogeneous
marginals. No joint compatibility premise is imposed.

In fact uniform_families proves BOTH the homogeneous bound and actual
covariance bound for EVERY finite ordered distinct nonaligned dyadic
family, even without regularity or a separation restriction. It uses the
unconditional actual marginal cap M/N, multiplies the genuine finite
homogeneous sum by (M/N)^2, and proves the exact power cancellation.
Specializing to the original regular separated population gives all
source conclusions. The rank-deficit specialization proves the exact
agreement of both rank conventions on that population.

One finite parameter bundle uses the SAME chosen-source surface,
ordinary two/three-radical surface and normalized-curve properties,
at sizeCap(epsilon/32). Its choice precedes N, every critical L and
EVERY actual finite ordered family. No target rank sum, covariance bound,
BCN premise, new literature theorem or global axiom is supplied.

This is a proof assembly and exact scope extension of the already
recorded P1-MATH-0113 weighted arithmetic source improvement. It does not
create a new improvement identifier. The stronger fixed-height hierarchy
already completed independently remains valid; main18.2 now also has
its own exact homogeneous source statement. The asymmetric compressed
profile T1.10, optimal triple41/30 and optimal exact-reference law upper
rate remain open. Main18.2 moves from not_started to conditional;
coverage is87/167 unconditional and39 conditional, with151 confirmed
improvements. Original source bytes, dependency pins and the later
Palomar milestone are preserved.

Verified under Lean v4.36.0-rc2: full build passed (13841 jobs); direct axiom audit passed for 10823 declarations using only propext, Classical.choice and Quot.sound; all 9297 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 12.07 GiB.


## Actual divisor auxiliary polynomials, before component counting

The auxiliary-polynomial construction in companion T8.1 is now
unconditional. T8.1 remains IN PROGRESS: the final nonlinear-curve point
count, O(B^(1/2+delta)) bound and little-o(B) conclusion remain open.

DivisorAuxiliaryPolynomialUniform.uniform_polynomial fixes d>=1 and
N0>=2 after C,tau>0 and fixed integers A,K>=1, BEFORE every N, critical
L, index TYPE, integer bases x,y, offset family(s_i,t_i) and composite
divisors g_i. The assumptions are |x|,|y|<=A*N, |s_i|,|t_i|<=K*(L+1),
pairwise coprimality, g_i>=N^tau, and divisibility of x+s_i,y+t_i.
The conclusion supplies an ACTUAL NONZERO rational polynomial P, with
both partial degrees<=d and total degree<=2d, vanishing at EVERY offset.
No index-cardinality bound, primeness or nonalignment is needed for
this construction. Fixed real comparison constants can be majorized
by integer A,K; nonalignment is needed later for the line count.

The (d+1)^2 rectangular monomials have quadratic dimension and linear
degree. choose_degree fixes 2d<tau*((d+1)^2-1), then absorbs all fixed
factorials and logarithmic powers into half the positive gap.
Replacing one integer evaluation row by the row at(-x,-y) produces a
determinant divisible by every OTHER g_i and hence their coprime
product. Its natural absolute value is bounded by
M!*X^(2d)*(B^(2d))^(M-1), M=(d+1)^2: the exceptional height X is paid
for once. All replacements vanish. The literal Cramer identity and
constant coordinate1 force every maximal evaluation minor to vanish.
The span/annihilator proof constructs nonzero coefficients and P,
rather than assuming them. Casts, row operations, determinant heights,
degree bounds and evaluations are checked. The generic annihilator
works over every field; its integral variant clears denominators of
a rational kernel to give a nonzero integral kernel.

The finite indexed divisor bound also keeps all point multiplicities:
pairwise coprime g_i>=N^tau dividing nonzero n with |n|<=N^beta have
cardinality<=beta/tau for N>1. If a*s_i+b*t_i=c, each g_i divides
a*x+b*y+c. This yields the same line cardinality bound when that
integer is nonzero and has the prescribed height. Deriving those two
line hypotheses uniformly from the source geometry remains pending.

No new unproved input or additional Paper C port is introduced. The
previously attributed logarithmic-factor bound is reused from its
existing checked P1 module. No numbered completion or new improvement
identifier is added:87/167 unconditional,39 conditional,151 confirmed
improvements. Dense primitive triples, dense nonaligned pairs, optimal
triple activity and the optimal quadratic upper rate remain open.
Original manuscript bytes, dependency pins and the Palomar milestone
are preserved.

Verified under Lean v4.36.0-rc2: full build passed (13857 jobs); direct axiom audit passed for 10850 declarations using only propext, Classical.choice and Quot.sound; all 9328 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 12.04 GiB.
