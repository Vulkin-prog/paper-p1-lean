# Mathematical corrections and improvements

Baseline: original P1 V1.6 article and companion, 31 October 2026, preserved in
`manuscripts/paper-p1/v1.6/`. This log is separate from the original package's
historical reviews and editorial revisions.

**Twenty-five mathematical improvements are confirmed; no error in a manuscript conclusion
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
