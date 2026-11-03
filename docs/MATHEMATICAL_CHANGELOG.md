# Mathematical corrections and improvements

Baseline: original P1 V1.6 article and companion, 31 October 2026, preserved in
`manuscripts/paper-p1/v1.6/`. This log is separate from the original package's
historical reviews and editorial revisions.

**106 mathematical improvements are confirmed; no error in a manuscript conclusion
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
The r=4 case remains open, so main 15.5 stays in progress. Companion
T4.3 also retains its r=3 and ordered nominal-population obligations.
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
