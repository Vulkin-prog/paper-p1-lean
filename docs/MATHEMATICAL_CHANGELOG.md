# Mathematical corrections and improvements

Baseline: original P1 V1.6 article and companion, 31 October 2026, preserved in
`manuscripts/paper-p1/v1.6/`. This log is separate from the original package's
historical reviews and editorial revisions.

**Ten mathematical improvements are confirmed; no error in a manuscript conclusion
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
