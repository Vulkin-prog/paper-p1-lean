# P1 version 1.8 working revision

Version 1.8 integrates the selected recommendations of the independent
mathematical/editorial review at source 2553ce56f7cc6bdc10194801c3d926b72b587dd1.
The article has 65 pages and the companion 104. All 167 numbered-result labels
and actual typeset numbers are retained. Versions 1.6 and 1.7 are preserved.

The two necessary v1.7 corrections, T1.10 and T5.1, are unchanged. The following
seven blocks differ from v1.7; these are optional strengthenings or a notation
clarification, rather than additional false-original statements.

| Result | Version 1.8 integration | Proof correspondence |
|---|---|---|
| 3.2 | Both ordered-pair profiles have exponent 1+epsilon instead of 6/5+epsilon. The early elementary estimate is distinguished from the later proof. | NonalignedSourceResidual.uniform_source_bounds |
| 7.4 | Star bound for every nonnegative activity, including heterogeneous vertex weights. | MarkedGraphGenerator.polynomial_star_bound; GraphStarWeights.heterogeneous_generating_bound |
| 13.5 | Upper degree envelopes allow a=0 and need no lower growth. | QuadraticGrowingDegreePlaneCount.article_13_5 |
| 15.5 | All fixed primitive sizes r>=3 have rank mass N^(-r/2+epsilon); dense families have N^epsilon hosts and mass N^(1-r+epsilon). | SharpPrimitiveMass; DensePrimitiveRankMass; DensePrimitiveHosts |
| 16.1 | The first quartic identity has error N^(-5/3+epsilon); the signed-to-positive error remains N^(-3/2+epsilon). | FourthCumulantIdentities.article_16_1 |
| 20.1 | The independent reference law is consistently H; the original full-grid weighted 4/5 rate and fixed-degree regime are retained. | IndependentPositionalApproximation.main_20_1 and its canonical realization |
| T19.6 | Probability <= exp(-2log^3 N) for every b>=N^(9/10); near-linear thresholds work for every fixed c>0. | VerySmallTail.power_threshold plus NearLinearThreshold.threshold_ge_power |

The lower bound for the Poisson correction coefficient is also doubled to
exp(-lambda)/2. It is an unnumbered consequence recorded separately.

The companion now gives the fixed-arity anchored support construction and its
recovery/erasure argument before applying it to primitive hosts. The smooth
census is next to its use in T19.17; the cylinder refinements follow T19.7;
reference marginals, covariance, block independence and the bivariate mass
formula accompany the positional comparison. The formalization appendix is
limited to revision scope and reproducibility. The exact-rank refinement S07
remains optional and is not asserted: the example retains the checked bound
rank<=10. A subsequent [Lean certificate](EXACT_RANK_EXAMPLE.md) at
checkpoint0999 proves exact rank 10, two forcing samples and mass 2^-10;
this remains an optional source edit and does not change the frozen draft. The Gaussian census exposition summarizes the existing internal
analytic chain; this revision does not claim a new general short-average theorem.

Eighteen unnumbered scientific claims have their own source-bound proof
correspondence. Checkpoint P1-MATH-0998 exposes the two individual anchored
kernel caps that were previously internal to the product-bound proof. Its
public endpoint gives distinct actual natural window values, uniformly over
all physical relation spaces and cutoffs satisfying the printed assumptions.
This is a proof-interface extraction, not a new scientific bound.

The [full checkpoint replay](validation/checkpoint-0998/validation.json) at
c07b036aed5a9310d4f79f816969e45a20628138 passed 18,617 build jobs, 19,957
theorem axiom checks and 19,880 distinct declaration references, with all
three actual exits zero. Only propext, Classical.choice and Quot.sound occur.
The separate [compiled-type extraction](validation/manuscript-v1.8/compiled-types-validation.json)
checked 528 declarations and audited its 485 propositions. All proof sources
and compiler/dependency pins are bound by a complete manifest.

The [source correspondence](manuscript-v1.8-revision.json) records objects,
hypotheses, quantifiers and exact compiled-type hashes for all seven changes.
The checker also validates all 18 auxiliary correspondences. Eleven positive
and negative source/metadata controls reject missing claims, changed types,
unreviewed comparisons, source escapes and a kernel axiom substituted for a
manuscript theorem. This is AI-assisted semantic comparison, distinct from
an independent human review.

Both PDFs rebuilt with shell escape disabled and stabilized after three rounds.
All 167 numbers were checked in the actual auxiliary files. All 169 pages were
rendered and inspected in 12 contact sheets; 27 complete selected pages were
inspected at 110 dpi. No overfull boxes, unresolved references, missing glyphs,
clipping or overlap were found. The [validation record](manuscript-v1.8-validation.json)
states the exact scope of that review.

Palomar submissions remain on hold at the user's request. The six prepared
configurations and their 68 selections retain their earlier exact types and
local qualification sources. No new selected target or registration is claimed.
