# Companion T19.6 — A smaller threshold without smooth-pair input

Source: Proposition T19.6, page 70, `p1:limits:colored-tail`,
`companion_sections/limits_appendix.tex:296`. Original statement SHA-256:
`377d9659754253d1c87b71aea548e2b6f20b12f7ff691912355db547ce493e9b`.
The original source bytes are preserved.

`VerySmallTail.companion_T19_6` proves both original inequalities under
the actual infinite prime-sign probability measure. One threshold in N
precedes all lengths in an arbitrary fixed critical band and every
integer moment order 1 <= r <= log N. The source ceiling is literal:
R = ceil(N/L), A = ceil(R exp(-c sqrt(log N log log N))).

The theorem permits every fixed c > 0. It follows from the stronger
`VerySmallTail.power_threshold`: for every real b >= N^(9/10), eventually

    P(Z_N > b) <= exp(-2 (log N)^3),
    E[Z_N^r; Z_N > b] <= exp(-(log N)^3/2),  0 <= r <= log N.

No estimate of ordinary smooth pairs, odd-pivot smooth pairs, or a
conditional dependency graph is assumed. This is P1-MATH-0033.

## Checked proof chain

1. `QuarticLogPrimePool.raw_budget_le_envelope` bounds the actual pool
   of small primes and old raw observations, uniformly after every
   j <= K (log N)^2 windows. Its logarithmic prime budget is bounded by
   (a_K log N)^4. The proved finite Rankin estimate at sigma=3/4 then
   gives N^(3/4+epsilon) supported positive integers, uniformly in
   the pool. Its extra logarithmic exponent is O_K(log N/log log N).
2. `QuadraticOrderBranching.quadratic_order_branching` supplies an
   actual deterministic exceptional set of size <= N^(3/4+epsilon).
   Outside it the entire new relative vector is fair and independent
   of every old raw observation. Those properties are proved by the
   previously checked binary relation criterion, rather than inferred
   from conditional one-dimensional marginals.
3. `JointBranchingEvents.retained_joint_factor` identifies the old joint
   start event as a measurable function of those raw observations and
   proves q(A union {x}) = p q(A) outside the exceptional set. Inside
   it, event inclusion gives q(A union {x}) <= q(A). Consequently the
   extension sum is <= (Np+D)q(A), for every actual old family A.
4. `BranchingTuples.sum_tuple_succ_le` passes this inequality to ordered
   distinct tuples. The erasure encoding is injective, and enlargement
   to all extension pairs is an inequality between nonnegative sums.
   It does not identify repeated-index terms with distinct tuples.
   `FactorialBranching.factorial_le_power` proves the actual finite
   falling-factorial recurrence before choosing a growing order.
5. `QuadraticOrderMoments.factorial_bound` proves, with one uniform
   threshold, F_k <= (2 N^(3/4+epsilon))^k for every k <= K (log N)^2.
   The count and factorial moments are actual infinite-model Bochner
   integrals, connected to finite cylinders by exact equalities.
6. `QuadraticTailScale` chooses k = ceil(128 (log N)^2), K=129 and
   epsilon=1/20. Eventually 2k <= N^(9/10), so the falling-factorial
   Markov bound gives a probability at most
   (4 N^(-1/10))^k <= exp(-2 (log N)^3). The ceiling is included and
   no fixed-order asymptotic is extrapolated to growing k.
7. `CountTailBounds.moment_le_count_power` proves the truncated-moment
   bound E[Z^r; Z>b] <= N^r P(Z>b) directly by finite expectation.
   For r<=log N this yields the claimed cubic-logarithmic exponent.
8. `NearLinearThreshold.threshold_ge_power` proves A >= N^(9/10)
   eventually for every fixed c>0, uniformly in the critical length.
   It uses L<=N^(1/20) and c sqrt(log N log log N)<=log N/20, with
   both source ceilings retained. Monotonicity finishes T19.6.

## Scope

The result controls very rare large counts. It does not prove bounded
second moments, small-count Poisson approximation, the sharper
square-root effective support of T19.5, or the main asymptotic theorem.
No revised manuscript or Palomar registration is produced at this stage.

Validated implementation of companion T19.6 and P1-MATH-0033:
[79e4e6d814ac0dc941544b2beb92437e45657a39](https://github.com/Vulkin-prog/paper-p1-lean/commit/79e4e6d814ac0dc941544b2beb92437e45657a39).
