# Disjoint recovery — article Lemma 6.1

**Status: in progress, not a completed numbered result.** Source: article
V1.6, page 21, `main_sections/fixed_moments.tex:30`, label
`p1:fixed:recovery`. Exact statement SHA-256:
`18db139a0bd9ab77f064acb65b950ad41adfc0ba3ee9dba623584d8600e83131`.

## Proved subspace and multiplicity conclusions

`DisjointRecoverySubspace.exists_small_recovery_subspace` constructs an
actual subspace M in an arbitrary finite-dimensional vector space U over
any field K. For any finite family `L:V→Dual K U`, d≥1 and t≥2, it proves

`codim(M)≤2 card(V) t^(-1/d)`.

No nonzero form on M has t representations by pairwise disjoint coordinate
sets of sizes between one and d. The definition quantifies over every
nonzero dual form, not just those already present as a coordinate label.
`coordinate_multiplicity_le` proves that each nonzero coordinate form on
M occurs at most t−1 times. Specializing U to the manuscript's actual R
and L to coordinate evaluation gives these two original conclusions.

The field and the finite family need not be binary or separating. This
generalization is `P1-MATH-0013`, presently scoped to these proved clauses.
The final independent-label representation count is still open, so the
entire source lemma remains in progress.

## The constructed history and deterministic rank certificate

`exists_maximal_history` constructs a finite history of independent new
directions. Each step records actual t disjoint recovery sets and the
corresponding equalities modulo earlier directions. Prefix span dimension
equals history length, bounding the possible length by dim U. A finite
maximum gives a history with no remaining bad recovery. No assumed greedy
output or stopping-space existence is an input.

For each coordinate selection A, a successful step lies in the span of its
selected labels plus earlier directions. Induction proves that all history
directions lie in the selected-label span plus the failed directions.
The resulting pointwise inequality is

`history length≤card(selected coordinates)+number of failed steps`.

`RecoveryRankCertificate.pointwise_rank_certificate` proves this from the
recorded algebraic recoveries. The deterministic premise of the separate
sampling interface is therefore discharged before constructing M.

## Exact finite sampling

`FiniteBernoulliSubset` constructs the actual product weights on Boolean
selections. Their mass is one and their positivity is proved. Every fixed
subset has inclusion probability u^card, and the expected selected size is
card(V)u. For disjoint recovery sets, finite product expansion proves the
exact failure probability `prod_j (1-u^card(A_j))`; it is not assumed from
an independence slogan. It is at most `(1-u^d)^t`.

The literal parameter is u=t^(-1/d). Its positivity, upper bound one and
identity u^d=1/t are proved. Elementary Bernoulli's inequality proves
`(1-1/t)^t≤1/2`. Averaging the pointwise rank inequality gives the source's
constant two with no independence assumption between different steps.
The annihilator of the stopped dual span has the required exact codimension;
dual restriction transports its stopping property to every nonzero form on M.

## Remaining obligation and a candidate improvement

The last source conclusion bounds independent j-term label representations
by j!t^(j−1), for 1≤j≤d. It has not yet been formalized. The displayed
source proof suggests the sharper j!(t−1)^(j−1), by retaining its exact
maximal-disjoint-family bound. This is a candidate under examination,
not a confirmed improvement or proved theorem at this checkpoint.

## Inputs and validation

All probability weights, recovery probabilities, rank budgets, history
maximality and the stopping subspace are proved internally. Mathlib at
`9d581dfff2e41de989072ea63abf3daf69311520` supplies finite sum/product
identities, Bernoulli's inequality, finite-dimensional rank and dual
annihilator identities. No literature proposition, target codimension
bound or pointwise rank certificate is assumed in the subspace theorem.
No additional Paper C proof is ported.

The full Lean v4.36.0-rc2 build passed (8,787 jobs), followed by the actual
axiom audit of all 1,874 project theorem/lemma declarations. Only `propext`,
`Classical.choice` and `Quot.sound` occur. Completed coverage remains
25 / 167. No Palomar registration is made.
