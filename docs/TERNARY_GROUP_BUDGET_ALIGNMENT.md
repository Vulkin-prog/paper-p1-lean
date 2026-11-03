# Companion T1.16: actual ternary group budget

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

The exact validation and proof commit are recorded in the T1.16 JSON ledger entry.
