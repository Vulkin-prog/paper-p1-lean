# Exact original once/all coupling and optimal transport

Source: companion_sections/limits_appendix.tex:659-767, and arithmetic_appendix.tex:1199-1210.

The finite probabilistic coupling assertions of companion T19.10 are now
proved for the ACTUAL ORIGINAL once-erased and good-isolated count laws:
0 <= beta-r <= E[(Xi)_2]/2, TV <= E[(Xi)_2]/2 and W1 <= E[(Xi)_2].
No arithmetic estimate for the target second moment is a premise of
these exact finite inequalities. T19.10 remains IN PROGRESS only for
its numerical O(a_N^2) conclusions, which still require the sharper
positive two-good-edge upper bound of T1.17. Numbered coverage remains
87/167 unconditional and46 conditional.

FirstWasserstein defines the usual discrete transport infimum on N.
A plan is a nonnegative matrix with the prescribed probability rows
and columns, and summable cost mass(i,j)*|i-j|. The matrix has summable
total mass exactly one. The real-valued infimum explicitly requires
the existence of a finite-cost plan; it is never used on an empty
cost set. Its nonnegativity and comparison with every plan are proved.
For ANY pair of finite observations of the same sample, finitePlan
is their literal joint mass matrix. Its row and column marginal
identities and exact expected absolute cost are proved.

FirstWassersteinTests proves absolute summability and exact marginal
identities for ANY integrable real test under EVERY transport plan.
Every one-Lipschitz test gives a lower bound for the transport cost
and for the infimum. The attained total-variation test is one-Lipschitz
on N, giving TV <= W1 with the probability convention for TV.
FirstWassersteinFinite applies the identity test to prove that ANY
finite ordered coupling W<=Z is optimal, with W1=E[Z]-E[W]. These
lower bounds are proved for all competing transport plans; no
optimality or distance comparison is assumed.

FiniteOnceAllCoupling proves the pointwise natural-count inequalities
with the exact constants: the disagreement indicator is at most
(k)_2/2 and the absolute count cost is at most (k)_2, for the actual
active-edge count k. The two deterministic observations share the
same finite binary field and the same arbitrary finite probability.
Their actual TV and transport bounds follow without independence.

OnceAllOriginalCoupling constructs the actual original sample plan.
Its factorialCost_eq_second identifies the finite expectation with
the infinite prime-sign second factorial moment; factorialSecond_eq_joint
identifies that moment with the ordered distinct-edge union joint sum.
good_bounds has all three literal T19.10 inequalities with constants
one half, one half and one. The once law is the genuine previously
constructed uniform-deletion count law, identified EXACTLY with the
deterministic observation Z-2*1_(some good edge active); the other law
is the genuine original all-good-edge isolation law.

OnceAllMeanCost proves, UNCONDITIONALLY for every H,N,L, the sharper
identity W1=actual once mean-actual isolated mean. Thus the natural
coupling is optimal. It also proves the order of the actual means
and TV <= their difference. This is improvement P1-MATH-0159 and can
be added to the future statement or proof of T19.10.

OnceAllCouplingUnderInputs uses only the EXISTING coarse connected
geometry to prove BOTH E[(Xi)_2] <= N^(-1+epsilon) and the SUM of
the activation correction, TV and W1 <= N^(-1+epsilon), uniformly
over ALL real H in the critical band. Parameters4 are chosen first
and their accuracy is epsilon/16. At the source H=8(L+1), one fixed
accuracy1/96 gives uniform little-o of the first-order pair scale
L*N^(-2/3). This provides another direct check that the sharper
O(a_N^2) estimate is not needed for first-order once/all transfer.
The sharp rate4/3 and the asymptotic E[(Xi)_2]=beta^2+o(beta^2)
remain open in T1.17; the rate-one statement does not establish them.

All geometric premises are exactly the already recorded ordinary
chosen-source surface covers, ordinary surface covers and normalized
curve estimates, inside the existing finite coarse bundle. No target
estimate, global axiom or new external property is introduced.
No Paper C port, dependency download or original manuscript edit occurs.
Palomar remains a later milestone.

The JSON rows and mathematical finding record exact verification and proof commits.
