# Modified moment decomposition and complete pair leakage, companion T22.6

Source: companion_sections/uniform_appendix.tex:266. All finite and weighted asymptotic clauses are proved for the actual original-model modified count.

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

The T22.6 JSON row and finding147 record the direct full validation and exact proof commit.
