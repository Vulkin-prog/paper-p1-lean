# Original-model active principal edges and their probability exponent

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
