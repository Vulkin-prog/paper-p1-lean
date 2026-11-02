# Actual fixed-order dependent mass and bounded count moments

Sources: main 6.3, the bounded-moment clause of main 6.4, and moment transfer in main 3.1. The sharp expansion in main 6.4 is **in progress**.

Actual fixed-order dependent-family mass is now bounded under the existing
explicit BCN premise. For every fixed r and eta>0, uniformly for critical L
and every G contained in the dyadic block,

    sum_(I subset G, |I|=r, rho(I)>0) P(all starts in I active)
       <= N^(-1/2+eta)

for all sufficiently large N. The argument does not assume this bound.
Every dependent I contains a primitive seed D of size between 2 and r.
Canonical injective enumerations transport actual unordered families to the
already proved ordered-tuple propagation theorem, with an explicit r! position
factor. Their joint masses are exactly those of the original infinite measure.
The zero masses of incompatible seeds are retained; no regularity or positivity
restriction is imposed. A finite cover over all seed sizes is taken before N.

More generally, every actual family of size s+k containing a seed from a
finite s-site seed family F has joint mass at most

    (s+k)! * N^eta * sum_(D in F) P(all starts in D active).

This propagation statement is unconditional and keeps the full actual seed
mass. BCN is used only for the primitive two-site mass needed in the final
coarse dependent-family estimate.

An unconditional finite decomposition then proves, with the exact
heterogeneous mean mu=sum_x p_x,

    E(Z_G)_r <= mu^r + r! * dependentJointMass(G,L,r).

The direct families have exactly their actual product marginals, and the
nonnegative elementary-symmetric inequality bounds their total. Under BCN,
for every fixed r and eta>0 this gives

    E(Z_G)_r <= mu^r + N^(-1/2+eta).

The critical mean is uniformly bounded. Hence every fixed factorial moment
and every fixed ordinary moment of the original count is uniformly bounded.
The passage to ordinary moments uses the checked finite integer inequality

    n^r <= (2*r)^r + 2^r * n.descFactorial(r),

including r=0. No moment hypothesis, Poisson-law approximation, small coupling
error, or large-order estimate is used to deduce these bounded moments.
The already proved regular-count transfer now has its higher-moment premise
discharged under BCN, yielding, for every fixed j>=1,

    |E Z_N^j - E Z_regular^j| <= K * N^(-1+eta).

Main 6.4 moves from not_started to in_progress: its bounded-moment clause is
proved under explicit BCN, but its two-sided factorial/ordinary expansions,
quadratic correction, sharp 4/5 remainder and all higher factorial cumulants
are not asserted. Main 3.1 retains its previously proved aligned scope;
the new moment-transfer consequence is conditional only on BCN. Numbered
coverage remains 77/167 (main 28/73, companion 49/94), confirmed improvements
remain 88. No new external input, axiom, dependency download, source-byte
change, or Palomar registration is introduced.

Verified Lean v4.36.0-rc2 full build (10789 jobs), actual Audit.lean kernel audit (6636 declarations; only propext, Classical.choice, Quot.sound), 4353 direct ledger/finding declaration checks, 138 source manifest entries and all 167 original statement hashes. Ubuntu root free space: 15.49 GiB. Unordered actual seed propagation is unconditional; fixed dependent-mass and original moment bounds use only the existing ordinary explicit BCN premise. All moment orders and finite seed-size covers are fixed before N. Main 6.4 is in progress: bounded original moments are proved under BCN, but no full sharp moment expansion is claimed. Coverage 77/167 (main 28/73, companion 49/94); confirmed improvements 88.
