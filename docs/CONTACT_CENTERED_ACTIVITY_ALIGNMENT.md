# Actual fixed-order centered contact activity

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
