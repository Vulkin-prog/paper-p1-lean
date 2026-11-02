# Refined coarse pair and conversion rates with explicit BCN input

The literal original nonaligned family now has a finite positive host
bound. Every nonzero covariance is represented by an ordered increasing
nonaligned full-loss host. A joint cap M gives

    A_nonaligned <= #hosts * M + independent_host_mass.

The representation includes locally irregular sites, zero marginals and
affine incompatibility. It does not assume pairwise independence or a
positive covariance sign. Zero-loss pairs are removed only after their
actual centered coefficient has been proved zero.

With exactly the existing explicit BCN premise
PlaneCurvePointCount.UniformBound c kappa, c>0, put
s=(2/3) log 2. The already checked nonaligned joint cap N^(-2+s+delta)
and unconditional host count N^(1+delta) give

    A_nonaligned <= N^(-1+s+epsilon).

Independently, the complete aligned family satisfies the unconditional
bound A_aligned <= N^(-2/3+epsilon). Its cutoff can be chosen internally
as H=8(L+1), so this statement has no free private-prime cutoff.

The exact aligned/nonaligned partition therefore gives, under the same
explicit BCN premise and uniformly over every deterministic subset G
of the original dyadic block,

    A_2(G) <= N^(-1+s+epsilon),
    |alpha(G)| <= N^(-1+s+epsilon),
    ||B_2(G)-Q(actual mean, actual alpha)||_1 <= N^(-2+s+epsilon).

The exact single-site square diagonal is retained in alpha. Since
1/3 <= s < 1/2, these improve the previous coarse -1/2 activity/cumulant
and -3/2 conversion exponents by the strict gap 1/2-s. The first two
exponents are approximately -0.5379, and the conversion exponent is
approximately -1.5379. This is the analytic conversion of the finite
second-order reference, not an error bound for the complete count law.

All parameters c, kappa, C and epsilon are fixed before the common
threshold; lengths and deterministic subsets vary afterwards. BCN is an
ordinary theorem argument, not a new kernel axiom or an internally proved
external result. No stronger unformalized input is introduced.

These are intermediate rates, weaker than the source's sharp -2/3 pair
rate and -5/3 conversion rate. They do not establish the weighted dense
nonaligned estimate or finish main 3.3, 3.4, 15.1 or T7.1. All four
remain in progress; T1.8 stays not started. Coverage stays 77/167
(main 28/73, companion 49/94), and confirmed improvements stay 94.
No original manuscript edit, dependency download or Palomar registration
is introduced.

Verified under Lean v4.36.0-rc2: full lake build (11031 jobs), source and ledger checks, actual axiom audit of 7025 declarations (only propext, Classical.choice and Quot.sound), and 4742 direct ledger/evidence declaration checks; Ubuntu root free space 15.03 GiB. Original manuscript bytes and all 167 statement hashes preserved.
