# Companion T19.4 — Order-dependent branching and the initial pair moment

Source: Lemma T19.4, page 69, `p1:limits:branching`,
`companion_sections/limits_appendix.tex:190`. Statement SHA-256:
`6057533a131360cb3c57f28e780d053e295b563e1426341d720c8ffb0d700afb`.
The source bytes are preserved. This result is **in progress**.

The finite exception and the first displayed uniform logarithmic rate are
fully proved. The growing factorial-moment exponential factor is also
proved, multiplied by the actual second factorial moment. The remaining
input is a uniform bound for that initial moment; it is not assumed.

## Exact finite exception and independence

Let B=L+1 and let m be exactly the paper's natural ceiling of
pi(B)+j B log(3N)/log B. `PrimeCardinalityEuler` proves, for every finite
prime set P with card(P)<=m, including m=0 and m=1,

    sum_{p in P} p^(-1/2) <= C0 sqrt(m/log(m+2)),
    card(naturalValues(P,X)) <= sqrt(X) exp(C0 sqrt(m/log(m+2))).

The explicit positive constant is C0=2*(4 log 4+64)+8. Split the prime
set at m log(m+2). The low part uses the existing elementary weighted
prime sum and the high part its actual cardinality. No nth-prime bound,
prime number theorem or literature estimate is an unproved input.

`OrderDependentBranching.finite_independence` constructs the actual
deterministic exception set and proves its full infinite-model conclusion
against all old raw sign values. For N>=2 and 1<=L<=N it has size at most

    (B/2) sqrt(3N) exp(C0 sqrt(m/log(m+2))).

The old windows are any subset of the dyadic block, with cardinality at
most j. No fixed-order restriction on j is imposed here. The whole new
relative vector has its fair product law, is independent of the whole old
raw vector, and every realized old word has the nominal conditional word
mass. The smaller set counts only windows with two supported values.
Thus the removal of the separate contact term and the factor 1/2 in
P1-MATH-0030 extend to this sharper Euler estimate. The paper's larger
literal exception D=j(2L+1)+B sqrt(3N) exp(C0 sqrt(m/log(m+2))) is also
a valid bound for this same constructed set.

## Uniform order dependence

`OrderPrimeBudget` bounds the actual ceiling, not a substitute budget:
with H=log N, h=log H and u=1/log 2+1, eventually

    m <= (5u+1) j H^2/h,
    log(m+2) >= h/2,
    sqrt(m/log(m+2)) <= sqrt(2*(5u+1)) sqrt(j) H/h.

These estimates hold uniformly for every j>=1. Their common threshold
depends only on the critical band. `OrderDependentRate.uniform_source_rate`
then proves exactly the first source rate, simultaneously for
1<=j<=H and every critical-band length:

    log(N*2^(-L)+D) <= H/2 + K_C (h+sqrt(j)*H/h).

The nominal mean is used here because the paper defines lambda_N=Np.
No replacement of the exact heterogeneous event marginals is made in a
joint moment or conditional event.

## Actual growing factorial moments and remaining scope

`OrderDependentMoments.uniform_source_growth` proves, with one positive
K_C and one threshold preceding every 2<=k<=H,

    F_k <= F_2 exp((k-2)*H/2 + K_C*(k*h+k^(3/2)*H/h)).

Every recurrence is instantiated using the actual deterministic exception,
the proved infinite-model joint probabilities and the actual falling
factorial moment of the original count. Real k^(3/2)=k*sqrt(k) is proved,
as are the integer subtraction, all denominators, and the order range.

The source replaces F_2 by O_C(1), citing the pair estimate. That bound
remains open in this development. Retaining F_2 is a proved stronger
finite recurrence but does not discharge the missing uniform pair input.
T19.4 is therefore not counted complete. Coverage stays 66/167 and the
confirmed mathematical findings stay 66: this is an extension of the
existing improvement P1-MATH-0030, not a new independent correction.

No source edit, Paper C port, external assumption or Palomar registration
is introduced by this checkpoint.
