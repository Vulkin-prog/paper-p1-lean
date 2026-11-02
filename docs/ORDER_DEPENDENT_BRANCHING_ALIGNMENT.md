# Companion T19.4 — Order-dependent branching and the initial pair moment

Source: Lemma T19.4, page 69, `p1:limits:branching`,
`companion_sections/limits_appendix.tex:190`. Statement SHA-256:
`6057533a131360cb3c57f28e780d053e295b563e1426341d720c8ffb0d700afb`.
The source bytes are preserved. The full result is now **conditional** on the single named field-polynomial BCN input. The finite branching and first rate remain unconditional. The uniform bounded seed is derived under that input; it is not an additional assumption. This result is outside proved coverage.

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

## Complete conditional growing-order conclusion

The missing bounded second-moment seed and the full growing-order
source conclusion of companionT19.4 are now proved under the single
ordinary explicit field-polynomial BCN input already used for13.5,
13.6 and13.8. The deterministic exception, actual infinite-model
independence, first logarithmic rate and recurrence remain unconditional.
The result is conditional and adds no proved numbered coverage.

`SecondMomentPairCap.finite_bound` splits actual ordered pairs into
zero-full-loss pairs and the actual full-loss hosts. The zero-loss
contribution is at most N^2*(2^(-L))^2, with actual affine deficiencies
handled by the proved zero-loss implication. The remaining contribution
is at most the actual host cardinality times a bound for actual distinct
pair joint probabilities. This is an unconditional finite theorem;
the asymptotic pair cap is discharged in the next step, not assumed
as a completed conclusion.

The proved host bound with epsilon=1/8 and the conditional pair joint
bound with epsilon=1/8 give an exceptional contribution at most

    N^(1+1/8)*N^(-3/2+1/8) = N^(-1/4) <= 1.

The nominal critical mean is at most2^C. Consequently
`BoundedSecondMomentUnderBCN.uniform_bound` proves the explicit actual
seed F_2<=(2^C)^2+1, uniformly before every critical length. This does
not assert that actual heterogeneous marginals equal the nominal one.
No weighted residual estimate, bounded pair moment, independence
premise or fixed-order extrapolation is supplied as an input.

`OrderDependentMomentsUnderBCN.uniform_source_growth` combines this
seed with the existing actual recurrence and absorbs its fixed
constant into the exponential, obtaining

    F_k <= exp((k-2)*H/2 + K_C*(k*h+k^(3/2)*H/h))

simultaneously for every2<=k<=H, where H=logN and h=logH. The positive
K_C is chosen before the BCN constants c,kappa; these affect only the
eventual threshold. The absorption uses h>=1 and the actual order
range, with all real powers and denominator signs proved. This
implies the source statement, including its allowed fixed prefactor.

The external BCN proof and its geometric-to-plane-polynomial
presentation remain unformalized. T19.4 is therefore conditional,
with exactly the same named BCN input, and remains outside proved
coverage77/167 (main28/73, companion49/94). No additional external
input or new mathematical finding is introduced. P1-MATH-0030 retains
the unconditional smaller exception improvement. Confirmed findings83.
No Paper C port, manuscript-byte change or Palomar registration.

## Validation

Lean v4.36.0-rc2 full build passed (10587 jobs); actual axiom audit passed for all 6074 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 3791 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records remain intact. Ubuntu available space: 15.81 GiB. The bounded actual seed F_2<=(2^C)^2+1 and complete T19.4 growing-order source conclusion are proved under the existing single field-polynomial BCN input. The positive exponential constant precedes the BCN constants; those affect only the threshold. Finite branching and its smaller exception remain unconditional. T19.4 is conditional and adds no proved coverage. Coverage77/167 (main28/73, companion49/94); confirmed findings83. No additional unformalized input, Paper C port, dependency download, manuscript-byte change or Palomar registration.
