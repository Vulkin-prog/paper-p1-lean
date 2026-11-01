# Companion T19.11 — The scalar recurrence criterion

Source: Lemma T19.11, page 76, `p1:limits:stein`,
`companion_sections/limits_appendix.tex:847`, statement SHA-256
`7e070bb71a29687765ca75f1869a42e82d2ab9acc98731d44928fbff56191eab`.

`ScalarRecurrenceTheorem.companion_T19_11` proves both original
conclusions for arbitrary actual probability laws on the naturals.
The finite-first-moment hypothesis is proved equivalent to Bochner
integrability, and `firstMoment_eq_integral` identifies the mean.
Total variation is exactly half the ordinary sum of absolute singleton
differences. No target residual estimate, stationarity identity,
Stein-factor bound or literature proposition is an input.

## Closed unit Stein factors

`PoissonSteinSolution` constructs the solution by finite partial sums
of the Poisson masses. For every test taking values in [0,1], it proves
the exact Poisson Stein equation, |f(k)|<=1, |f(k+1)-f(k)|<=1 and
f(0)=f(1). These are closed proofs for every positive intensity.

The proof uses finite Poisson balance. If F_k and T_k are the cumulative
and tail probabilities, the two balance inequalities imply
F_k*T_k<=mu*p_k. This bounds the solution itself. The exact two tail
factors F_k/(mu*p_k) and T_k/(mu*p_k) are respectively increasing and
decreasing in k. In the successive-difference kernel all coefficients
except the central one are nonpositive, and their sum is zero. The
central positive coefficient is at most 1. This proves the second
unit bound without an assumed semigroup construction or Stein theorem.

`AtomicTests` proves summability of bounded tests, the unit-test
difference bound and an indicator test attaining total variation.
`RawRecurrence.operator_expectation` proves the exact unweighted
residual identity, with every summability requirement discharged.

## The actual single/double Poisson reference

`HermiteRecurrence.law_eq_product_sum` identifies the reference with
the actual pushforward of a product measure by (u,v)->u+2*v. Both
coordinate laws are proved equal to Mathlib's Poisson measures.
The intensities are mu-theta and theta/2. The construction retains
zero intensities and the full probability law, rather than only
moments or a formally stationary coefficient sequence.

Poisson product summation identities prove the stationary operator
identity internally. Applying the closed Stein solution and absorbing
the perturbation gives exactly

    TV(P,H(mu,theta)) <= R(P;mu,theta)/(1-2*theta).

The source hypothesis 0<=theta<min(mu,1/2) follows directly. The
stronger `scalar_recurrence_criterion_closed` also permits theta=mu
for mu>0 and theta<1/2. This is the pure-double-jump boundary recorded
in P1-MATH-0031; the denominator is unchanged.

## Canonical size bias and actual shifted laws

`SizeBiasedRecurrence.sizeBiased` is a normalized actual probability
law with mass k*P_k/m, where m is the positive finite mean. The
successor law is the actual measure pushforward by Nat.succ.
`shiftMixture_eq_weighted_successors` proves equality of measures
with (1-theta/m)*Law(X+1)+(theta/m)*Law(X+2). The pointwise signed
residual identity gives the exact norm/total-variation identity.

This identity holds for every theta in [0,m], with only a positive
finite first moment. Taking theta=Var(X)-E(X) gives the source
specialization whenever its parameter conditions hold. A variance
and second moment are unnecessary for the general identity. The
unnumbered parameter stability inequality following the source
lemma is also proved, for arbitrary real parameter changes.

## Attribution and limits

The three Paper C Stein modules previously inspected remain unported.
In particular, the positive-intensity input left explicit in
`PaperCV282/ScalarSteinInput.lean` is not imported as an assumption.
The cumulative/tail proof, actual reference construction and size-bias
bridge are new P1 code. See [inspection records](PAPER_C_REUSE.md).
This result alone gives no arithmetic bound for the raw residual of
the multiplicative run count and no principal Poisson asymptotic.

## Validation

The full Lean v4.36.0-rc2 build passed (9,113 jobs). The actual axiom
audit passed for all 2,875 theorem/lemma declarations, permitting only
`propext`, `Classical.choice` and `Quot.sound`. All 672 distinct
coverage/finding names were checked directly by Lean. Source checks
passed for all 138 manifest entries and 167 original statement hashes.
Coverage is 44 / 167: main 15 / 73, companion 29 / 94. There are
31 confirmed improvements; none is integrated into a revised manuscript.
Original bytes are preserved, no Palomar registration is made, and
Ubuntu-root space is 17.82 GiB.

Validated implementation of companion T19.11 and P1-MATH-0031:
[9ca5f8aecbbc79ecd99b0658bf2cb37fa414f842](https://github.com/Vulkin-prog/paper-p1-lean/commit/9ca5f8aecbbc79ecd99b0658bf2cb37fa414f842).
