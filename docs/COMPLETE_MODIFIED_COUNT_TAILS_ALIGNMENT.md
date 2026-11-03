# Complete modified count in companion T19.3

Source: companion_sections/limits_appendix.tex:132. The original-law coupling rate and all every-order clauses share one threshold.

Companion T19.3 is now COMPLETE CONDITIONALLY, including restoration
from the actual regular-ground count to the full original dyadic count.
The modified count is constructed on the SAME original infinite prime-sign
space: it equals the regular-ground count when its active configuration is
retained at threshold H=8*(L+1), and zero on the actual nonretention event.
The original and modified laws are actual normalized probability measures,
identified with the pushforwards of those random variables.

ModifiedCountAllTailsUnderInputs.companion_T19_3 selects its finite geometric
parameters before their ordinary hypotheses, and ONE threshold before N,L
and EVERY natural tail order k>=1, factorial order r>=1 and real s>=1.
For the actual regular ground G, n=|G|, p=2^(-L) and mu=n*p, it gives ALL
of the source conclusions together:

  TV(Law(full original count),Law(modified regular count))<=N^(-4/5+epsilon),
  delta=P(actual nonretention on G)<=N^(-4/5+epsilon),
  P(regular count>=k)<=mu^(k-1)/(k-1)!+delta,
  P(modified count>=k)<=mu^(k-1)/(k-1)!,
  E s^modified<=s*(1+p*(s-1))^n,
  E s^modified<=s*exp((s-1)*mu),
  E(modified)_r<=mu^r+r*mu^(r-1).

The all-order inequalities themselves were already proved UNCONDITIONALLY
for the actual direct maximum R and shifted envelope R+1, followed by the
pointwise domination modified<=R+1. Their tail probabilities, finite-cylinder
realizations, observable integrability, binomial subset counts and full
nonnegative subset generator are all actual checked theorems. No fixed-order
asymptotic constant is reused at growing order. The exact falling-factorial
shift retains its repeated-index term r*mu^(r-1). Zero means, empty grounds
and orders beyond the ground size are included by those finite results.

OriginalCountLawCoupling.finite_law proves invariance of the actual count
law under every sufficiently large finite observation cutoff. A common
finite cylinder therefore proves the coupling of actual count laws on
arbitrary finite grounds by their actual disagreement probability.
restore_modified composes this with the actual retained-modification
coupling. The existing unconditional regular-ground restoration error is
O_C(N^(-1+epsilon/2)), while the newly completed literal exceptional event
has exponent4/5. Their sum is absorbed uniformly into N^(-4/5+epsilon).
Thus the TV conclusion is for the FULL original count, rather than only
the already regularized count.

The same earlier heterogeneous envelope statements remain valid on ANY
actual finite ground: replace p^|I| by the product of exact p_x, mu by
sum p_x and the binomial generator by product(1+(s-1)*p_x). In particular,
local affine incompatibility and zero marginals were handled explicitly.
The source regular-ground formulas are obtained by the proved exact
regular marginal identity. No exponential estimate for the full original
count on the exceptional event is asserted; the exponential and factorial
tails here concern the constructed modified variable.

The only unproved inputs for the numerical4/5 coupling rate are the same
three finite geometric properties used in the completed T15.2. They occur
as RetainedExceptionalEventUnderInputs.Hypotheses at epsilon/2. No BCN
plane bound or new unformalized property occurs in the completed proof.
Earlier qualitative BCN preparations remain historical declarations; the
new theorem supplies the literal rate and every-order quantifier order.
No new mathematical finding is added: this completes the missing event
and original-law restoration clauses of the existing T19.3 development.
The existing improvement88 in its ledger remains recorded with its
original validation history.

This checkpoint adds2 modules and5 theorems, with no new definitions or
inputs. Coverage is87/167 unconditional and28 conditional, with144 confirmed
improvements. T15.1 sharp separated clauses and the optimal quadratic-law
rates remain open. No original manuscript bytes, Paper C port, dependency
download, hidden axiom or Palomar registration is added.

The JSON T19.3 row records full validation and its exact proof commit.
