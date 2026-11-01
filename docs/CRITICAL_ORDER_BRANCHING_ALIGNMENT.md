# Companion T22.4 — Independent extensions at growing critical orders

Source: Proposition T22.4, page 90, `p1:uniform:branching`,
`companion_sections/uniform_appendix.tex:147`, statement SHA-256
`b66fbd94f42d758ee34a11221126ad2e532d7a82d09218eef646acd5be6e0468`.

`CriticalOrderBranching.companion_T22_4` proves the original assertion
under the original infinite prime-sign measure. For every fixed K>0 and
critical-band constant C, one positive error constant, one deterministic
envelope Dstar and one threshold precede N, every j<=K*H/h, every
critical-band L and every old source set of cardinality at most j.
Here H=log N and h=log H. The result includes

    log Dstar(N) <= (2/3)H - H*log(h)/(9h) + c*H/h.

The entire new relative vector is exactly fair and independent of the
entire vector of old raw values outside a deterministic exceptional
set of cardinality at most Dstar(N). Every realizable old observation
also has the exact nominal conditional probability for every new word.
Repeated source windows cause no difficulty: the exposed raw-value set
is a finite image and its size bound is proved internally.

## Prime budget and variable tilt

`CriticalBranchingBudget.raw_budget_le_cubic` proves the actual pool
budget from the old windows, without assuming the desired count. Its
coefficient is A(K)=1+upperScale*(log 4+2K), which is at least one.
The budget is Y=A(K)*H^3/h. `CubicLogTilt` proves, for a sufficiently
large H uniformly after K is fixed, that sigma=1-h/log Y belongs to
[3/5,3/4] and Y^(1-sigma)=H exactly.

The finite inequality

    h/log Y >= 1/3 + (log(h)-log(A))/(9h)

is proved by multiplying by the positive denominator. The resulting
identity has remainder -(log(h)-log(A))^2/(9h). It gives the literal
negative coefficient 1/9 in the manuscript; no asymptotic expansion
is assumed. The internally proved T22.3 Rankin estimate and elementary
width estimates then prove the envelope, with the explicit positive
constant `CriticalBranchingBudget.errorConstant K`.

## Exact independence and exceptions

The proof uses the two-supported-value exception set already validated
in P1-MATH-0030. Twice its size is at most B times the actual supported
integer count. At most one supported value leaves the conditional
relative kernel zero, so even a retained contact has the full exact
independence statement. A separate overlap deletion is unnecessary.
The earlier improvement validation is retained in its own ledger entry.

This theorem does not bound all factorial moments at growing orders
and does not prove the principal Poisson approximation theorems.
No target estimate, external mathematical assumption, new Paper C
port or Palomar submission is introduced.

## Validation

The full Lean v4.36.0-rc2 build passed (9,095 jobs). The actual audit
passed for all 2,777 theorem/lemma declarations, permitting only
`propext`, `Classical.choice` and `Quot.sound`. All 647 distinct
coverage/finding declaration names were checked directly by Lean.
Source checks passed for all 138 manifest entries and 167 original
statement hashes. Coverage is 43 / 167: main 15 / 73, companion
28 / 94. The 30 confirmed improvements retain their earlier validation
commits. Original source bytes are preserved. Ubuntu-root space is
17.85 GiB.

Validated implementation of companion T22.4:
[c5334aa55a0c179a93747cf2d3d6820d575b78dc](https://github.com/Vulkin-prog/paper-p1-lean/commit/c5334aa55a0c179a93747cf2d3d6820d575b78dc).
