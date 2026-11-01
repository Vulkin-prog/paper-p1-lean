# Article Proposition 13.7 — rank on a known alignment

Source: article 13.7, page 33, `p13:rig:aligned`,
`main_sections/pair_rigidity.tex:331`, original statement hash
`f35f1d523724f58d47358f9401d9a7d7ac65506632395e176199769a7b446a1e`.
All three assertions are proved. Original manuscript bytes are unchanged.

## Literal rank and stronger pair deficiency

`FreeComponentRank.pairIntersectionRank x y L` is exactly
finrank(S_x intersect S_y), the source d_xy. The full pair deficiency
`NormalizedPairRankLoss.pairLoss` is 2L-rank(S_x+S_y), so it includes
internal local deficiencies and dominates d_xy. All new bounds apply to
this stronger quantity and therefore to d_xy.

`KnownAlignmentRank` uses the literal enlarged alignment
|b*x-a*y|<=(a+b)B with positive coprime coefficients and max(a,b)<=B^3.
Both coefficient orientations are covered by the proved T1.9 wrapper.
All critical-band thresholds precede every channel and pair choice.

## Fixed tau and the first displayed estimate

The actual T1.9 residual already gives, for every positive epsilon,

    pairLoss <= L/max(a,b)+epsilon*B.

For a fixed tau in (0,1), choose epsilon=(2/3)*log(1/tau)>0.
Since L<=B, `quantitative_bound` gives eventually

    pairLoss, d_xy <= B/max(a,b)+(2/3)*B*log(1/tau).

Thus the original fixed-tau estimate holds with zero additional error
after a tau-dependent threshold. No assertion uniform as tau tends to
one with N is made. This avoids needing a quantitative residual rate
of B/sqrt(log B): the positive fixed extraction margin absorbs o(B).

## Height one, exact contact and the uniform half bound

Actual compatibility of distinct centres implies separation by at least L.
Their true complete windows share at most one actual value, including
contact at distance exactly L=B-1. At a=b=1, the exact unit cardinality
is this actual intersection cardinality. `height_one_units` proves u<=1.
The all-case T1.9 estimate pairLoss<=(u-1)_++epsilon*B therefore proves

    pairLoss, d_xy <= epsilon*B.

This covers zero units, exact one-position contact and local defects.
For reduced height at least two, L/max(a,b)<=B/2. Combining the two
cases proves the uniform compatible B/2+o(B) assertion.

`main_13_7` packages `QuantitativeConclusion`, `HalfConclusion` and
`HeightOneConclusion` with their literal actual ranks and full pair losses.
The compatible event used here is the actual infinite-prime-sign joint
moment; deterministic separation is derived from a common realization.

## Proof simplification and scope

The original known-line proof used short-basis extraction, two
norm-polynomial witnesses and line substitution. Those inputs are
unnecessary for this conclusion once T1.9 is available. The replacement
is recorded as P1-MATH-0042, explicitly as reuse of the already proved
residual rather than an independent new residual theorem.

The nonaligned rank bound, triple theorem and algebraic curve-counting
inputs remain separate unfinished work. No new external mathematical
hypothesis, Paper C port, manuscript revision or Palomar registration
is introduced.

Validated complete article 13.7 and P1-MATH-0042 (9,311 build jobs;
3,349 audited declarations; 1,064 directly checked coverage/finding names):
[0b7945eff438d61604f6a3aea0bc33f7263372e9](https://github.com/Vulkin-prog/paper-p1-lean/commit/0b7945eff438d61604f6a3aea0bc33f7263372e9).
