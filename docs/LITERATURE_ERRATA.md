# External-reference errata verified during the formalization

This file concerns cited literature. The two confirmed false literal P1 statement scopes remain recorded separately in `MATHEMATICAL_CHANGELOG.md` and the numbered-result ledger. Original manuscript files are preserved byte for byte.

## BCN normalized derivative recurrence: mixed-term sign

- Reference: Binyamini--Cluckers--Novikov, arXiv:2302.04209v2, Section 4, Proposition 8, equation (21). Both the [official HTML](https://arxiv.org/html/2302.04209v2) and [official PDF](https://arxiv.org/pdf/2302.04209v2) were checked.
- Finding: expanding the stated normalized operator `L_x = partial_x - (P_x/P_y) partial_y` requires `-P_y P_x partial_y(N)` in the numerator recurrence. The displayed recurrence prints this mixed term with a plus sign.
- Exact corrected form: with `L_P=P_y partial_x-P_x partial_y`, the next numerator is `P_y L_P(N) - e N L_P(P_y)`, with `e=2j-1` at derivative order `j>=1`.
- Checked counterexample: `P=x+y+xy`, `Q=y`, at `(0,0)`. The point lies on the curve and `P_y=1`. The corrected second numerator is `2`; the displayed plus-sign expression is `0`.
- Lean evidence: `PaperP1.RationalTangentNumerator.step_expanded`, `mixed_term_sign_counterexample`, and `PaperP1.IteratedGraphDerivative.positive_order`, recorded with P1-MATH-0507. Every positive-order actual derivative on an open chart with nonzero denominator satisfies the corrected formula and degree bound.
- Scope: this is a typo in an intermediate external formula. The corrected recurrence preserves the polynomial degree allowance. This entry does not refute the BCN theorem or any additional P1 numbered statement. No author contact or external issue submission has been made.
