# External mathematical inputs

No literature proposition is currently encoded as an assumption in the initial
Lean module. The arithmetic and analytic input inventory is **not complete**.
The paper's claims of unconditionality remain manuscript claims until their
inputs and proofs have been accounted for.

For each later input record: stable ID, exact reference and locator, full
statement, coefficient and degree dependence, quantifier order, uniformity,
Lean type, uses, and status (`proved`, `mathlib`, `explicit_hypothesis`, or
`unresolved`). Include the exact upstream commit for Mathlib results.

If a literature result is intentionally left unformalized, pass it as an
ordinary explicit theorem argument and state that conditional scope in the
coverage and Palomar metadata. Do not introduce a global `axiom`, and do not
describe a theorem conditional on an external estimate as having proved it.

Start with the cited sources behind the split-product, quadratic-equation,
determinant and local rigidity bounds in companion T1 and article Section 2.
Compare the stronger uniformity required here with the exact interfaces in
Paper C; importing an old interface alone cannot discharge this comparison.
