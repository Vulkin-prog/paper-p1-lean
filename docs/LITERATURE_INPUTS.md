# External mathematical inputs

No literature proposition is currently encoded as an unproved assumption in the
Lean development. The arithmetic and analytic input inventory is **not complete**.
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

## Checked measure-theory infrastructure

The general probability-space version of Proposition 4.1 uses already-proved
Mathlib facts at the pinned commit
`9d581dfff2e41de989072ea63abf3daf69311520`:

| Fact | Mathlib source | Role |
|---|---|---|
| `MeasureTheory.sum_measureReal_singleton` | `MeasureTheory/Measure/Real.lean` | Normalize finite observation weights |
| `MeasureTheory.map_measureReal_apply` | `MeasureTheory/Measure/Real.lean` | Identify actual event probabilities |
| `MeasureTheory.integral_fintype` | `MeasureTheory/Integral/Bochner/SumMeasure.lean` | Identify finite weighted expectation with Bochner integration |
| `MeasureTheory.integral_map` | `MeasureTheory/Integral/Bochner/Basic.lean` | Transport expectations through the measurable observation |
| `MeasureTheory.Measure.ext_of_singleton` | `MeasureTheory/Measure/Dirac/Basic.lean` | Identify the full count pushforward measure |

These are compiled library theorems, not literature assumptions passed as
unproved premises. Probability normalization, measurability and finite-measure
integrability are supplied or proved explicitly in the P1 modules.
