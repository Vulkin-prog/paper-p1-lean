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

## Proved split-product bound

Stable ID: `P1-ARITH-SPLIT`. Status: **proved**.

- Target: companion T1.1, `p1:arith:runge`, page 5,
  `companion_sections/arithmetic_appendix.tex:19`.
- Scope: every `d = 2k ≥ 2`, real `R ≥ 1`, distinct integer shifts bounded
  in absolute value by R, integer `U ≥ 2R`, and an integer-square product.
  Conclusion `U ≤ (64R)^d`, with an absolute constant independent of degree.
- Lean theorem: `PaperP1.SplitProductBound.uniform_split_product_real_radius`.
- Inputs: proved finite binomial/formal-series identities, integral
  coefficient scaling, cancellation, integer-square separation, and the
  integral-polynomial root height bound. Exact Paper C source identities
  are recorded in the reuse ledger. Mathlib's compiled Cauchy root bound
  (`Polynomial.IsRoot.norm_lt_cauchyBound`,
  `Analysis/Polynomial/CauchyBound.lean`) is used at Mathlib commit
  `9d581dfff2e41de989072ea63abf3daf69311520`.
- The manuscript cites Munsch et al., Lemma 3.3, for the antecedent fixed-degree
  argument. No proposition from that reference is assumed by the Lean proof;
  the cited paper's statement has not been used to discharge a proof obligation.
- Degree dependence is fully explicit in the intermediate height estimate.
  This resolves T1.1 itself. The quadratic-equation count is resolved below;
  the determinant, remaining defect and local-rigidity inputs are separate
  obligations.

## Proved coefficient-uniform quadratic count

Stable ID: `P1-ARITH-PELL`. Status: **proved**.

- Target: companion T1.2, `p1:arith:pell`, page 5,
  `companion_sections/arithmetic_appendix.tex:62`.
- Quantifiers: for each fixed real A₀ > 0 and ε > 0, there exists N₀; for
  every N ≥ N₀ and every positive A,C and nonzero e with
  A,C,|e| ≤ N^A₀, the exact positive-solution count in the N^A₀ box is ≤ N^ε.
- Lean theorem: `PaperP1.UniformQuadraticCount.uniform_quadratic_equation_count`.
  Its exact floor-height membership equivalence is separately proved.
- Source comparison: [Tao, arXiv:2603.27990v3](https://arxiv.org/html/2603.27990v3),
  §2.5, Lemma 2.10 and proof; [Cilleruelo–Garaev,
  arXiv:1007.1526v2](https://arxiv.org/pdf/1007.1526v2), §3, Lemma 4 and
  Proposition 1. The primary statements and the polynomial-height substitution
  were inspected. See [exact alignment](QUADRATIC_COUNT_ALIGNMENT.md).
- Proof inputs: internally proved finite ideal-divisor and unit-orbit bounds,
  squarefree reduction, conductor descent, and elementary divisor
  subpolynomiality. Exact Paper C blobs are recorded in the reuse ledger.
  Standard quadratic-field, ideal-factorization, trace/norm and Pell-unit
  facts come from compiled Mathlib at
  `9d581dfff2e41de989072ea63abf3daf69311520`.
- No theorem from either cited paper is an unproved premise. No
  Nicolas–Robin estimate, fixed-discriminant constant, squarefree coefficient
  assumption or class-number bound remains in the final statement. The
  determinant estimate and the remaining local/transformation parts of T1.3 remain
  open. Its global defect-count conclusion is now proved.

## Proved defect-count ingredients

Companion T1.3 remains **in progress**. The finite Chebyshev estimate and
weighted defect/Euler-product estimates are ported from exact Paper C sources,
with no literature assumption. Mathlib's `primorial_le_four_pow`
(`NumberTheory/Primorial.lean`) is a proved library input at the pinned
commit. The new global theorem
`PaperP1.GlobalDefectCount.global_defect_count_le_rpow_eventually` proves the
actual positive-set count ≤ N^(1/2+ε), with a threshold before all H,X in the
stated logarithmic/linear ranges. The two-defect count is now also proved by
explicit finite configurations and the proved T1.2 theorem. The new uniform
prime-support estimate, polynomial support heights and exact dyadic-window
reindexing are proved in P1, with no new literature assumption. See
[two-defect alignment](TWO_DEFECT_ALIGNMENT.md) and
[partial statement alignment](DEFECT_COUNTS_ALIGNMENT.md) for what remains.

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

## Checked infinite-cylinder infrastructure

The infinite prime-sign model and its finite restrictions use compiled Mathlib
results at the same pinned commit, with probability and measurability supplied
explicitly:

| Fact | Mathlib source | Role |
|---|---|---|
| `MeasureTheory.Measure.uniformOfFinset_apply` | `Probability/Distributions/Uniform.lean` | Normalize the two-point coordinate measure |
| `MeasureTheory.Measure.infinitePi_map_restrict` | `Probability/ProductMeasure.lean` | Identify every finite coordinate marginal of the infinite product |
| `MeasureTheory.Measure.pi_map_piCongrLeft` | `MeasureTheory/Constructions/Pi.lean` | Reindex observed prime coordinates |
| `MeasureTheory.integral_map` | `MeasureTheory/Integral/Bochner/Basic.lean` | Transport every actual finite-cylinder expectation |

These are proved library inputs. They supply no arithmetic counting bound or
asymptotic estimate. The no-constant-tail result uses only finite cylinders,
their masses tending to zero, and prime/square evaluations.
