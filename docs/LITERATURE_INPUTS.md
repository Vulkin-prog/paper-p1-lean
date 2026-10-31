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
  the determinant and local-rigidity inputs are separate
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
  determinant estimate remains open. T1.3 and the complete local-rigidity
  specialization are proved below.

## Proved defect-count ingredients

Stable ID: `P1-ARITH-DEFECT`. Status: **proved**, full companion T1.3,
`p1:arith:defects`, page 6, `companion_sections/arithmetic_appendix.tex:90`.

The finite Chebyshev estimate and
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
[complete statement alignment](DEFECT_COUNTS_ALIGNMENT.md). The new uniform
prime budget and B/log B conversion prove the full local rate. Exact positive
integer-point definitions, rounded endpoint bounds and injective shifted
starts prove the fixed real affine versions. The complete
`UniformDefectCounts.companion_T1_3_run_length` and
`companion_T1_3_run_length_fixed_affine` declarations choose the local
constant before the error exponent and a common threshold before every
cutoff, interval and length. No arithmetic estimate is an unproved premise.

## Local rigidity: proved code bound and sharp prime asymptotic

Stable ID: `P1-CODE-GRIESMER`. Status: **proved**.
Reference: J. H. Griesmer, *A Bound for Error-Correcting Codes*, IBM Journal of
Research and Development 4(5) (1960), 532–542, Section 2, equation (2.10),
DOI [10.1147/rd.45.0532](https://doi.org/10.1147/rd.45.0532);
[original article](https://bitsavers.trailing-edge.com/pdf/ibm/IBM_Journal_of_Research_and_Development/045/ibmrd0405M.pdf).
The binary linear-code bound and the prefix redundancy form for every t≤r
are proved internally in `PaperP1.GriesmerBound`. The residual construction
is proved in `PaperP1.BinaryResidual`. No external proposition is assumed.
The arithmetic application uses the proved T1.1, with the exact `64B` scale.

Stable ID: `P1-ARITH-PNT`. Status: **proved**.
For every real η>0 there is B₀≥2 such that every integer B≥B₀ satisfies
`primeCount B ≤ (1+η) * B / log B`. The sequential limit
`π(B) log B / B → 1` is also proved, with the exact inclusive prime count.
There is no coefficient or degree parameter. The public declarations are
`PaperP1.SharpPrimeCount.primeCount_upper_eventually` and
`PaperP1.SharpPrimeCount.prime_counting_ratio_tendsto`.

Primary statement reference: Avigad, Donnelly, Gray and Raff,
*A formally verified proof of the prime number theorem*, ACM TOCL 9(1),
Article 2 (2007), DOI
[10.1145/1297658.1297660](https://doi.org/10.1145/1297658.1297660),
[preprint](https://arxiv.org/abs/cs/0509025), introduction, page 1.
Its explicit inclusive-prime-count limit agrees with the required convention.
The checked Lean proof below is independent of that Isabelle proof.

The selected Lean proof source is
`AlexKontorovich/PrimeNumberTheoremAnd`, commit
`127b50e33f6033e2147921167a117af96d9ba4ea`, Apache-2.0, Lean 4.35.0.
`WeakPNT` in `Wiener.lean` and `pi_alt'` in `Consequences.lean`, together with
their selected function-space, Fourier, cutoff and asymptotic dependencies,
are recompiled and audited under Lean 4.36.0-rc2 and the pinned Mathlib.
The unused unfinished bounded-variation decay block is excluded; the actual
proof uses the proved W21 Fourier estimates. Source blobs, scopes, licences,
statement comparison and version adaptations are recorded in
[PRIME_NUMBER_THEOREM_ALIGNMENT.md](PRIME_NUMBER_THEOREM_ALIGNMENT.md).
Mathlib's analytic continuation and nonvanishing facts are compiled inputs
at `9d581dfff2e41de989072ea63abf3daf69311520`. The historical Paper C PNT
interface is an unproved proposition and is not used as evidence or a premise.
No literature theorem is left as an unproved assumption in this PNT chain.

The exact finite inequality, all uniform asymptotic specializations and actual
relative-sign independence of article Lemma 2.1 are now proved. See
[local rigidity alignment](LOCAL_RIGIDITY_ALIGNMENT.md), including the weaker
base hypothesis and the exact critical-band marginal consequences.

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

## Regular-set transfer: no additional external input

Main Proposition 3.1 is now proved using the internal T1.3 two-defect count,
full local rigidity and exact affine probabilities. Finite coupling, moment
truncation and the complete second factorial-cumulant identity are proved
internally. The source's bounded-fixed-moments premise remains an ordinary,
explicit mathematical hypothesis only for the conditional moment-transfer
clauses; no literature theorem or target transfer estimate is assumed.
It may hold just along one prescribed length sequence. See
[regular-set alignment](REGULAR_SET_ALIGNMENT.md).

## Local square threshold and critical defects

Companion T9.1 is proved directly from the internal T1.1 split-product bound,
with the stronger threshold recorded in `P1-MATH-0005`. Companion T9.2 is a
specialization of the proved T1.3 local count with cutoff 10B; the absolute
constant quantifier is recorded in `P1-MATH-0006`. No new external theorem,
analytic truncation estimate or admissibility premise is assumed. See
[alignment](LOCAL_SQUARE_THRESHOLD_ALIGNMENT.md).
