# Companion T1.1: degree-uniform split products

Original locator: companion V1.6, page 5, Lemma T1.1,
label `p1:arith:runge`,
`companion_sections/arithmetic_appendix.tex:19`.
The source block and its SHA-256 remain unchanged in the coverage ledger.

## Statement

Let `d = 2k ≥ 2`, let the integer shifts `γ : Fin (2k) → ℤ` be
injective, and suppose `|γ_i| ≤ R`, `R ≥ 1`. For an integer `U ≥ 2R`,
a square value of `∏ (U + γ_i)` implies `U ≤ (64R)^(2k)`.

`PaperP1.SplitProductBound.uniform_split_product_real_radius` proves this
statement with **real radius R and integer base U**. The supporting natural
radius/base theorem is `uniform_split_product`. The floor of the real radius
contains every integral shift, and the base is proved nonnegative before
conversion to a natural number. No rounding factor enters the final constant.

All degrees are quantified in the theorem. There is no degree-dependent
constant, asymptotic qualification, or external counting hypothesis.

## Algebraic proof

Write `G(T) = ∏ (T + γ_i)`, and let `c_m` be the coefficient of the
formal product `∏ (1 + γ_i z)^(1/2)`. Finite weak compositions give

`|c_m| ≤ 2^(m+d) R^m`, and `2^d c_m ∈ ℤ` for `m ≤ k`.

Set `D = 2^d`, `P(T) = Σ_(m≤k) c_m T^(k-m)`,
`A = DP ∈ ℤ[T]`, and `Q = D²G - A²`. The formal series identity
proves cancellation of the top `k+1` coefficients, hence
`deg Q ≤ k-1`. Distinct roots of G imply `Q ≠ 0`.

The new degree-weighted coefficient estimates prove

`H(Q) ≤ (k+1) 2^(5d) R^d ≤ (64R)^d`.

If `G(U) = a²`, then `Q(U) = (Da)² - A(U)²`. When this is nonzero,
separation of integer squares gives `|Q(U)| ≥ D|a|`. Each factor
`2(U+γ_i) ≥ U`, so `2^k |a| ≥ U^k`. Consequently,

`2^k U^k ≤ |Q(U)| ≤ k H(Q) U^(k-1)`.

Since `U ≥ 1`, `k ≥ 1`, and `k ≤ 2^k`, cancellation gives
`U ≤ H(Q)`. When `Q(U) = 0`, the integral-root height bound gives the
same conclusion. This proves exactly the manuscript's constant 64.

## Provenance and validation

The formal-series coefficients, integral truncation, squarefreeness and
high-coefficient cancellation are adapted from the exact Paper C snapshot
recorded in [PAPER_C_REUSE.md](PAPER_C_REUSE.md). The new weighted height
estimate, integer-square argument, real-radius transport and final theorem
are new P1 proofs under Lean v4.36.0-rc2.

This proof supplies the simplification tracked as
`P1-MATH-0002`. It neither relies on nor verifies the original analytic
tail estimates. Their replacement preserves the full statement and constant.
No original manuscript file has been edited, and no unproved literature
proposition occurs as a premise.

The theorem and all supporting proved declarations are included in
`Audit.lean`. A successful full build and actual axiom audit permit only
`propext`, `Classical.choice`, and `Quot.sound`.

