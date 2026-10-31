# Companion T1.2: coefficient-uniform quadratic counts

Original locator: companion V1.6, page 5, Lemma T1.2,
label `p1:arith:pell`,
`companion_sections/arithmetic_appendix.tex:62`.
The original statement and SHA-256 remain in the coverage ledger.

## Statement and quantifiers

`PaperP1.UniformQuadraticCount.uniform_quadratic_equation_count` proves:

For each fixed real `A₀ > 0` and each real `ε > 0`, there is a natural
threshold `N₀` such that for every `N ≥ N₀`, **all** positive natural
coefficients A,C and nonzero integer e with

`A,C,|e| ≤ N^A₀`

have at most `N^ε` positive integer solutions of

`A u² - C v² = e, u,v ≤ N^A₀`.

The coefficient quantifiers follow the threshold. This is the precise
uniform meaning of the manuscript's `N^{o_(A₀)(1)}` upper bound.
There is no squarefree, coprimality, fixed-discriminant or nonsquare-ratio
assumption in the final theorem.

`positiveQuadraticSolutions` is an actual finite set of integral pairs,
with its cardinality in the conclusion. The box uses `floor(N^A₀)`.
`mem_positiveQuadraticSolutions_real_height` proves that this is exactly
the literal real-height restriction on positive integer coordinates.
The ceiling of A₀ is used only to invoke an intermediate polynomial-box
bound; it does not alter the solution set.

## Two arithmetic branches

When AC is square, a natural r satisfies `AC = r²`. The equation gives

`(Au-rv)(Au+rv) = Ae`.

For positive u,v, the sum Au+rv is positive and is an integral divisor of Ae.
This sum determines the other factor, and hence the original pair. Thus

`#solutions ≤ τ(|Ae|)`.

When AC is nonsquare, the injective substitution `(u,v) ↦ (Au,v)`
produces `x² - AC y² = Ae` in a polynomial-height box.
The internally proved squarefree reduction, maximal-order ideal-divisor
count, conductor descent and unit-orbit estimate give a finite envelope

`4 τ(|Ae|)² · pellUnitOrbitEnvelope(polynomial height)`.

The orbit factor is explicitly logarithmic. A proved elementary divisor
estimate and proved absorption of fixed logarithmic powers turn the
envelope into `N^ε`, with one threshold for every coefficient in the box.
No fundamental-unit or class-number estimate is supplied as an assumption.

The ideal-divisor envelope counts divisors of the principal ideal (Ae),
which yields a square of the rational divisor count. The manuscript instead
describes ideals of a prescribed norm and a single divisor factor. The
formal proof's coarser finite envelope has the same stated subpolynomial
conclusion. This is a valid proof route, not an assertion that the two
intermediate counts coincide.

## Source comparison and provenance

Primary references inspected:

- [Tao, arXiv:2603.27990v3](https://arxiv.org/html/2603.27990v3),
  Lemma 2.10 and proof, §2.5. The displayed equation uses the opposite
  orientation for the shift; replacing its h by -e gives our orientation.
  Its one-coordinate box also contains the paper's restricted two-coordinate
  box after changing the fixed polynomial exponent.
- [Cilleruelo–Garaev, arXiv:1007.1526v2](https://arxiv.org/pdf/1007.1526v2),
  §3, Lemma 4 (PDF pp. 5–7), with Proposition 1 as a more general conic
  formulation. The substitution above gives its nonsquare equation, with
  polynomially bounded coefficients and coordinates.

These references supply context and a statement comparison; no theorem from
them is an unproved argument of the Lean result. The proof route is adapted
from the immutable Paper C snapshot and its elementary subpolynomial
development, with precise blob identities and selected scope in
[PAPER_C_REUSE.md](PAPER_C_REUSE.md). Historical literature interfaces and
stronger exp(log N/log log N) endpoints are excluded from this port.

The new P1 code supplies the square branch, combines both branches, counts
the exact positive solution set and transfers to the literal real exponent.
Every proved dependency is rebuilt under Lean v4.36.0-rc2 and included in
the actual 655-declaration kernel-axiom audit. Only propext, Classical.choice
and Quot.sound are permitted.

