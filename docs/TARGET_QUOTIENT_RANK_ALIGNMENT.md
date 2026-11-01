# Actual finite target quotient rank — partial T2.6 and T1.11

Primary source: companion T2.6, page 22, `p1:arith:fixed-channel-rank`,
`companion_sections/supplemental_arithmetic.tex:209`, statement hash
`8dd614c19e50df20ed1eb9f3ab37c07386f1ce3665c3499e26d83211ceab60b9`.
The same bridge is used in T1.11, page 15, `p1:arith:palmrank`,
`companion_sections/arithmetic_appendix.tex:861`, statement hash
`f5c10336a982eb463bd69da026b36971a8d8bbede48fd0ad27463a97cfe6a307`.
Both numbered asymptotic rank statements remain **in progress**.

## Literal old/new values and actual deficiency

Write U=b*V_x union a*V_y, deduplicated as before, and set

    S=c*U,       T=a*b*d*V_z.

`ScaledTargetValues.oldValues`, `newValues` and `allValues` are exactly
these true finite sets and their union. Their intersection has cardinality
exactly `ActualNormalizedMatches.exactOffsets.card`; this is a proved
bijection on actual target positions. The total union has at most 3B
values, where B=L+1.

One actual source unit and positive coefficients/labels give

    evenSpace(S)=S_x+S_y,       evenSpace(T)=S_z,       |T|=B.

No private-source coordinate or local regularity is used. For any finite
prime-coordinate set Q, let W=(S_x+S_y)+primeSpan(Q).
`TargetWindowRank.deficiency` is the paper's actual dimension expression

    delta_Q = L - (rank(W+S_z)-rank(W)).

Its kernel characterization is proved by rank--nullity on the actual
zero-sum target domain of dimension L. It therefore includes internal
target rank deficiency. With Q empty the literal source formula is proved
by `deficiency_empty`.

## Generic finite relative-rank inequality

For any map f from actual finite values into a vector space over any
division ring, `FiniteSetRelativeRank.matches_add_residual` proves

    dim{zero-sum target selections mapping into span(f(S))}
      <= |S intersect T| + dim ker(full value map on S union T).

The proof uses the full value-map rank identity, finite union
inclusion-exclusion, and the fact that the full target image is generated
by its zero-sum image and one anchor. The larger full old-value span is
used only for an upper bound. No old value absent from S is inserted into
the match count, and no position count is equated with rank loss.

## Deleted prime rows and added old prime information

`MaskedParityRank.project P` deletes exactly the coordinates in a finite
set P. Its actual full-value kernel equals the literal row solution space
`CoverGraphResolution.rowSolutions (PrimeRowComponents.rows (S union T) P)`.
The generic finite relative bound is proved after this projection.

If Q is contained in P, every old prime-coordinate generator in Q maps to
zero. The old even-value space maps into the full projected old-value
span. `ProjectedOldInformation.relative_kernel_le_masked` proves the
actual kernel inclusion, giving the finite bound even with those old
prime signs exposed. In particular Q may be primeFactors(a*b) whenever
that set is contained in P.

`TargetWindowRank.finite_bound` combines these steps on the actual source
and target windows:

    delta_Q <= card(actual matching positions)
                 + rank(literal remaining-row kernel on S union T).

It needs positive coefficients, complete-window values >=1, one actual
source unit and Q subset P. It needs no source private coordinates,
local regularity, compatibility or separation. This weakening concerns
the finite rank step; it does not remove hypotheses from the source-mass
or Palm arguments. The finite bridge is P1-MATH-0041.

`TargetWindowRank.interior_bound` then uses the proved separated matching
estimate to give

    delta_Q <= B*gamma_{a:b}+3+rank(remaining-row kernel).

Its matching hypotheses include reduced positive c,d, coprime source
slopes, strict interior fraction, actual affine source/target identities
and deterministic target/source separation. Actual positive joint mass
can provide that separation.

## Finite and uniform residual estimates available

The component proof is strengthened from the full value kernel to the
actual solution space after all rows in P are removed. Thus
`ResidualComponentRank.row_rank_sublinear` and
`TwoProgressionSublinear.row_rank_sublinear` prove uniform o(B) under
the stated true-subset, width, height and prime-budget conditions.
`MaskedParityRank.finite_loss_bound` gives the explicit finite
matches-plus-Runge--Hamming bound under its literal row-size and growth
conditions. None of these estimates is assumed as an external theorem.

## Remaining application to the numbered statements

The geometry of the actual combined target union S union T still needs
to be connected to the already proved two-progression residual theorem.
The construction of polynomially bounded affine target data from the
paper's geometric alignment predicate also remains unfinished. The
finite actual quotient-rank and old-prime-information bridges are now
closed; their full asymptotic application is separate work. T1.11 and
T2.6 are not counted complete.

No new Paper C source, external mathematical hypothesis, manuscript
revision or Palomar registration is introduced. Original source bytes
are preserved.

Validated finite target quotient-rank checkpoint and P1-MATH-0041:
[469f5ac7ab234cdd18962337291971682554d913](https://github.com/Vulkin-prog/paper-p1-lean/commit/469f5ac7ab234cdd18962337291971682554d913).
