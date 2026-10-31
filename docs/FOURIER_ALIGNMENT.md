# Article Lemma 4.2: statement alignment

Baseline: P1 V1.6, main article page 18, label `p1:alg:fourier`,
`main_sections/affine_algebra.tex:60`. The unchanged statement hash is in
`manuscript-results.json`.

The checked conclusion is `PaperP1.Model.InfiniteStarts.dyadic_squareClass_fourier`.
It includes the exact identity, both bounds and the existence implication.
All expectations are actual Bochner expectations under the constructed
infinite independent prime-sign measure.

## Dictionary

| Manuscript object | Lean object and identification |
|---|---|
| Window `V_x = {x-1, …, x+L-1}` | `startCompleteVertexLabel x L` on `Fin (L+1)`; for `x>0` its labels are injective and enumerate exactly this interval |
| Even selections | Kernel of `startVertexSum L`; `startVertexSum_eq_zero_iff_even_selection` identifies it with even cardinality of the selected vertices |
| Effective square-class space `S_x` | `squareClassSpace x L`, the image of those even selections under `vertexParityMap` |
| Actual marginal `p_x` | `infiniteMarginal x L`; exact finite-cylinder equality is proved, with no substitution of `2⁻ᴸ` |
| Centered coefficient `c(I)` | `infiniteFamilyCenteredMoment L` on the subtype `I`; `infiniteCenteredCoefficient_subtype` proves equality with the finite-set Bochner product |
| Full-support relative relation | `IsFullSupportRelation (squareClassFamilySpace L g) s`: every component is nonzero and their sum vanishes |
| Relative nullity | `relativeNullity`; `relativeNullity_eq_dimension_deficit` proves it equals `Σ dim S_x - dim (Σ S_x)` |
| Product of affine signs | `squareClassTupleSign`; the supplied local witnesses solve their actual start systems |

## Why the square-class representation is faithful

Every window integer is positive when `x≥2`, as in the paper. Its prime
factorization modulo two records its positive rational square class.
`vertexParityMap_zero_iff_rational_square` proves the exact criterion: a
selection has zero image precisely when the product of its labels is a square
in `ℚ`. This uses the checked natural-factorization criterion and Mathlib's
`Rat.isSquare_natCast_iff`, rather than assuming a square-class relation.
Thus the parity-vector image represents the relevant square-class image,
including every local relation.

`startBoundaryEquivEven` identifies row coefficients with even vertex
selections. `parityPairing` maps their parity vectors to actual linear
characters on the finite prime signs. For a cutoff covering the window,
`parityPairing_injOn_bounded` proves this map is injective on the entire
represented prime-parity subspace. Consequently `squareClassEquivRow`
identifies each local image with the effective affine row space.

The same injection preserves sums across all blocks, not just individual
dimensions. `squareClassRelationEquivRow` is a linear equivalence of the
relative-relation kernels. `relativeNullity_squareClassFamily_eq_rows`
therefore preserves precisely the nullity used in the bounds.

## Affine and probability scope

Positive actual marginals imply compatibility by a proved equivalence.
The selected local witnesses solve those affine systems. Evaluating a
character at such a witness gives the prescribed sign, has absolute value
one, and is independent of the chosen solution. Centering removes the zero
frequency in each block. Uniform character orthogonality leaves exactly the
tuples whose total square class vanishes.

Finite restrictions of the infinite prime-sign measure have exactly the
normalized real uniform weights used in the algebra. Start indicators,
marginals, centered products and the complete count law are transported by
proved measurable restriction identities. No independent-block assumption
is made.

`dyadic_squareClass_fourier` assumes only positive run length, a nonempty
finite subfamily of `[N,2N)`, and positive actual marginals. The cutoff
`2N+L` is proved adequate in its proof. Taking `N≥2` supplies the paper's
positive vertices. The formula and estimates in fact extend to any finite
supported compatible family; that extension introduces no extra premise
in the dyadic application.

## Bounds and remaining scope

Every full-support relation of a nonempty family is a nonzero element of its
relative-relation kernel. That kernel has `2^ρ` elements, so the signed sum
has absolute value at most `2^ρ - 1`, and hence at most `2^ρ`. A nonzero
centered coefficient forces at least one such tuple. These statements are
all checked, including the sharper subtraction of one.

This result supplies no arithmetic estimate for `ρ`, local rigidity, canonical
components, or an asymptotic approximation theorem. Those remain separate
coverage obligations. The compatible-nullity maximum and bound of Lemma 4.3
are now proved separately; see [its alignment note](COMPATIBLE_NULLITY_ALIGNMENT.md).
