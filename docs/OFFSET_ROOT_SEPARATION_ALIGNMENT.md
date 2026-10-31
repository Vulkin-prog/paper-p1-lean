# Offset-root separation — companion T20.5

**Status: proved in full.** Source: companion V1.6, page 83,
`companion_sections/offset_geometry.tex:192`, label `p1:offset:root-separation`.
Exact statement SHA-256:
`465917147676dcae0ce62fd66ee88a0eb70874be3aacb04120c5ab5a6b4f772b`.

## Actual square classes and regularity

`TwoPointSquareClasses.pairSelection` is the actual even selection of two
physical coordinates. Its image is the sum of their prime-parity vectors.
The effective rank L implies injectivity of the even-selection map by
rank-nullity; this is proved in `injective_evenMap_of_rank`. Thus two distinct
coordinates in a regular window give a nonzero even square class.

If n1*m2=n2*m1 for positive actual values, multiplicativity of prime parity
proves that the even class of n1,n2 equals that of m1,m2. Membership in each
actual `squareClassSpace` is proved from the selections. A nonzero such
class is impossible when those two spaces are disjoint.
`no_proportional_pairs` uses injectivity only for the first window.

## Exact rational roots

The physical offset is u-1 for u in Fin(L+1). `leftRoot` is its negative;
`rightRoot` is -(beta+offset)/alpha. Both root lists are injective within
their respective block when alpha is nonzero. `vertex_cast_value` proves
the exact correspondence with the actual positive window values.

For y=alpha*x+beta, a common root gives
`y+offset(v)=alpha*(x+offset(u))`. Two matches give the cross-product
identity for actual natural values. The nonzero common even class then
contradicts directness. `commonRoots_card_le_one` bounds the intersection
of the entire window root lists, so every selected pair of lists is covered.
No small-window or asymptotic approximation is used.

## Deleting at most two equations

If there is a common root, choose its two physical offset coordinates,
one from each window. Otherwise choose the empty set. The exceptional
coordinate set H has cardinality at most two, and the actual combined root
map is injective on its complement; both facts are proved.

For a finite family of pairwise disjoint physical equation supports,
`DiscardTouchedSupports` chooses the equations touched by H. Choosing one
touched coordinate in each such support is injective, so the number of
discarded equations is at most card(H), hence two. Every retained support
avoids H. This is an actual constructed deletion set, without an assumed
exceptional-equation bound.

## The actual substituted polynomials

`OffsetRootPolynomials.polynomial alpha beta S` is the product of the actual
factors Z+offset(u) from the first window and alpha*Z+beta+offset(v) from
the second. `polynomial_eq_split` identifies each factor with its nonzero
leading coefficient times Z-root. The product leading coefficient is a unit.

The proved injectivity on each retained support makes the monic root product
separable and hence squarefree, using the compiled Mathlib theorem.
Multiplication by the nonzero constant preserves squarefreeness.
`isRoot_iff` identifies every root of the actual polynomial with a physical
coordinate in its support. If two retained polynomials shared a root,
injectivity off H would give a common coordinate in their disjoint supports,
a contradiction. Thus the exact remaining polynomials are squarefree and
have pairwise disjoint root sets.

## Source statement and improvement

`companion_T20_5` retains both regular-window assumptions of the source,
positivity, the nonzero rational slope, the line relation and directness.
It proves the common-root bound and the constructed deletion of at most two
equations, including polynomial squarefreeness and disjoint roots.
`root_separation` needs only first-window regularity. `P1-MATH-0019`
records this weakening for the entire lemma. The original conclusion is
preserved, with no error or optimality claim.

## Inputs and validation

No additional Paper C source is ported. Existing P1 parity and even-selection
proofs are reused. Mathlib at `9d581dfff2e41de989072ea63abf3daf69311520`
supplies rank-nullity and separability of products of distinct linear factors.
All value, root, support-count and actual-polynomial identities are proved.
No root bound, deletion theorem or squarefreeness conclusion is assumed.

The full Lean v4.36.0-rc2 build passed (8,847 jobs). The actual axiom audit
passed for all 2,038 project theorem/lemma declarations, with only
`propext`, `Classical.choice` and `Quot.sound`. Coverage is 31 / 167:
11 main results and 20 companion results. No Palomar registration is made.

All 313 distinct coverage/finding declaration names were checked directly by Lean.

Validated implementation of companion T20.5 and P1-MATH-0019:
[9fac0fbf1971b9145acd77ce72f3e6e42cbfedfc](https://github.com/Vulkin-prog/paper-p1-lean/commit/9fac0fbf1971b9145acd77ce72f3e6e42cbfedfc).
