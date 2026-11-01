# Dependent block pairs — main Corollary 10.3 complete

`DependentBlockPairsCount.article_10_3` proves the literal critical-block
version of main Corollary 10.3, `main_sections/half_counts.tex:100`.
`uniform_logarithmic_count` proves the bound for every fixed logarithmic
signed-distance width, with no critical-length input required.

## Actual pair set

`DependentBlockPairs.pairs` is the actual finite set of ordered candidate
centre pairs with a nonzero common vector in their two effective even-
selection images. `dependent_iff_intersection` identifies this predicate
with a non-bottom intersection of those actual submodules. The two block
families can have different finite shapes and fixed normalizations. Their
values satisfy a fixed positive comparable height bound, and their signed
distances from their respective centres have a fixed logarithmic bound.

The threshold precedes every finite candidate-centre set and both complete
block families. Candidate centres need not be given a separate interval or
size bound. Equal centres are included, with their two potentially different
block shapes. Unordered or distinct-centre subclasses inherit the count.

## Instantiated counts

An off-diagonal pair maps injectively to its actual two-coordinate tuple.
The two equal nonzero common vectors sum to zero in characteristic two,
so this tuple belongs to the actual full-support list set with no old
sources. The complete main 10.1 bound is instantiated at r=2, s=0.

A diagonal pair injects into its centre. That centre has a nonzero effective
space in the first block and therefore an actual value in the block.
`ActiveBlockCentresCount.uniform_count` derives its comparable height from
that value and the actual radius, then applies the proved elementary
centre count. It does not bound the whole arbitrary candidate set.

The actual pair set is covered by these two actual classes. With internal
margin epsilon/2, both counts are at most N^(1+epsilon/2); the proved
fixed-factor absorption handles their factor two. The final bound is
N^(1+epsilon), which implies the printed fixed-constant O estimate.
No target pair count is an argument.

## Logarithmic widths and provenance

`LogarithmicBlockGeometry.length` is floor(log(N)/log(2)). Its critical-band
error is proved to be at most one. The proved lower critical scale covers
every width E*logN by a fixed multiple of L+1. This gives the explicit
logarithmic-width version of both 10.1 and 10.3.

No additional external input, Paper C port or manuscript edit is used.
This is a consequence of the completed half-count, with the diagonal
checked explicitly. It introduces no additional independent mathematical
finding. Coverage is now 64/167 (main 21/73, companion 43/94), with 64
confirmed improvements. Palomar registration remains a later milestone.

Dependent-pair verification checkpoint: Lean v4.36.0-rc2 full build passed (9,805 jobs); actual axiom audit passed for all 4,465 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 2,180 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records remain intact. Ubuntu available space: 17.23 GiB. Coverage is 64/167 and confirmed findings remain 64; no new external input, Paper C port, manuscript-byte change or Palomar registration.
