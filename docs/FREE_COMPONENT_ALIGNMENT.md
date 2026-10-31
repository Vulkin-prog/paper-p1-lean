# Companion T9.3: free components

**Status: proved**, every assertion of the lemma. Coverage is 16 / 167:
8 / 73 main and 8 / 94 companion. Original locator: companion V1.6, page 40,
`p13:rig:components`, `companion_sections/pair_rigidity.tex:129`.
The original statement and source hash are unchanged.

## Exact graph and cutoff

`LargePrimeOccurrences.Occurrence L` is the disjoint union of two copies of
`Fin (L+1)`, labelled by the true complete vertex windows. Overlapping
physical values remain distinct formal vertices. Put B=L+1.

A prime greater than B has at most one odd occurrence in either block,
proved from the private-prime lemma without a valuation-one assumption.
In the P1 graph, `IsLargePrime L p` means p is prime and 10B<p. Edges join
its two occurrences, which lie in opposite blocks; a unique occurrence is
a pin. The occurrence bound explicitly keeps L fixed when deriving B<p
from 10B<p.

`largePrimeSolution` is the actual kernel of these prime-coordinate equations.
Its membership is equivalent to agreement across edges and vanishing at pins.
The checked pinned-graph equivalence gives one free binary value per
unpinned component before the remaining prime and parity constraints.

`LargePrimeGraphResolution` proves exactly

`dim(largePrimeSolution) = D + c`,
`D + 2c ≤ 2B`.

Here D counts defective formal vertices and c counts unpinned components
with at least two vertices. `nontrivial_free_iff_unpinned_edge` proves that
this is exactly the source's free components containing an edge. It is not
a different count of physical labels.

## Actual defective positions and component selection

`LargePrimeComponentArithmetic.isDefective_iff_kernel_one` identifies graph
defectiveness with the literal large odd-prime kernel above 10B being one.
An injective label map and exact image equality give

`D = #criticalDefectivePositions x L + #criticalDefectivePositions y L`.

The proved T9.2 yields `defectiveVertexCount_critical_bound`. One constant
precedes the fixed band width C; only the threshold depends on C.

`solution_constant_on_component` and `component_selected_or_omitted` prove
that every solution assigns zero to every vertex of a component or one to
every vertex. Pinned components take zero. No independence is asserted after
the other constraints are imposed.

`component_has_edge` and `component_card_two_le_of_edge` identify nontrivial
components with those containing an edge. The actual opposite-block
occurrence lemma then proves `free_nontrivial_component_meets_both_blocks`.
Thus both structural assertions in T9.3 are included.

## Complete even relations and their dimension

`Affine.completeRelationCode x y L` imposes the full prime-parity equation
on both formal copies and a separate zero coordinate sum in each block.
These are precisely complete even square relations, before any local
relations have been factored out.

`completeRelationEquivPair` identifies this code with the kernel of addition
from the two actual even-selection maps. The proved generic identity
`finrank_coprod_kernel_eq` uses rank-nullity and the dimension formula for
the sum and intersection of two images. Its specialization gives

`dim(completeRelationCode) = k_x + k_y + d_xy`,

where k_x and k_y are the two actual local kernel dimensions and
`d_xy=finrank(squareClassSpace x L ∩ squareClassSpace y L)`.
This accounts for local defects explicitly and imposes no regularity premise.

## Exact small-prime and block-parity cost

`pairSmallConstraintMap` records the actual parity coordinates at all
π(10B) small primes and the two block sums. Restricting it to
`largePrimeSolution` gives `largeSpaceSmallConstraints`.

`completeRelationEquivConstraintKer` explicitly identifies its kernel with
the complete relation code. For the converse, each prime is either above
10B and already cancelled, or is one of the enumerated small primes. Every
nonprime coordinate is proved zero. No missing-coordinate assumption is used.

The codomain dimension is exactly π(10B)+2. Rank-nullity proves

`dim(completeRelationCode) ≤ dim(largePrimeSolution)`,
`dim(largePrimeSolution) ≤ dim(completeRelationCode)+π(10B)+2`.

These finite inequalities are proved for all x,y,L; they are not passed as
assumptions to the asymptotic theorem.

## Full critical-band comparison

`FreeComponentRank` combines the identities to give d_xy≤c+D. The already
proved critical local-rigidity theorem applies to every dyadic window,
including inadmissible windows, and bounds k_x,k_y by one. Hence

`c ≤ d_xy + π(10B) + 4`,
`|c-d_xy| ≤ D + π(10B) + 4`.

The closed `ComponentPrimeBudget` proof specializes the internally proved
PNT with error parameter one and proves, beyond an absolute B₀,

`π(10B)+4 ≤ 24B/log B`.

The number 24 is a convenient bound, not an asserted optimal constant.
The literal critical band implies B≥B₀ beyond one C-dependent threshold.
Together with the actual D bound, `FreeComponentRank.companion_T9_3` proves

`∃ K>0, ∀ C, ∃ N₀(C), ∀ N≥N₀(C), ∀ L in the band, ∀ x,y∈[N,2N),`
`|c-d_xy| ≤ K B/log B`.

This includes overlapping windows and even equal centres. It adds no
separation, compatibility, admissibility or positive-probability hypothesis.
The source's O_C bound follows; the stronger absolute-constant quantifier
is recorded as a consequence of `P1-MATH-0006`, preserving its original
T9.2 validation history. The constants for the two lemmas may differ.

## Provenance and validation

The four full graph ports and selected two-copy label definition come from
Paper C commit `b9fa9ba490f201b408a302a86f1594ee620b228b`, with exact blobs,
Apache-2.0 attribution and adaptations in [PAPER_C_REUSE.md](PAPER_C_REUSE.md).
The rank decomposition, actual small-prime constraint equivalence and full
P1 asymptotic comparison are new proofs, not additional Paper C imports.

The complete project uses Lean v4.36.0-rc2 and matching pinned Mathlib.
Full build, source identities and the actual 1,435-declaration kernel audit
are checked before publication. Only `propext`, `Classical.choice` and
`Quot.sound` are allowed. No external mathematical input remains assumed
in this proof. No manuscript bytes or Palomar records are changed.
