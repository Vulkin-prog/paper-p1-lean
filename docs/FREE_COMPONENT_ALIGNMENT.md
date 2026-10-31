# Companion T9.3: free components

**Status: in progress.** This is not a completed numbered result; coverage
remains 15 / 167. Original locator: companion V1.6, page 40,
`p13:rig:components`, `companion_sections/pair_rigidity.tex:129`.
The original statement and source hash are unchanged.

## Exact graph and cutoff, proved

`LargePrimeOccurrences.Occurrence L` is the disjoint union of two copies of
`Fin (L+1)`. The labels are the true complete vertex labels of V_x and V_y,
including each left boundary. Overlapping physical values remain distinct
formal vertices, as in the source.

A prime greater than L+1 has at most one odd occurrence in each copy. This
is proved from the checked P1 private-prime lemma, without assuming valuation
one. `primeOccurrences` is the actual finite set where the parity coordinate
is one. Its cardinality is at most two, and distinct occurrences lie in
opposite blocks.

In the P1 graph, `IsLargePrime L p` means p is prime and
`10*(L+1)<p`. Edges join its two occurrences; a unique occurrence is a pin.
`largePrime_gt_length` explicitly supplies the weaker length condition when
using the occurrence lemmas, with L fixed in all cardinality calls.

`largePrimeSolution` is the actual kernel of all these large-prime equations.
Its membership is proved equivalent both to the full parity-coordinate
equations and to agreement across every edge plus vanishing at every pin.

## Component resolution and exact arithmetic dictionary, proved

`PinnedGraphResolution.pinnedGraphLinearEquiv` resolves the generic pinned
solution space by one free binary value per unpinned connected component.
The dimension is the number of those components. Isolated and nontrivial
unpinned components partition them, and their vertex budget is proved.

The concrete `LargePrimeGraphResolution` gives exactly

`finrank(largePrimeSolution x y L) = D + c`,
`D + 2c ≤ 2(L+1)`.

Here c is the number of unpinned components with at least two vertices, and
D is the number of actual defective formal vertices. The equivalence of
isolated unpinned components and defective vertices is proved, not assumed.

`LargePrimeComponentArithmetic.isDefective_iff_kernel_one` identifies graph
defectiveness with the literal large odd-prime kernel above 10(L+1) being
one. An injective label map and an exact image equality give

`D = #criticalDefectivePositions x L + #criticalDefectivePositions y L`.

This counts formal copies, even for overlapping physical windows.
`defectiveVertexCount_critical_bound` proves its O(B/log B) estimate in the
critical band, with B=L+1, by the already proved T9.2. The multiplicative
constant is chosen before the fixed band width; only the threshold depends
on that width.

## Selection and the two blocks, proved

`solution_constant_on_component` proves constancy on a connected component
for every actual solution of the large-prime equations.
`component_selected_or_omitted` states the exact binary consequence: every
vertex of a component is assigned zero, or every vertex is assigned one.
Pinned components necessarily take zero by the checked resolution.

`nontrivial_component_meets_both_blocks` proves that every connected
component with at least two vertices contains vertices from both formal
blocks. Its proof finds an edge in the component and uses the actual
opposite-block occurrence lemma. The free-component specialization is
`free_nontrivial_component_meets_both_blocks`.

## Remaining obligation

The source also asserts `c=d_xy+O_C(B/log B)`, where
`d_xy=finrank(S_x ∩ S_y)`. This comparison is not yet formalized.
It needs the complete even-relation space, its dimension in terms of the two
local kernels and d_xy, and the finite rank cost of imposing the remaining
small-prime equations and the two block parities. The critical local-kernel
bound and the required actual defect count are already proved elsewhere,
but their complete rank comparison is still an obligation.

The graph equivalence, dimension D+c and small D alone are not counted as
having proved that missing comparison. No bound on c-d_xy is introduced as
an assumption or hidden interface.

## Provenance and validation

Four selected full graph modules are adapted from the pinned Paper C snapshot
`b9fa9ba490f201b408a302a86f1594ee620b228b`, with exact Git blobs, Apache-2.0
attribution and adaptation records in [PAPER_C_REUSE.md](PAPER_C_REUSE.md).
Only the two-copy label definition is selected from its older two-start
module. The old relational-assignment and geometric component imports are
not imported. No compiled artifact from the old Lean version is reused.

The full Lean v4.36.0-rc2 build and actual kernel audit pass for all 1,416
project theorem/lemma declarations. Only `propext`, `Classical.choice` and
`Quot.sound` are permitted. Source identities are checked separately.
No new mathematical finding or Palomar registration is made at this partial
checkpoint.
