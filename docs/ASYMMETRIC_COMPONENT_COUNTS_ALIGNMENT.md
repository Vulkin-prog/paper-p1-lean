# Actual asymmetric component host counts

Source: companion T1.10, arithmetic_appendix.tex:811-860. Uses the [actual graph and target budget](ASYMMETRIC_TARGET_BUDGET_ALIGNMENT.md) and the [corrected offset exclusions](ENLARGED_OFFSET_SYSTEMS_ALIGNMENT.md).

The ACTUAL asymmetric pinned components now have the geometric
half-power and degree-one subpower host counts, with the corrected
old-width-dependent nonalignment exclusion. AsymmetricComponentHostCount
keeps the prescribed old rule arbitrary after the common constant and
threshold. It never assumes component systems or counts as input.
The underlying ordinary/source surface-cover and curve properties
remain the same explicit unproved geometric arguments as before.

AsymmetricComponentOffsets constructs each literal root offset as the
actual component value minus its ORIGINAL source or target centre,
not the centre of the enlarged bookkeeping envelope. The root maps
are injective, their cardinalities equal the actual left/right vertex
counts, and distinct components give disjoint root lists. Every free
old root lies in the actual old set, so its offset is bounded by R.
Every free new root is an actual original-window value, so its offset
is bounded by the same R when B<=R. The complete integer product and
square prescription are proved at those original centres. The actual
coefficient has odd-prime support at most10(H+1), since augmented
unpinned components are also unpinned for the original envelope graph.

AsymmetricComponentSystems constructs the general two-sided root pattern
and the degree-(a,1) pattern, including every coefficient, square root,
bounded offset, disjointness condition and degree bound. Their literal
pool width is R-1, hence radius R; the new length remains the original L.
AsymmetricComponentHostData defines the actual augmented-unpinned
nontrivial components, the small components and their degree-(a,1)
subfamilies. It extracts k distinct original components by a genuine
finite injection whenever the actual count is at least k.

AsymmetricComponentHostCount.uniform_general gives N^(1/2+epsilon)
hosts for k small actual asymmetric components. uniform_linear gives
N^epsilon hosts for k actual degree-(a,1) components, uniformly over
EVERY positive a with a+1<=K; enlarged nonalignment is needed ONLY
when a=1. Both statements use the original dyadic centres and the
radius Dold, under R<=Dold*B, B<=R, 2R<=H and H<=Dcut*B.
The actual arbitrary old sets lie within distance R of their centre.
All small-prime codes and root positions are summed by the previously
checked enlarged smooth pattern counts. No old-rank or selected-value
independence condition is imposed.

The dense consequence is assembled as well. With
sizeCap=ceil(4*(Dcut+1)/eta), the elementary disjoint vertex budget
shows that eta*B actual nontrivial components give at least (eta/2)*B
small components. A single critical threshold makes this at least k.
uniform_dense therefore gives N^(1/2+epsilon) hosts whenever the
actual asymmetric nontrivial component population has size>=eta*B.
It retains the original new length, arbitrary prescribed old sets and
the corrected radius Dold. The chosen-source surface cover and
normalized curve-count property are its only unproved arguments.

What remains for the weighted dense profile is to bound the number of
singleton-target components outside the actual degree-one exceptional
populations, and to combine the exact rank budget with local defects.
The31/24 assertion is not proved. The unconditional sparse support
bound remains4/3+epsilon. T1.10 stays in progress; coverage stays87/167
unconditional and48 conditional, and findings stay161 improvements
plus the one confirmed alignment-scope correction P1-MATH-0162.
No manuscript source, dependency or toolchain change occurs.

The result ledger records exact verification and proof commits.
