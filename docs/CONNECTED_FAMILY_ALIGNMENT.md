# Connected and primitive original-window families — main Corollary 10.2 complete

`OriginalWindowFamilyMass.article_10_2` proves all the source conclusions:
the connected host count and the independent masses of connected and
primitive families. It also gives the primitive host count explicitly.
The original label is `p13:half:connected`,
`main_sections/half_counts.tex:68`. Coverage includes the actual unordered
families and the exact infinite-model marginals.

## Actual source families and effective spaces

`ConnectedWindowFamilies.connectedFamilies G L r` is the actual finite
set of r-element subsets I of G whose effective window spaces have a
one-part canonical direct decomposition. Connectedness is equality of
the previously proved finest relation partition with the top partition;
`Affine.DirectPartitions` identifies it with the canonical direct-space
decomposition in the manuscript.

`primitiveFamilies` uses the source condition: relative nullity on I is
positive and the relative nullity on every proper subfamily is zero.
These are the actual addition-kernel nullities of the effective spaces.
Local square relations have already been factored out.

The complete original window value set is
`NormalizedWindowSets.values x L = Ico (x-1) (x+L)` for x>0.
`space_values` identifies its finite even-selection image exactly with
`squareClassSpace x L`. For every critical-band length and sufficiently
large N, its actual values have height in [N/2,3N] and signed distance
at most L+1 from x. `OriginalWindowValueBounds.values_geometry` proves
these literal inequalities. `CriticalWindowGeometry.uniform_geometry`
supplies a common positive-length/logarithmic-width threshold.

The final statements are uniform in every length in a fixed critical band
and every candidate subset G of the dyadic block. They therefore apply to
the paper's admissible candidate set without a regularity restriction.

## Canonical connectedness and primitive relations

`ConnectedRelations.coordinate_relation` proves that every coordinate in
a connected family with at least two indices is nonzero in some actual
global relation. If all its relation projections vanished, the partition
isolating that coordinate would be direct, contradicting the actual finest
one-part partition. Different coordinates may use different relations.

The fully proved relative-participation extension of 10.1 counts these
actual tuples. It does not assert that every connected family has one
full-support relation. Its actual support extraction, old-span enlargement
and simultaneous induction are described in
[the relative-participation alignment](RELATIVE_PARTICIPATION_ALIGNMENT.md).

`PrimitiveRelations.full_relation_of_minimal_nullity` starts with an actual
nonzero vector in the full relation kernel. If a coordinate vanished,
erasing that index would give a relation in a proper direct subfamily.
Its addition map is injective by the proved zero-nullity/directness
equivalence. Extension by zero would then force the original relation to
vanish. Thus the actual primitive relation has full support.

## Actual unordered-family cardinalities

`FiniteFamilyEnumeration.enumeration` enumerates each actual r-element
family by Fin r. Its centre tuple is injective and has exactly that family
as its image. Reindexing the actual canonical or primitive relations
preserves their zero sums and own-space nonzero projections.
`ConnectedWindowFamilies` places these enumerations in the actual
relative-participation tuple population.

Every actual connected or primitive family is an image of one of those
actual tuples. The finite image/cardinality theorem therefore bounds each
unordered family population by the actual tuple population.
`OriginalWindowFamilyCounts.uniform_hosts` instantiates the complete
relative-participation count with the actual window height/distance data.
Both host counts are at most N^(r/2+epsilon) eventually. No family or tuple
host count is an assumed argument.

## Exact heterogeneous independent mass

`FamilyIndependentMass.independentMass F L` is the actual sum
sum_(I in F) product_(x in I) infiniteMarginal(x,L).
Each factor is the exact infinite-model window marginal.

`OriginalWindowFamilyMass.uniform_marginals` instantiates the already proved
critical-band marginal theorem at the actual base x-1>=N/2. Positive
marginals have the proved common K/N cap. A zero marginal also satisfies
it, and every exact marginal is nonnegative. The threshold is common to
all lengths and starts in the band and dyadic block.

The finite product inequality bounds each r-element family's actual product
by (K/N)^r. Summing over the actual family population and using its proved
host count gives K^r*N^(-r/2+eta). The proved fixed-factor absorption uses
the remaining epsilon margin. This yields N^(-r/2+epsilon) for both actual
connected and primitive independent masses. No homogeneous nominal marginal
or affine compatibility assumption replaces the source data.

## Scope and verification

All four actual conclusions are proved for each fixed r>=2 and positive
epsilon. All thresholds precede the varying critical length and candidate
subset. The constants imply the printed fixed-parameter O estimates.
The separate actual successive-exposure population count remains available
as an additional proved model of the printed exposure argument.

P1-MATH-0065 records the stronger relative-participation input; its earlier
generic-count-only validation is preserved in the finding's history.
Completing the original-window and independent-mass alignment adds no new
independent mathematical finding. Coverage is 65/167 (main 22/73,
companion 43/94), with 65 confirmed improvements. No original manuscript
bytes, external input or Paper C port change. Palomar remains a later
milestone for the completed development as a whole.

Full original-window family verification: Lean v4.36.0-rc2 full build passed (9,835 jobs); actual axiom audit passed for all 4,515 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 2,230 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records remain intact. Ubuntu available space: 17.18 GiB. Full main 10.2 is complete; coverage is 65/167 (main 22/73, companion 43/94), with 65 confirmed improvements. No unproved host or independent-mass count, new external input, Paper C port, manuscript-byte change or Palomar registration.
