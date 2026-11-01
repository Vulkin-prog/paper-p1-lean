# Connected and primitive families — main Corollary 10.2 in progress

This corollary is not complete and is not included in numbered coverage.
Actual generic canonically connected effective-block tuples have the
full half-count. The remaining original-window family and independent-
mass/primitive alignment is listed explicitly below.

## Canonical connectedness and actual generic host counts

`ConnectedBlockLists.Connected` means that the previously proved canonical
relation partition of the actual effective block spaces is the one-part
top partition. The earlier equivalence with the canonical direct-space
decomposition is proved in `Affine.DirectPartitions`.

`ConnectedRelations.coordinate_relation` proves that every coordinate of
a connected family with at least two indices is nonzero in some actual
global relation. It uses the actual finest partition and the direct split
that would isolate a coordinate if all its relation projections were zero.
This does not assert one full-support relation for the whole family.

The actual connected tuple set embeds into the actual relative-participation
population. The complete simultaneous count in
`RelativeBlockRelationsCount.uniform_count` gives N^(r/2+epsilon) for
these actual tuples, uniformly in all finite block shapes and candidate
sets obeying literal positive value heights and logarithmic distances.
See [the complete relative extension](RELATIVE_PARTICIPATION_ALIGNMENT.md).

## Actual successive-exposure populations

`EffectiveExposure.Exposable` also models the printed successive-exposure
construction directly: the empty tuple is exposed, and each nonempty group
has a nonzero own-space projection at every new coordinate whose total
lies in the full span of already exposed blocks. All split/bijection codes,
actual populations and fixed-prefix fibre injections are proved.

`EffectiveExposureCount.uniform_count` proves the complete actual exposure
population bound by strong induction in the number of coordinates. It
instantiates the complete 10.1 group estimate at every actual fixed prefix
and the actual smaller exposed population count, then sums the finite
role/bijection choices. No extension count is supplied as an assumption.
The relative-participation proof gives a separate direct route for the
canonical connected generic tuple count.

## Remaining obligations before marking 10.2 complete

- Identify the actual original-window effective spaces and geometry with
  the finite blocks used by the generic tuple theorem.
- Count actual unordered size-r window families by the actual injective
  tuple population, with all reindexing and cardinality bridges verified.
- Prove the primitive-family inclusion from the source positive nullity
  and directness of every proper subfamily.
- Bound the actual independent mass using the exact heterogeneous window
  marginals and the already proved uniform critical-band marginal estimate.

The generic host count does not by itself complete these obligations.
Coverage remains 64/167 and confirmed improvements are 65. Original sources
remain byte-for-byte preserved. Palomar is a later completion milestone.

Verification checkpoint: Lean v4.36.0-rc2 full build passed (9,821 jobs); actual axiom audit passed for all 4,501 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 2,216 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records remain intact. Ubuntu available space: 17.20 GiB. No unproved group, extension or target count, new external input, Paper C port, manuscript-byte change or Palomar registration. Coverage remains 64/167; confirmed improvements are 65; main 10.2 is still in progress.
