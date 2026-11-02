# Article Lemma 4.4: statement alignment

Baseline: P1 V1.6, main article page 18, label `p1:alg:components`,
`main_sections/affine_algebra.tex:134`. The original statement hash is preserved
in `manuscript-results.json`.

The complete conclusion is
`PaperP1.Model.InfiniteStarts.canonical_run_components_finset`.
It gives a unique finest direct partition and all three factorization
identities under the actual infinite prime-sign measure.

## Partitions and directness

The finite carrier is the subtype of the original finite set `I`. A partition
of its universe is a partition of the elements of `I`; its parts contain the
original indices with their membership proofs. Reindexing preserves the
labels. The ordinary finite-set joint moment and centered coefficient agree
with the corresponding carrier-indexed Bochner products by
`infiniteJointMoment_eq_family_subtype` and
`infiniteCenteredCoefficient_eq_family_subtype`.

`blockSpace S C` is the range of addition from the subspaces indexed by `C`.
`blockSpace_eq_iSup` identifies it exactly with their sum. A
`BlockDirectPartition` states that a zero sum of vectors in these part-spaces
has every component zero. `blockDirect_iff_addition_injective` proves the
equivalent injectivity of addition, the standard direct-sum condition.

The construction first uses `RelationDirectPartition`: every global zero-sum
effective coefficient tuple restricts to a zero-sum tuple on each part.
`relationDirect_iff_blockDirect` proves equivalence with the actual block-space
directness condition. Thus the relation criterion is not assumed to stand in
for directness without proof.

## Existence and uniqueness

The relation criterion is closed under common refinement. Restrict a relation
to one part of the first partition, then to a part of the second; the resulting
sum is on their intersection. The indiscrete partition satisfies the criterion,
including the unique empty partition when the carrier is empty.

There are finitely many partitions of the finite carrier. Their common
refinement over all relation-preserving partitions is itself relation-preserving
and refines every such partition. The proved equivalence makes it the unique
finest direct partition. `canonicalRunPartition` applies the construction to
the effective square-class images of the actual run windows.

## Nullity additivity

`groupCoefficientsEquiv` regroups coefficients by their unique partition part.
For a direct partition, `relationKernelPartitionEquiv` restricts this to a
linear equivalence between the global relation kernel and the product of the
relation kernels inside the parts. Taking dimensions proves
`relativeNullity_partition_additive` and its canonical specialization.

These kernels are formed from the effective square-class images. Local
relations have already been quotiented out; they are not counted again in
the relative nullity.

## Probability and centered-moment factorization

`spectralCoefficient_partition` proves a finite character-sum factorization
for any local frequency condition. Directness makes the global relation
condition equivalent to the relation conditions inside every part. Regrouping
coefficients and the finite product-of-sums identity then factor the spectrum.

The ordinary affine spectrum allows zero frequencies; the centered spectrum
excludes zero separately in each original block. Uniform character
orthogonality supplies actual expectations for both spectra. Consequently
`effectiveJointMoment_partition` and `effectiveCenteredMoment_partition`
prove both moment identities. No independent-block premise is used in these
theorems; factorization follows from the proved directness condition.

The square-class/character equivalence preserves sums and transports direct
partitions to the actual finite-cylinder characters. Exact finite/infinite
expectation transport gives the identities for the original infinite-model
joint and centered Bochner moments. Actual individual marginals are retained
throughout.

## Scope

The final theorem assumes positive run length and positive actual marginals,
exactly the paper's admissible-family context. It constructs a cutoff covering
the finite family inside its proof. The empty family is included: the unique
empty partition, unit joint and centered products, and zero relative nullity.

The construction uses every effective relation, including those joining an
already dependent group to another block. It does not identify canonical
components using primitive block supports alone. No local-rigidity or
asymptotic arithmetic estimate is imported or assumed.


## Original finite families including zero marginals

The actual finite-set version of main 4.4 is now checked without a
positive-marginal/admissibility premise. For every finite original family I,
L>0 and every actual relation-direct partition P, the original q(I), c(I)
and relative nullity factor exactly over the original images of its parts.
The same unique finest canonical partition satisfies the complete existing
CanonicalRunPartitionConclusion, with no positive-marginal argument supplied
by the caller. If a marginal vanishes, its unique containing part has zero
joint and centered coefficients, and both full products vanish exactly.
The positive case uses the already checked effective-space factorization.
Empty families and all zero-mass cases are retained. This completes the
unrestricted original-model statement directly rather than relying on a
standing admissibility convention. Main 4.4 stays proved; no new numbered
completion or manuscript correction is counted.

Verified Lean v4.36.0-rc2 full build (10887 jobs), actual Audit.lean kernel audit (6797 declarations; only propext, Classical.choice, Quot.sound), 4514 direct ledger/finding declaration checks, 138 source manifest entries and all 167 original statement hashes. Ubuntu root free space: 15.34 GiB. The unique canonical original finite-set decomposition and all direct-partition joint/centered products include zero marginals and need no positivity premise. The literal non-direct pair cost is at most A2^2/2; the complete actual connected fourth-cumulant comparison at N^(-1+epsilon) uses the existing explicit BCN premise. The sharper source N^(-3/2+epsilon) comparison remains open. Main 4.4 stays proved; main 16.1 stays in progress. Coverage 77/167, improvements 89.
