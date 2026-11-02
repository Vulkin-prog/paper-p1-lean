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


## Original canonical block families at every finite order

Actual canonical components are now handled as original finite subsets
at every finite order. Their union recovers I, every part is nonempty and
connected, and the original coefficient satisfies c(I)=prod_(C in P(I))c(C).
The absolute identity also holds exactly. Reindexing the subtype parts is
injective, so no duplicate part or hidden multiplicity is introduced.
If c(I)!=0, every part has at least two sites. Every nonempty nonconnected
family has at least two canonical parts. These finite statements include
zero marginals and incompatible families; only L>0 is needed for the
probability factorization.

A separate arbitrary-weight finite polymer lemma proves the tail bound

    sum_(P subset A, |P|>=2) prod_(C in P)w(C)
        <= (W^2/2)*exp(W),  W=sum_(C in A)w(C), w>=0.

An actual decomposition whose union recovers its source family is injective
as a finite record, so the same bound controls any covered family with
at least two blocks. No independence of arbitrary polymers is assumed.
Applying this to the actual canonical components gives, for every fixed r>=1,

    A_r - A_r_connected = A_r_nonconnected >= 0,
    A_r_nonconnected <= (W_r^2/2)*exp(W_r),

where W_r is the literal absolute activity of all connected original blocks
of sizes 2 through r. The finite bound and exact difference are unconditional.
Under the existing ordinary explicit BCN premise, the already checked
fixed-order half-power estimates at the finitely many orders up to r give

    0 <= A_r - A_r_connected <= N^(-1+epsilon)

eventually uniformly over critical lengths and all dyadic subgrounds.
The threshold depends on r before N; no growing-order conclusion is made.
This is a sharper remainder for nonconnected families. The source 4/5
connected bound and separate contact estimate of T14.1 remain open.
Main 4.4 stays proved and companion T14.1 stays in progress. Coverage stays
77/167 (main 28/73, companion 49/94), confirmed improvements stay 90.
No new external input, axiom, dependency download, source-byte change or
Palomar registration is introduced.

Verified Lean v4.36.0-rc2 full build (10913 jobs), actual Audit.lean kernel audit (6838 declarations; only propext, Classical.choice, Quot.sound), 4555 direct ledger/finding declaration checks, 138 source manifest entries and all 167 original statement hashes. Ubuntu root free space: 15.28 GiB. Exact canonical original block images, connectedness, coefficient/absolute factorization, nonzero block size and the finite quadratic polymer tail are unconditional. Under existing explicit BCN, nonconnected activity and the absolute all/connected activity difference are at most N^(-1+epsilon) at every fixed positive order, uniformly over dyadic subgrounds. Growing orders and the source sharp connected/contact bounds are not claimed. Main 4.4 stays proved; companion T14.1 stays in progress. Coverage 77/167, improvements 90.
