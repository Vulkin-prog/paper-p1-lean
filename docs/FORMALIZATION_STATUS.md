# Formalization status

Stage: **finite identities on general probability spaces**, 31 October 2026.
Neither document is fully formalized.

- Baseline: P1 V1.6, 167 numbered results: main 73, companion 94.
- Numbered results completed: **3 / 167**: article Propositions 4.1, 5.2 and Lemma 5.1.
  Lemma 5.1 is the full
  first-excluded-prefix polynomial expansion on an arbitrary finite ordered set.
  The boundary is proved to be deletion of the maximum, and the suffix is proved
  to lie strictly after that maximum. The scalar parameter and empty products
  are included. The theorem holds over any commutative semiring.
- Article Proposition 4.1 is proved on an arbitrary probability space for a
  finite measurable Boolean family. `observedCountLaw_realizes` identifies the
  full measure-theoretic count law; `centered_bernoulli_expansion` proves the
  identity over the admissible set of positive exact Bochner marginals, the
  unit empty coefficient, vanishing singleton terms and probability status of
  the complementary references. The carrier may be the finite subtype of the
  paper's index set; `indicatorCount_subtype` proves the count reindexing.
  No independence or model-specific arithmetic premise is used.
- Article Proposition 5.2 is proved on an arbitrary probability space.
  `positive_stopped_remainder` gives the exact stopped law difference, positive
  kernel and its mass, and the full ordinary ℓ¹ error bound. Each kernel
  coefficient is proved to be the expected prefix activity times the actual
  suffix count event; its mass is the actual joint activation probability.
  The suffix can remain completely dependent. The retained reference has total
  mass one, without an assertion that its individual coefficients are positive.
- The ordinary ℓ¹ norm is the sum of absolute singleton masses. Its triangle
  inequality, convolution submultiplicativity and difference-power bound are
  proved. Positive kernels have norm equal to their mass, so the bound incurs
  no exponential factor in the suffix size.
- The inclusion-exclusion transform is proved to equal actual finite centered
  moments. Total mass is proved to be the coefficient sum and a convolution
  homomorphism; coefficientwise positivity is preserved by convolution.
- The project currently has **296 audited theorem/lemma declarations**. This
  count includes auxiliary facts and is distinct from numbered-result coverage.
  Generic binary character orthogonality and the affine fiber Fourier identity
  are proved. The full-support centered Fourier formula, its sharper
  `2^ρ - 1` bound and nonzero-moment implication are now proved on effective
  dual subspaces and instantiated for actual finite-cylinder run moments.
  The relative nullity is identified with the dimension deficit in the paper.
  These formulas and bounds are also transported to the actual infinite
  prime-sign measure. Square-class-image identification remains open, so
  article Lemma 4.2 remains in progress. No P1 compatible-nullity or
  asymptotic estimate is claimed proved.
- Paper C code ported: parity vectors and selected finite prime-cylinder
  definitions/proofs, with exact source identities recorded in the reuse ledger.
  Complete multiplicativity, the signed run-start interpretation, cutoff
  adequacy, actual cylinder probabilities and the exact-marginal centered
  count-law identity are proved. The infinite prime-sign measure, restriction
  to finite cylinders and exact consistency of values and start events have
  now been ported. Finite product-measure singleton weights equal the actual
  real weights used in P1. Every finite-cylinder expectation is transported;
  infinite start marginals and centered moments equal their finite versions.
  `dyadicCountLaw_realizes_infinite_count` identifies the full count law with
  its actual infinite-measure pushforward. The no-constant-tail result is
  also checked; its inherited lemma number refers to Paper C.
  External literature propositions encoded: none.
- Generic affine fibers, their kernel equivalences, power-of-two cardinalities
  and rational uniform probabilities have been ported and checked. The actual
  real uniform mass is now proved to be zero for incompatible systems and
  `2⁻ʳ` otherwise. The full run-start affine system has been ported, and this
  formula is linked to actual finite-cylinder run marginals for positive length.
  Local rigidity and the comparison of effective rank with `L` remain open.
- On any effective subspace of actual binary linear forms, the affine event
  has its character expansion and actual marginal equal to the inverse size
  of that space. Local signs are evaluations at a solution and proved
  independent of the chosen solution. Run events are identified with the
  image of their actual row transpose, so local row relations are quotiented
  before taking centered products. Square-class identification remains open.
- Mathematical improvements confirmed: `P1-MATH-0001`, weaker ambient algebra
  assumptions for Lemma 5.1. No error in the original conclusion is asserted.
- Palomar registrations: none; preparation only.

The machine-readable [coverage ledger](manuscript-results.json) records the
individual status of every result. It records the exact original source block
hash and the original label, number, page and file. Preparatory lemmas do not
change these result statuses.

## Development sequence

1. Construct the completely multiplicative random sign model and run-start
   events, retaining both signs and the left boundary. Audit possible reuse
   of Paper C's finite and infinite prime-sign models.
2. Formalize effective square-class spaces, affine consistency, exact marginal
   probabilities and their finite-dimensional algebra; prove the full centered
   and first-excluded-prefix identities without independence assumptions.
3. Inventory every arithmetic literature input with its parameters and
   uniformity. Formalize the local/relative rank and channel estimates; separate
   fixed-order bounds from bounds with a growing number of blocks.
4. Formalize exact cumulant identities, reconstruction with every marginal
   retained, the fourth-order lower bound, the optimal quadratic error theorem,
   and explicit rational-channel refinements.
5. Complete companion coverage, including positional and supplementary results;
   reconcile each correction with the future manuscript revision.
6. Freeze a validated commit, prepare standalone statements and solutions,
   perform Comparator and kernel replay checks, then prepare Palomar records.

Each stage requires precise statement alignment and updated coverage, correction
and literature-input ledgers. This order is provisional and may be refined by
the dependency graph discovered during formalization.
