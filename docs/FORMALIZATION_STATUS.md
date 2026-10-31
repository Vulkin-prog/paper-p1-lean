# Formalization status

Stage: **finite algebraic identities**, 31 October 2026. Neither document is fully formalized.

- Baseline: P1 V1.6, 167 numbered results: main 73, companion 94.
- Numbered results completed: **1 / 167**: article Lemma 5.1, the full
  first-excluded-prefix polynomial expansion on an arbitrary finite ordered set.
  The boundary is proved to be deletion of the maximum, and the suffix is proved
  to lie strictly after that maximum. The scalar parameter and empty products
  are included. The theorem holds over any commutative semiring.
- Article Proposition 4.1: **in progress**. Its complete finite-probability
  identity is proved for the actual count pushforward, with arbitrary dependence,
  exact heterogeneous marginals, unit empty coefficient, vanishing singleton
  coefficients and probability status of every complementary Bernoulli product.
  Connecting the multiplicative prime-cylinder model to the manuscript law
  remains an explicit obligation, so the numbered result is not marked proved.
- The inclusion-exclusion transform is proved to equal actual finite centered
  moments. Total mass is proved to be the coefficient sum and a convolution
  homomorphism; coefficientwise positivity is preserved by convolution.
- The project currently has **89 audited theorem/lemma declarations**. This
  count includes auxiliary facts and is distinct from numbered-result coverage.
  No Fourier, compatible-nullity or asymptotic estimate is claimed proved.
- Paper C code ported: parity vectors and selected finite prime-cylinder
  definitions/proofs, with exact source identities recorded in the reuse ledger.
  Complete multiplicativity, the signed run-start interpretation, cutoff
  adequacy, actual cylinder probabilities and the exact-marginal centered
  count-law identity are proved. Infinite-cylinder consistency is still open.
  External literature propositions encoded: none.
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
