# Formalization status

Stage: **initialization**, 31 October 2026. Neither document is fully formalized.

- Baseline: P1 V1.6, 167 numbered results: main 73, companion 94.
- Numbered results completed: **0 / 167**.
- Initial scope: the algebraic inclusion-exclusion centering transform and its
  empty, singleton and two-site identities, with normalization and marginal
  premises explicit. Probability-space interpretation remains to be constructed.
- These five auxiliary lemmas are not the full centered Bernoulli expansion,
  Fourier formula, compatible-nullity bound, or an asymptotic estimate.
- Paper C code ported: none. External literature propositions encoded: none.
- Mathematical corrections confirmed: none at initialization.
- Palomar registrations: none; preparation only.

The machine-readable [coverage ledger](manuscript-results.json) starts every
numbered result at `not_started`. It records the exact original source block
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
