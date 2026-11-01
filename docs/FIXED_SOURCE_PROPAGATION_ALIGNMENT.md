# Main 6.3 — Conditional sums and propagation

Source: main Proposition 6.3, page 22, `p1:fixed:propagation`,
`main_sections/fixed_moments.tex:105`, statement SHA-256
`a053ebcb00eb0a8b133d02a11c330ec2119e4122cb9304305b1a7b8e4858a659`.
The first conditional-sum assertion is **proved**. The full numbered
result is **in progress**, pending extension-family propagation and
the local-defect/contact seed conclusion.

## Actual conditional affine probabilities

`WindowFamilyConditional.sourceEvent` is the literal event that all
source relative-bit vectors have their prescribed values under the
infinite prime-sign measure. `conditionalProbability` is the real
measure of the intersection with the target-vector atom divided by
the actual source-event probability.

`CompatibleWindowPrescriptions.source_mass_affine` transports every
source event to the finite joint affine system. Every positive-mass
prescription therefore has an actual cylinder witness. Homogeneous
prescriptions have positive mass. No compatibility or witness existence
is assumed without an explicit positive-mass source premise.

`WindowFamilyConditional.conditional_eq_mass` identifies the actual
conditional probability with the finite affine observation probability
after observing the full source row space. Its increment is proved
equal to the actual square-class delta_z, including overlapping,
dependent or repeated sources.

`ExtensionRankBudget.total_rank_identity` proves the exact total-rank
identity. `FamilyConditionalMass.kernel_rank_identity` combines it
with the quotient-rank identity. The conditional mass is either zero
or 2^delta times the inverse power of two of the actual target rank.
Nonnegativity and the cap one are proved from the actual events.
The critical local relation-rank bound <=1 then gives the uniform
upper bound 2*2^delta/2^L for every target prescription, even when its
unconditioned affine atom is incompatible.

## The complete conditional sum

`WindowConditionalSum.finite_bound` proves the exact low/high split

    sum_z conditional(z) <= N*(2/2^L)*2^(eta*L)
                              + # {z : delta_z>=eta*L}.

`SmallRankLossPower` proves an explicit critical-band power bound.
`FixedSourceConditionalSum.witness_sum` combines it with the complete
actual main 6.2 count. One eta is selected before every source tuple,
length and cylinder. The exponent margins and constant absorption
are proved.

`FixedSourceConditionalSum.conditional_sum` removes the witness
parameter using its constructed cylinder representative. It bounds
the actual infinite-measure sum by N^epsilon after one threshold,
for every compatible affine source prescription and arbitrary target
prescriptions, which may depend on the centre. Repeated sources are
allowed and all centres in I_N are counted. `homogeneous_sum` gives
the all-homogeneous specialization. `fresh_conditional_sum` proves
the exact source-excluding first display of main 6.3.

## Remaining full-statement obligations

- Construct the actual higher-order extension families and prove their
  total positive joint-mass propagation from this conditional sum.
- Supply the actual local-defect and compatible-contact seed mass
  bounds, and propagate them to all fixed orders.

No extension-family or seed mass estimate is currently counted complete.
Coverage remains 70/167 (main 24/73, companion 46/94), with 69 confirmed
independent findings. No external assumption, new Paper C code, original
manuscript edit or Palomar registration is introduced.

Conditional-sum checkpoint verification: Lean v4.36.0-rc2 full build passed (9999 jobs); actual axiom audit passed for all 4908 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 2623 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records are intact. Ubuntu available space: 16.57 GiB. The first conditional-sum assertion of main 6.3 is complete on the actual infinite prime-sign measure, including arbitrary compatible affine prescriptions, homogeneous prescriptions and literal source exclusion. Extension-family propagation and the final seed consequence remain open, so main 6.3 stays in progress. Coverage and confirmed independent findings remain 70/167 and 69. No conditional-sum premise, external assumption, new Paper C port, manuscript-byte change or Palomar registration.
