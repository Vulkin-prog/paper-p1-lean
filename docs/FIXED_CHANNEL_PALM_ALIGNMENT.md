# CompanionT2.7: actual negative conditional deviation

Source: `p1:arith:fixed-channel-palm`, companion supplemental arithmetic. Status: **in progress** for the positive-excess and two-sided Palm estimates.

The negative-deviation and source-deletion step in the proof of
companionT2.7 is now proved without BCN, for every source set of any
fixed maximum cardinalityj, not only the selected good channel pairs.
Conditioning uses the actual prescribed source event with positive
joint massq(A). Each actual new conditional probability is precisely
q(A union{z})/q(A); it lies in[0,1] and its probability-event ratio is
identified under the original infinite measure.

With p=2^(-L), define the positive and negative deviations over the
fresh dyadic starts by max(0,conditional-p) and
max(0,p-conditional). The actual retained branching identity gives
conditional=p outside the deterministic badStarts set constructed
from the old raw-value prime pool. Thus, at finiteN,L,

    negativeDeviation <= #badStarts*p.

The complete fixed-j exceptional count and the critical nominal bound
give, for everyepsilon>0, eventually uniformly beforeN,L,A,

    negativeDeviation <= N^(-1/2+epsilon),
    #A*p <= N^(-1+epsilon),
    E[Z_N-#A | all sources inA active] >= lambda-N^(-1/2+epsilon).

The expectation is an actual conditional Bochner integral, not a
formal sum substituted for an unproved conditional law. Finite
indicator integrability and integral linearity identify it with the
sum of actual conditional probabilities over fresh starts. On the
source event all#A source indicators are one, so deleting them is
proved identical to subtracting#A from the full original count.
The exact signed decomposition is

    freshMean=lambda-#A*p+positiveDeviation-negativeDeviation.

The same negative bound holds after any finite nonnegative weighting
of source sets, including division by the actual positive total
weight. One threshold precedes the population and its weights.
Forj=2 this supplies the complete negative error and source-removal
part of the source Palm mean proof, including its actual conditional
expectation and arbitrary good-pair averaging.

The positive excess, its fixed-channel exponenteta_(a:b), the
asymmetric nonaligned pair profile and the resulting two-sided Palm
mean estimate remain open. No positive-excess bound or conditional
mean convergence is assumed or counted proved. CompanionT2.7 moves
from not_started to in_progress, without a numbered completion.
Coverage77/167 (main28/73, companion49/94), findings87 unchanged.
No new mathematical finding, external input, BCN premise, PaperC
port, dependency download, manuscript-byte change or Palomar
registration is introduced.

Lean v4.36.0-rc2 full build passed (10743 jobs); actual axiom audit passed for all 6485 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 4202 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records remain intact. Ubuntu available space: 15.59 GiB. For any fixed maximum source cardinality, actual negative conditional deviation is at mostN^(-1/2+epsilon), source deletion costsN^(-1+epsilon), and the actual conditional expectation of Z_N-#A is at leastlambda-N^(-1/2+epsilon), without BCN. Actual event probability ratios, finite indicator integrability, conditional Bochner mean identities, signed positive/negative decomposition and arbitrary weighted/normalized source averaging are proved. The fixed-channel positive excess and two-sided Palm estimate remain open; T2.7 is in progress. Coverage77/167 (main28/73, companion49/94), confirmed findings87. No new mathematical finding, external input, BCN premise, PaperC port, dependency download, manuscript-byte change or Palomar registration.
