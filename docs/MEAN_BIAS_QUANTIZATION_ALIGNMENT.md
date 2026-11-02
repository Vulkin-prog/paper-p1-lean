# Main17.3: exact mean quantum and critical signed classification

Source: `p13:optimal:nominal`. Status: **in progress** for the true-law distance estimates. The exact identity and finite criteria below are proved; original source bytes are preserved.

The exact integer identity and quantum in main17.3 are now proved
for everyN>=2 and positive lengthL, without a critical-band assumption.
The more general finite statement holds for every deterministic subsetG
of the dyadic block, with nominal mean#G*2^(-L).

`deficiency` is exactly L minus the actual square-class rank, proved
nonnegative. `localMultiplicity` is zero when the actual infinite
marginal vanishes and otherwise2^deficiency. Its equality with the
source compatibility indicator times2^deficiency is proved through the
actual finite affine system. The actual Bochner marginal is exactly
2^(-L) times this natural multiplicity; rank truncation and every cast
are justified. Thus the actual count mean minus the nominal mean is
exactly2^(-L) times an actual finite sum of integer coefficients.
No heterogeneous marginal is replaced by a nominal one.

The mean equals the nominal mean if and only if the integer bias is
zero. Every nonzero bias has absolute value at least2^(-L), with the
explicit critical lower constant (2^C)^(-1)/N. This includes both signs
and makes no assertion of infinitely many nonzero scales.

The proved critical one-window rank theorem gives deficiency at most1
under one threshold before every length. Define actual zero windows
by marginal0 and actual double windows by marginal2*2^(-L). Their
identification with local multiplicities0 and2 is proved. They are
disjoint and partition the irregular set. Regular windows have
multiplicity1. Consequently the literal integer bias satisfies

    M = #double - #zero = 2*#double - #irregular,
    |M| <= #irregular,
    M mod2 = #irregular mod2.

An odd irregular cardinality therefore forces a nonzero mean bias at
that scale. Both the finite criterion and its uniform critical version
are proved. P1-MATH-0085 records this exact signed classification and
parity criterion. It does not claim odd cardinalities or nonzero biases
at infinitely many scales.

The analytic reference comparison is also proved independently:
if0<=mu,nu<=M and alpha>=-1, then

    ||Q(mu,alpha)-Q(nu,alpha)||_1
      >=exp(-M)/2*|mu-nu|.

It uses the actual signed measures and their zero singleton mass;
the exponential difference and all infinite sums are justified. The
parameter assumptions are explicit and are not counted as an actual
law approximation. The remaining conclusions of main17.3 concern
the true count law and require the still-open approximation theorem.
The result is in progress and adds no proved numbered coverage.

Coverage77/167 (main28/73, companion49/94), confirmed findings85.
No new external mathematical input, BCN premise, Paper C port,
dependency download, manuscript-byte change or Palomar registration.

## Validation

Lean v4.36.0-rc2 full build passed (10637 jobs); actual axiom audit passed for all 6201 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 3918 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records remain intact. Ubuntu available space: 15.80 GiB. Exact finite integer mean quantization, source affine compatibility, the nonzero quantum, critical signed zero/double-window classification, parity and the odd-irregular-count criterion are proved. Actual quadratic signed references have explicit mean-separation lower bound exp(-M)/2 for0<=mu,nu<=M andalpha>=-1. No infinitely-many-scales or true-count law approximation is claimed. Main17.3 remains in progress for its true-law distance conclusions. Coverage77/167 (main28/73, companion49/94); confirmed findings85. No new external mathematical input, BCN premise, Paper C port, dependency download, manuscript-byte change or Palomar registration.
