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

Validated proof checkpoint: [72894c0c1dda29fbeb1e57bea917b20f55d6f534](https://github.com/Vulkin-prog/paper-p1-lean/commit/72894c0c1dda29fbeb1e57bea917b20f55d6f534).


## Actual reference-distance upper bound and nonzero quantum

The finite analytic mean-change step used in main1.4 and the fixed-height
hierarchy is now checked for actual signed measures. For nonnegative
meansmu,nu and arbitrary realalpha,beta,

    ||Pi_mu-Pi_nu||_1 <= 2*|mu-nu|,
    ||Q(mu,alpha)-Q(nu,beta)||_1
      <= 2*(1+2*|alpha|)*|mu-nu| + 2*|alpha-beta|.

The same bounds hold first in the completed convolution algebra and
are transported coefficient by coefficient to the ordinary infinite
sum of absolute singleton masses. The Poisson estimate uses its
actual nonnegative series, the explicit bound
||Pi_t-delta_0||<=2*(1-exp(-t))<=2t and the norm-one convolution
semigroup. It needs neither a mean cap nor an exponential loss.
No reference probability or infinite-tail estimate is assumed.

For each fixed coefficient boundA>=0 and epsilon>0, one threshold
precedes everyN,L in the critical band and every |alpha|<=A. Holding
alpha fixed, changing the actual original count mean toN*2^(-L)
costs at mostN^(-1+epsilon). This uses the already proved actual mean
bias estimate and is unconditional. At every sufficiently large scale
where the literal integer mean bias is nonzero, the same signed
reference distance is at leastc_C/N for everyalpha>=-1, with

    c_C = exp(-2*2^C)/(2*2^C) > 0.

Both signs of the mean bias are included. This is a scale-by-scale
conditional lower bound, not an assertion that nonzero biases occur
infinitely often. The coefficient is held fixed in this lower bound;
no lower bound for simultaneous arbitrary parameter changes is claimed.
The true count-law distance in main17.3 remains open.

For every fixed heightb>=3 and epsilon>0, the exact-to-nominal mean
change is at mostepsilon times the actual moving scalar phase at
heightb, uniformly for every boundedalpha. The proof uses the full
positive phase lower boundd*L*N^(-1+1/b) and chooses a mean-bias loss
strictly smaller than1/b. A weaker d/N phase lower bound would not
suffice for this step. Neither the residue nor the nominal mean is
frozen along a subsequence.

For each literal finite channel coefficientalphaHat_h, h>=3, both
Q(actualMean,alphaHat_h) and the corresponding actual Hermite law
are eventually probabilities without BCN or a pair-profile input.
Positive actual mean bounds and direct smallness/positivity of the
finite channel sum establish admissibility. There are actual
probability witnesses for Q(actualMean,alphaHat_h) and
Q(nominalMean,alphaHat_h) whose distances to EVERY probability lawP
differ by at mostepsilon times phaseMass_(h+1). The threshold and
witnesses precedeP, and both references retain the same literal
finite coefficient. No count-law approximation or leading distance
equivalent is assumed or established.

These results complete the analytic mean-replacement step of main1.4
and18.1. Their original count-law and cumulant remainders, leading
distance equivalents and optimality remain open. Main17.3 remains
in progress for its true-law conclusions. No numbered completion is
added: coverage77/167 (main28/73, companion49/94), findings87 unchanged.
Finding85 is extended with its explicit actual-reference quantum.
No new external input, BCN premise, PaperC port, dependency download,
manuscript-byte change or Palomar registration is introduced.

Lean v4.36.0-rc2 full build passed (10737 jobs); actual axiom audit passed for all 6466 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 4183 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records remain intact. Ubuntu available space: 15.61 GiB. Actual Poisson and quadratic signed references have universal parameter Lipschitz bounds, without a mean cap. Holding a bounded quadratic coefficient fixed, exact-to-nominal mean replacement has unconditional cost N^(-1+epsilon), and at every nonzero integer-bias scale has lower bound exp(-2*2^C)/(2*2^C*N) for alpha>=-1. No infinitely-many-scales assertion is made. The change is negligible on the actual moving omitted-height phase for every fixed height, and literal explicit references at the actual mean are eventually probabilities without BCN. Stability holds for every actual probability law P, after the common threshold and witness choices. Original-count approximation, distance equivalents and optimality remain open; main1.4,17.3,18.1 remain in progress. Coverage77/167 (main28/73, companion49/94), confirmed findings87. Finding85 is extended with its actual-reference quantum. No new external input, BCN premise, PaperC port, dependency download, manuscript-byte change or Palomar registration.
