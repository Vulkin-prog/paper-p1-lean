# Main15.1: exact heterogeneous analytic conversion

Source: `p13:transfer:conversion`, `main_sections/exact_transfer.tex:80`. Status: **in progress** for the arithmetic pair-activity rate. Original source bytes are preserved.

The full finite analytic statement of main15.1 is now proved for
actual signed measures, with the explicit constant C_M=16exp(2M).
The restriction p_*<=1/4 is unnecessary for this step: every actual
Bernoulli marginal in0<=p_i<=1 is allowed. A nonnegative P only needs
to dominate the marginals; it need not be small. Pair weights may have
either sign, and any selected family of two-element subsets is allowed.
No independence or covariance-sign assumption is used.

The new generic real Banach-algebra estimate is

    ||prod(1+v_i)-prod exp(v_i)
       +(sum v_i^2/2)*prod exp(v_i)||
    <=(2*sum||v_i||^3+(sum||v_i||^2)^2)*exp(sum||v_i||).

It follows by exact insertion identities, absolute exponential Taylor
tails and finite-product norm bounds. There is no logarithm or
small-norm restriction. The first-order estimate and deletion of any
actual two Bernoulli factors are also proved. Exact exponential sums,
scalar sums and pair corrections identify the resulting reference with
the actual Poisson–Charlier signed measure.

Writing mu=sum p_i, s_j=sum p_i^j, C_2=sum c(e),
A_2=sum|c(e)| and alpha=2C_2-s_2, the full finite bound is

    ||B_2-Q(mu,alpha)||_1
      <=16exp(2M)*(s_3+s_2^2+A_2*(s_2+P)),

whenever mu<=M. The actual ordinary sum of absolute singleton masses
is bounded, including its infinite tail. All covariances retain their
signs before taking this final norm, including incompatible pairs.
The exact finite reference and its completed-algebra image are proved
equal; no coefficient, convolution or tail identity is assumed.

The actual original-run specialization uses exact infinite-model
Bochner marginals and centered pair coefficients on every deterministic
subset G of the dyadic block. The exact identity

    secondFactorialCumulant(G)=2*sum c(e)-sum p_x^2

is proved from actual factorial moments, the finite subset formula and
the full square expansion. Thus the signed reference uses the actual
count mean and actual variance-minus-mean parameter, with its diagonal
term retained.

All actual marginals are proved in[0,1]. The already proved critical
local cap gives p_x<=2^(C+1)/N; its sum gives the actual mean bound,
and every power-sum substitution is proved. One threshold before all
critical lengths and all deterministic subsets gives

    ||B_2-Q(actual mean,actual second cumulant)||_1
      <=K_C*(N^(-2)+A_2/N).

This applies in particular to the full admissible set, with no
zero-marginal replacement or local-independence assumption. The
remaining source application requires A_2=O(N^(-2/3+epsilon)). That
arithmetic estimate remains open and is not supplied as a hypothesis
or counted as proved. Main15.1 is in progress for that final numerical
rate. Coverage remains77/167 (main28/73, companion49/94).

This extends P1-MATH-0084 to heterogeneous marginals without adding a
separate finding: confirmed findings84. No external mathematical
input, BCN premise, Paper C port, dependency download, manuscript-byte
change or Palomar registration is introduced.

## Validation

Lean v4.36.0-rc2 full build passed (10631 jobs); actual axiom audit passed for all 6169 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 3886 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records remain intact. Ubuntu available space: 15.81 GiB. The full finite heterogeneous conversion is proved with C_M=16exp(2M) for every true marginal in[0,1], with arbitrary signed pair weights. Actual infinite-model means, centered pair coefficients and the exact second factorial cumulant with its diagonal correction are identified. A uniform actual bound K_C*(N^(-2)+A_2/N) holds before every critical length and deterministic dyadic subset. The source numerical rate remains open for the arithmetic pair-activity estimate; main15.1 is in progress. Coverage77/167 (main28/73, companion49/94); confirmed findings84, extending P1-MATH-0084 without a new finding. No external mathematical input, BCN premise, Paper C port, dependency download, manuscript-byte change or Palomar registration.

Validated proof checkpoint: [a7ccc5acd2065b4c3cb25f9a42022a3f1774dd0b](https://github.com/Vulkin-prog/paper-p1-lean/commit/a7ccc5acd2065b4c3cb25f9a42022a3f1774dd0b).


## Universal-constant strengthening

A further strengthening of the finite analytic conversion is proved:
the constant is universal, C=16exp(2), with no upper bound on the total
mean. For arbitrary finite Bernoulli marginals0<=p_i<=1, arbitrary
signed weights on selected two-element subsets, and any nonnegative
upper marginal capP,

    ||B_2-Q(mu,2C_2-s_2)||_1
      <=16exp(2)*(s_3+s_2^2+A_2*(s_2+P)).

No mean bound mu<=M or small-marginal condition is required. The actual
Bernoulli convolution factors and actual Poisson factors are proved to
have normone. Their finite products are contractions. Exact insertion
identities and absolute exponential tails then need only the local
increment cap ||p_i*Delta||<=2, rather than a bound involving their sum.
Every contraction premise of the generic algebra lemma is discharged
for the actual probability factors; the target conversion is not an
input. All actual signed singleton masses and infinite tails remain
controlled by the ordinary l1 norm.

The universal inequality is instantiated on actual original-run
Bochner marginals and centered pair coefficients, with the actual count
mean and exact variance-minus-mean parameter. The full diagonal term
and all covariance signs are retained. It holds for every deterministic
dyadic subset, with no mean-cap argument and no asymptotic premise.

The homogeneous specialization is proved too. For every integern>=2,
0<=p<=1 and arbitrary realbeta,c2, the actual finite binomial pair
reference satisfies

    ||reference-Q(np,2c2-np^2)||_1
      <=4|beta-c2|+16exp(2)*
          (np^3+(np^2)^2+|c2|*(np^2+p)).

No upper bound onnp is assumed. A selected single pair in the full
finite heterogeneous theorem gives the exact covariance-reference
bound; the beta replacement has its proved cost4|beta-c2|. The source
natural subtractionn-2, omitted-product cardinality and all finite
products/sums are checked.

P1-MATH-0084 records the earlier removal of the logarithm and small-p
restriction. New P1-MATH-0086 records the independent removal of the
bounded-mean premise and the universal constant. This changes no
asymptotic exponent. Main15.1 remains in progress for the arithmetic
pair-activity rate A_2=O(N^(-2/3+epsilon)); companionT17.4 remains in
progress for C_2=O(a_N). Neither bound is assumed or counted proved.
Coverage77/167 (main28/73, companion49/94), confirmed findings86.
No external mathematical input, BCN premise, Paper C port, dependency
download, manuscript-byte change or Palomar registration is added.

Lean v4.36.0-rc2 full build passed (10655 jobs); actual axiom audit passed for all 6254 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 3971 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records remain intact. Ubuntu available space: 15.77 GiB. The universal constant16exp(2) is proved for the actual finite heterogeneous Poisson–Charlier conversion, with no bounded-mean argument and every true Bernoulli marginal in[0,1]. Every contraction premise is discharged for actual probability factors. Actual original-run means, signed covariances and exact second cumulants are retained. The homogeneous binomial pair conversion has the same universal constant with no bound onnp. Arithmetic pair-activity and covariance scales remain open; main15.1 and companionT17.4 are in progress and add no proved coverage. Coverage77/167 (main28/73, companion49/94); confirmed findings86. No new external input, BCN premise, Paper C port, dependency download, manuscript-byte change or Palomar registration.

Universal-constant proof checkpoint: [88ba9a757f9264e6ea74ebc07b94c1616e327ccb](https://github.com/Vulkin-prog/paper-p1-lean/commit/88ba9a757f9264e6ea74ebc07b94c1616e327ccb).


## A first coarse arithmetic conversion under explicit BCN

The literal actual absolute pair mass A2 now has an unconditional finite
host reduction. The exact factor2 from unordered pairs to ordered tuples
is proved. Zero full pair loss forces zero covariance, including every
actual affine compatibility case. An injective tuple-to-host map gives

    2*A2(full)<=#full_loss_hosts*M+actual_host_independent_mass

wheneverM bounds actual joint masses of distinct pairs. The independent
term retains the actual heterogeneous products p_x*p_y. Every smaller
deterministic ground set has no greater absolute pair mass.

Under precisely the same explicit field-polynomial BCN argument already
used for main13.5,13.6,13.8, the checked actual host count N^(1+epsilon)
and actual pair cap N^(-3/2+epsilon) imply, uniformly before every
critical length and every deterministic dyadic subsetG,

    A2(G)<=N^(-1/2+epsilon),
    ||B2(G)-Q(actual_mean,actual_second_cumulant)||_1<=N^(-3/2+epsilon).

These are coarse rates. They do not supply the stronger manuscript
A2=O(N^(-2/3+epsilon)) or the optimal conversion exponent5/3, and they
do not compare the original count law with the retained reference.

The exact second factorial cumulant, including its negative diagonal
term, satisfies |alpha(G)|<=2*A2(G)+sum p_x^2. Its actual diagonal is
bounded byK^2/N using the proved critical marginal cap. The same BCN
argument therefore gives |alpha(G)|<=N^(-1/2+epsilon), and hence a
uniform eventually-small statement with the threshold beforeL andG.
No cumulant or activity bound is supplied as a premise of these rates.

Independently of BCN, the actual full count mean satisfies eventually

    (2^C)^(-1)/2<=mu<=2*2^C.

The lower bound uses the actual regular population, whose size is at
leastN/2, and its actual nominal marginal; the upper bound uses the
proved actual marginal cap. Under BCN this gives |alpha|<=mu/2 and
alpha<mu uniformly in the critical band. Nonnegativity ofalpha is NOT
proved here, so the remaining Hermite admissibility condition remains
open, as do the original and explicit-parameter approximation rates.

Main15.1 and19.1 remain in progress. Neither this weaker conversion nor
a partial parameter gap adds proved numbered coverage. Coverage77/167
(main28/73, companion49/94), confirmed findings86 unchanged. The only
unformalized input is the existing ordinary BCN argument, explicitly
passed at every dependent theorem. The finite host identities and the
mean bounds are unconditional. No new external estimate, PaperC port,
dependency download, manuscript-byte change or Palomar registration.

Lean v4.36.0-rc2 full build passed (10671 jobs); actual axiom audit passed for all 6305 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 4022 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records remain intact. Ubuntu available space: 15.73 GiB. The exact finite2A2 host reduction and unconditional actual two-sided mean bounds are proved. Under the same explicit unformalized BCN argument, actual pair activity and actual second cumulants are at mostN^(-1/2+epsilon), actual conversion is at mostN^(-3/2+epsilon), and the upper parameter gap |alpha|<=mu/2 holds uniformly. No target activity, covariance or cumulant rate is assumed. Positivity ofalpha and the sharper source rates remain open; main15.1 and19.1 are in progress. Coverage77/167 (main28/73, companion49/94); confirmed findings86. No new external input, PaperC port, dependency download, manuscript-byte change or Palomar registration.


## Retaining the strict nonaligned rank gap

The literal original nonaligned family now has a finite positive host
bound. Every nonzero covariance is represented by an ordered increasing
nonaligned full-loss host. A joint cap M gives

    A_nonaligned <= #hosts * M + independent_host_mass.

The representation includes locally irregular sites, zero marginals and
affine incompatibility. It does not assume pairwise independence or a
positive covariance sign. Zero-loss pairs are removed only after their
actual centered coefficient has been proved zero.

With exactly the existing explicit BCN premise
PlaneCurvePointCount.UniformBound c kappa, c>0, put
s=(2/3) log 2. The already checked nonaligned joint cap N^(-2+s+delta)
and unconditional host count N^(1+delta) give

    A_nonaligned <= N^(-1+s+epsilon).

Independently, the complete aligned family satisfies the unconditional
bound A_aligned <= N^(-2/3+epsilon). Its cutoff can be chosen internally
as H=8(L+1), so this statement has no free private-prime cutoff.

The exact aligned/nonaligned partition therefore gives, under the same
explicit BCN premise and uniformly over every deterministic subset G
of the original dyadic block,

    A_2(G) <= N^(-1+s+epsilon),
    |alpha(G)| <= N^(-1+s+epsilon),
    ||B_2(G)-Q(actual mean, actual alpha)||_1 <= N^(-2+s+epsilon).

The exact single-site square diagonal is retained in alpha. Since
1/3 <= s < 1/2, these improve the previous coarse -1/2 activity/cumulant
and -3/2 conversion exponents by the strict gap 1/2-s. The first two
exponents are approximately -0.5379, and the conversion exponent is
approximately -1.5379. This is the analytic conversion of the finite
second-order reference, not an error bound for the complete count law.

All parameters c, kappa, C and epsilon are fixed before the common
threshold; lengths and deterministic subsets vary afterwards. BCN is an
ordinary theorem argument, not a new kernel axiom or an internally proved
external result. No stronger unformalized input is introduced.

These are intermediate rates, weaker than the source's sharp -2/3 pair
rate and -5/3 conversion rate. They do not establish the weighted dense
nonaligned estimate or finish main 3.3, 3.4, 15.1 or T7.1. All four
remain in progress; T1.8 stays not started. Coverage stays 77/167
(main 28/73, companion 49/94), and confirmed improvements stay 94.
No original manuscript edit, dependency download or Palomar registration
is introduced.

Verified under Lean v4.36.0-rc2: full lake build (11031 jobs), source and ledger checks, actual axiom audit of 7025 declarations (only propext, Classical.choice and Quot.sound), and 4742 direct ledger/evidence declaration checks; Ubuntu root free space 15.03 GiB. Original manuscript bytes and all 167 statement hashes preserved.
